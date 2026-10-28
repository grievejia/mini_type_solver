//! Check recorded `<:` rules before choosing values for variables.
//!
//! For `L <: ?X` and `?X <: U`, the check `L <: U` belongs to `?X <: U`.
//! Keep two records separate. One says which check requires another. The other
//! says which checks must repeat when a variable gets another recorded rule.
//! Every change to recorded rules can be undone after a failed choice.

mod compare;
mod cycles;
mod scopes;
mod solution;
#[cfg(test)]
mod tests;
mod witness;
pub use solution::Witness;

use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::mem;
use std::vec::IntoIter;

use crate::solver::input::Input;

use super::super::ClassRelation;
use super::Component;
use super::graph::{ChoiceCopy, FactorNode, Graph, SArm, SValue};
use super::identities::{
    Identities, PathStep, ROOT_SCOPE, RequirementId, TypePath, VarId, source_value,
};
use compare::constructor_children;
use cycles::cycles_pass;
use scopes::{Context, Conversion, ScopeState, ScopeUndo};
use witness::eliminate;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Comparison<T = SValue> {
    lower: T,
    upper: T,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum EdgeKind {
    Ordinary,
    Constructor,
    Superclass,
}

#[derive(Debug)]
struct Child {
    comparison: Comparison,
    kind: EdgeKind,
    path: TypePath,
}

#[derive(Debug, Clone)]
struct Goal {
    comparison: Comparison,
    context: Context,
    rule: Rule,
    children: BTreeSet<(EdgeKind, usize)>,
}

/// The selected rule is retained for checks after variables have values.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Rule {
    Pending,
    Written,
    Equation {
        variable: VarId,
    },
    Expansion,
    Exact,
    Stronger,
    Constructor,
    LowerGeneric {
        arguments: Vec<SValue>,
    },
    UpperGeneric {
        arguments: Vec<SValue>,
    },
    Transfer,
    Conversion(Conversion),
    Instance {
        copy: ChoiceCopy,
        requirement: RequirementId,
    },
}

#[derive(Debug, Default)]
struct Bounds {
    lower: BTreeSet<SValue>,
    upper: BTreeSet<usize>,
    readers: BTreeSet<usize>,
}

#[derive(Debug)]
enum Undo {
    Goal((Comparison, Option<Context>)),
    Variable(VarId),
    Edge(usize, EdgeKind, usize),
    Lower(VarId, SValue),
    Upper(VarId, usize),
    Reader(VarId, usize),
    Rule(usize, Rule),
    Scope(ScopeUndo),
}

#[derive(Debug)]
pub struct State {
    bounds: BTreeMap<VarId, Bounds>,
    goals: Vec<Goal>,
    goal_ids: BTreeMap<(Comparison, Option<Context>), usize>,
    scopes: ScopeState,
    pending: VecDeque<usize>,
    queued: BTreeSet<usize>,
    undo: Vec<Undo>,
}

#[derive(Debug)]
struct Checkpoint {
    changes: usize,
    pending: VecDeque<usize>,
    queued: BTreeSet<usize>,
}

#[derive(Debug)]
struct ChoiceFrame {
    parent: usize,
    checkpoint: Checkpoint,
    remaining: IntoIter<Alternative>,
}

impl State {
    fn new(variables: impl Iterator<Item = VarId>) -> Self {
        Self {
            bounds: variables.map(|id| (id, Bounds::default())).collect(),
            goals: Vec::new(),
            goal_ids: BTreeMap::new(),
            scopes: ScopeState::default(),
            pending: VecDeque::new(),
            queued: BTreeSet::new(),
            undo: Vec::new(),
        }
    }

    fn variable(&mut self, variable: VarId) {
        if let Entry::Vacant(entry) = self.bounds.entry(variable) {
            entry.insert(Bounds::default());
            self.undo.push(Undo::Variable(variable));
        }
    }

    fn enqueue(&mut self, id: usize) {
        if self.queued.insert(id) {
            self.pending.push_back(id);
        }
    }

    fn rule(&mut self, id: usize, rule: Rule) {
        if self.goals[id].rule != rule {
            let old = mem::replace(&mut self.goals[id].rule, rule);
            self.undo.push(Undo::Rule(id, old));
        }
    }

    fn goal(&mut self, comparison: Comparison, context: Context) -> usize {
        // Pure constructor and variable comparisons can share their continuation.
        // A generic use also keeps its source and position. Sharing its type must
        // not share selections between two independent requirements.
        let identity = (comparison.lower.contains_generic() || comparison.upper.contains_generic())
            .then(|| context.clone());
        let key = (comparison.clone(), identity);
        if let Some(id) = self.goal_ids.get(&key) {
            return *id;
        }
        // An existing comparison already registered every variable it reads.
        // Rollback removes a new comparison before its new variables.
        let mut pending = vec![&comparison.lower, &comparison.upper];
        while let Some(value) = pending.pop() {
            for factor in value.arms().iter().flat_map(SArm::factors) {
                match factor.node() {
                    FactorNode::Ref(variable) => {
                        self.variable(*variable);
                    }
                    node => pending.extend(node.children()),
                }
            }
        }
        let id = self.goals.len();
        self.goal_ids.insert(key.clone(), id);
        self.undo.push(Undo::Goal(key));
        self.goals.push(Goal {
            comparison,
            context,
            rule: Rule::Pending,
            children: BTreeSet::new(),
        });
        self.enqueue(id);
        id
    }

    fn child(&mut self, parent: usize, comparison: Comparison, kind: EdgeKind) {
        let context = self.goals[parent].context.clone();
        self.child_in(parent, comparison, kind, context);
    }

    fn child_in(
        &mut self,
        parent: usize,
        comparison: Comparison,
        kind: EdgeKind,
        context: Context,
    ) -> usize {
        let id = self.goal(comparison, context);
        if self.goals[parent].children.insert((kind, id)) {
            self.undo.push(Undo::Edge(parent, kind, id));
        }
        // Find a failed check before trying choices for unrelated expressions.
        // Otherwise that failure can repeat successful choices for every other
        // expression.
        if self.queued.contains(&id) {
            self.pending.retain(|queued| *queued != id);
            self.pending.push_front(id);
        }
        id
    }

    fn lower(&mut self, variable: VarId, value: &SValue) {
        let bounds = self.bounds.entry(variable).or_default();
        if !bounds.lower.insert(value.clone()) {
            return;
        }
        self.undo.push(Undo::Lower(variable, value.clone()));
        let upper: Vec<_> = bounds.upper.iter().copied().collect();
        let readers: Vec<_> = bounds.readers.iter().copied().collect();
        for parent in upper.into_iter().rev() {
            self.child(
                parent,
                Comparison {
                    lower: value.clone(),
                    upper: self.goals[parent].comparison.upper.clone(),
                },
                EdgeKind::Ordinary,
            );
        }
        for reader in readers {
            self.enqueue(reader);
        }
    }

    fn upper(&mut self, variable: VarId, parent: usize) {
        let bounds = self.bounds.entry(variable).or_default();
        if !bounds.upper.insert(parent) {
            return;
        }
        self.undo.push(Undo::Upper(variable, parent));
        let lower: Vec<_> = bounds.lower.iter().cloned().collect();
        for lower in lower.into_iter().rev() {
            self.child(
                parent,
                Comparison {
                    lower,
                    upper: self.goals[parent].comparison.upper.clone(),
                },
                EdgeKind::Ordinary,
            );
        }
    }

    fn reader(&mut self, variable: VarId, goal: usize) {
        if self
            .bounds
            .entry(variable)
            .or_default()
            .readers
            .insert(goal)
        {
            self.undo.push(Undo::Reader(variable, goal));
        }
    }

    fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            changes: self.undo.len(),
            pending: self.pending.clone(),
            queued: self.queued.clone(),
        }
    }

    fn restore(&mut self, checkpoint: &Checkpoint) {
        for change in self.undo.drain(checkpoint.changes..).rev() {
            match change {
                Undo::Variable(variable) => {
                    self.bounds.remove(&variable);
                }
                Undo::Goal(comparison) => {
                    self.goal_ids.remove(&comparison);
                    self.goals.pop();
                }
                Undo::Edge(parent, kind, child) => {
                    self.goals[parent].children.remove(&(kind, child));
                }
                Undo::Lower(variable, value) => {
                    self.bounds
                        .entry(variable)
                        .or_default()
                        .lower
                        .remove(&value);
                }
                Undo::Upper(variable, goal) => {
                    self.bounds.entry(variable).or_default().upper.remove(&goal);
                }
                Undo::Rule(id, rule) => {
                    self.goals[id].rule = rule;
                }
                Undo::Scope(change) => self.scopes.restore(change),
                Undo::Reader(variable, goal) => {
                    self.bounds
                        .entry(variable)
                        .or_default()
                        .readers
                        .remove(&goal);
                }
            }
        }
        self.pending.clone_from(&checkpoint.pending);
        self.queued.clone_from(&checkpoint.queued);
    }
}

fn bare_variable(value: &SValue) -> Option<VarId> {
    let factor = value.single_factor()?;
    match factor.node() {
        FactorNode::Ref(id) => Some(*id),
        _ => None,
    }
}

/// A loop requires the same variable twice on one path.
/// Two `&` parts can reach the same variable through independent paths.
fn expand_arm(
    graph: &Graph,
    arm: &SArm,
    bounds: &BTreeMap<VarId, Bounds>,
) -> (BTreeSet<SArm>, BTreeSet<VarId>) {
    let factors = arm
        .factors()
        .iter()
        .cloned()
        .map(|factor| (factor, BTreeSet::new()))
        .collect::<Vec<_>>();
    let mut pending = vec![factors];
    let mut expanded = BTreeSet::new();
    let mut readers = BTreeSet::new();
    while let Some(mut factors) = pending.pop() {
        let Some((index, variable)) =
            factors
                .iter()
                .enumerate()
                .find_map(|(index, (factor, _))| match factor.node() {
                    FactorNode::Ref(variable) => Some((index, *variable)),
                    _ => None,
                })
        else {
            if let Some(arm) = graph.arm(factors.into_iter().map(|(factor, _)| factor).collect()) {
                expanded.insert(arm);
            }
            continue;
        };
        let (_, mut path) = factors.remove(index);
        readers.insert(variable);
        if !path.insert(variable) {
            continue;
        }
        for lower in &bounds[&variable].lower {
            for arm in lower.arms() {
                let mut next = factors.clone();
                next.extend(
                    arm.factors()
                        .iter()
                        .cloned()
                        .map(|factor| (factor, path.clone())),
                );
                pending.push(next);
            }
        }
    }
    (expanded, readers)
}

#[derive(Debug)]
enum Step {
    Done,
    Reject,
    Choose(Vec<Alternative>),
}

#[derive(Debug)]
enum Alternative {
    Comparison(Comparison, PathStep),
    Conversion {
        variable: VarId,
        conversion: Conversion,
    },
}

/// Graph factors are sorted. Compare complete factors without reading variable
/// values. Every left-side union part needs a matching right-side part.
fn holds_by_written_form(lower: &SValue, upper: &SValue) -> bool {
    lower == upper
        || lower.arms().iter().all(|lower_arm| {
            upper.arms().iter().any(|upper_arm| {
                upper_arm
                    .factors()
                    .iter()
                    .all(|factor| lower_arm.factors().binary_search(factor).is_ok())
            })
        })
}

fn propagate(
    graph: &Graph,
    id: usize,
    state: &mut State,
    identities: &mut Identities,
    relation: &ClassRelation<'_>,
) -> Step {
    let Comparison { lower, upper } = state.goals[id].comparison.clone();
    if matches!(
        state.goals[id].rule,
        Rule::Conversion(_) | Rule::LowerGeneric { .. } | Rule::UpperGeneric { .. }
    ) {
        return Step::Done;
    }
    if holds_by_written_form(&lower, &upper) {
        state.rule(id, Rule::Written);
        return Step::Done;
    }
    if let Some(variable) = bare_variable(&upper) {
        return scopes::store(graph, id, variable, &lower, state, identities, relation);
    }
    if let Some(variable) = bare_variable(&lower) {
        state.rule(id, Rule::Expansion);
        state.upper(variable, id);
        return Step::Done;
    }
    if upper == graph.object() {
        state.rule(id, Rule::Written);
        return Step::Done;
    }
    let lower_arm = match lower.arms() {
        [arm] => arm,
        arms => {
            state.rule(id, Rule::Exact);
            for (index, arm) in arms.iter().enumerate().rev() {
                let context = state.goals[id].context.child(PathStep::LowerArm(index));
                state.child_in(
                    id,
                    Comparison {
                        lower: graph.arm_value(arm.clone()),
                        upper: upper.clone(),
                    },
                    EdgeKind::Ordinary,
                    context,
                );
            }
            return Step::Done;
        }
    };
    if lower_arm
        .factors()
        .iter()
        .any(|factor| matches!(factor.node(), FactorNode::Ref(_)))
    {
        state.rule(id, Rule::Expansion);
        let (expanded, readers) = expand_arm(graph, lower_arm, &state.bounds);
        for variable in readers {
            state.reader(variable, id);
        }
        for arm in expanded.into_iter().rev() {
            state.child(
                id,
                Comparison {
                    lower: graph.arm_value(arm),
                    upper: upper.clone(),
                },
                EdgeKind::Ordinary,
            );
        }
        return Step::Done;
    }
    propagate_arm(graph, id, lower_arm, &upper, state, identities, relation)
}

fn propagate_arm(
    graph: &Graph,
    id: usize,
    lower_arm: &SArm,
    upper: &SValue,
    state: &mut State,
    identities: &mut Identities,
    relation: &ClassRelation<'_>,
) -> Step {
    let lower = graph.arm_value(lower_arm.clone());
    let upper_arm = match upper.arms() {
        [] => return Step::Reject,
        [arm] => arm,
        arms => {
            state.rule(
                id,
                if has_choice(&lower) {
                    Rule::Stronger
                } else {
                    Rule::Exact
                },
            );
            return Step::Choose(
                arms.iter()
                    .enumerate()
                    .map(|(index, arm)| {
                        Alternative::Comparison(
                            Comparison {
                                lower: lower.clone(),
                                upper: graph.arm_value(arm.clone()),
                            },
                            PathStep::UpperArm(index),
                        )
                    })
                    .collect(),
            );
        }
    };
    let upper_factor = match upper_arm.factors() {
        [factor] => factor,
        factors => {
            state.rule(id, Rule::Exact);
            for (index, factor) in factors.iter().enumerate().rev() {
                let context = state.goals[id].context.child(PathStep::UpperFactor(index));
                state.child_in(
                    id,
                    Comparison {
                        lower: lower.clone(),
                        upper: graph.value(factor.clone()),
                    },
                    EdgeKind::Ordinary,
                    context,
                );
            }
            return Step::Done;
        }
    };
    let [lower_factor] = lower_arm.factors() else {
        state.rule(
            id,
            if has_choice(&lower) {
                Rule::Stronger
            } else {
                Rule::Exact
            },
        );
        return Step::Choose(
            lower_arm
                .factors()
                .iter()
                .enumerate()
                .map(|(index, factor)| {
                    Alternative::Comparison(
                        Comparison {
                            lower: graph.value(factor.clone()),
                            upper: upper.clone(),
                        },
                        PathStep::LowerFactor(index),
                    )
                })
                .collect(),
        );
    };
    if let Some(step) =
        scopes::generic_comparison(graph, id, lower_factor, upper_factor, state, identities)
    {
        return step;
    }
    state.rule(id, Rule::Constructor);
    let Some(children) = constructor_children(graph, lower_factor, upper_factor, relation) else {
        return Step::Reject;
    };
    for child in children.into_iter().rev() {
        let mut context = state.goals[id].context.clone();
        context.path.extend(child.path);
        state.child_in(id, child.comparison, child.kind, context);
    }
    Step::Done
}

/// Try choices with one current set of rules.
/// Each choice keeps pending checks and a position in the change log. These
/// records permit complete restoration after a failed choice.
fn run_search(
    graph: &Graph,
    state: &mut State,
    identities: &mut Identities,
    relation: &ClassRelation<'_>,
) -> bool {
    let mut frames: Vec<ChoiceFrame> = Vec::new();
    loop {
        if let Some(id) = state.pending.pop_front() {
            state.queued.remove(&id);
            match propagate(graph, id, state, identities, relation) {
                Step::Done => continue,
                Step::Choose(alternatives) => {
                    let mut remaining = alternatives.into_iter();
                    if let Some(first) = remaining.next() {
                        let checkpoint = state.checkpoint();
                        apply_alternative(graph, id, first, state, identities);
                        frames.push(ChoiceFrame {
                            parent: id,
                            checkpoint,
                            remaining,
                        });
                        continue;
                    }
                }
                Step::Reject => {}
            }
        } else if cycles_pass(state) {
            return true;
        }
        loop {
            let Some(frame) = frames.last_mut() else {
                return false;
            };
            state.restore(&frame.checkpoint);
            if let Some(next) = frame.remaining.next() {
                apply_alternative(graph, frame.parent, next, state, identities);
                break;
            }
            frames.pop();
        }
    }
}

/// Comparisons in this group share no variables with other groups.
/// Keep original and added comparisons for checking the chosen values.
pub fn solve_component(
    graph: &Graph,
    component: &Component,
    input: &Input<'_>,
    identities: &mut Identities,
    relation: &ClassRelation<'_>,
) -> Option<Witness> {
    let variables = component
        .metavars
        .iter()
        .map(|metavar| (*metavar, identities.declared(*metavar)))
        .collect::<BTreeMap<_, _>>();
    let mut state = State::new(variables.values().copied());
    for id in &component.atoms {
        let atom = input.atoms().atom(*id);
        state.goal(
            Comparison {
                lower: source_value(graph, atom.lower, input.types(), identities),
                upper: source_value(graph, atom.upper, input.types(), identities),
            },
            Context {
                check: *id,
                path: Vec::new(),
                scope: ROOT_SCOPE,
            },
        );
    }
    if !run_search(graph, &mut state, identities, relation) {
        // Keeping rules and their permitted choices makes this failure valid
        // after adding comparisons. See "Why adding comparisons preserves a
        // failure" in the design reference.
        return None;
    }
    let equations = equations(graph, &state);
    Some(Witness::from_state(equations, variables, state))
}

fn equations(graph: &Graph, state: &State) -> BTreeMap<VarId, SValue> {
    let mut equations = state
        .bounds
        .iter()
        .map(|(variable, bounds)| {
            (
                *variable,
                graph.union(
                    bounds
                        .lower
                        .iter()
                        .map(|value| solution::materialize(graph, value, &state.scopes)),
                ),
            )
        })
        .collect();
    eliminate(graph, &mut equations);
    equations
}

fn has_choice(value: &SValue) -> bool {
    value
        .arms()
        .iter()
        .flat_map(SArm::factors)
        .any(|factor| matches!(factor.node(), FactorNode::Choice(_)))
}

fn apply_alternative(
    graph: &Graph,
    parent: usize,
    alternative: Alternative,
    state: &mut State,
    identities: &mut Identities,
) {
    match alternative {
        Alternative::Comparison(comparison, path) => {
            let context = state.goals[parent].context.child(path);
            state.child_in(parent, comparison, EdgeKind::Ordinary, context);
        }
        Alternative::Conversion {
            variable,
            conversion,
        } => {
            scopes::apply(graph, parent, variable, conversion, state, identities);
        }
    }
}
