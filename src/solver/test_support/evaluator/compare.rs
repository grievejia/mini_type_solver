//! Graph comparison with independent Boolean and constructor rules.

mod equality;

use std::collections::{BTreeMap, BTreeSet};
use std::vec::IntoIter;

use crate::frontend::problem::ClassVariance;

use super::import::instantiate_arguments;
use super::{Graph, OBJECT_INDEX, Selections, Type, arms};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Check {
    Values(bool, usize, usize),
    ArmToValue(bool, Vec<usize>, usize),
    Arms(bool, Vec<usize>, Vec<usize>),
    ArmToFactor(bool, Vec<usize>, usize),
    Factors(bool, usize, usize),
    GenericBodies(usize, usize),
    SelectedBody {
        owner: usize,
        other: usize,
        upper: bool,
    },
}

type Bindings = Vec<(usize, usize)>;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Goal {
    check: Check,
    bindings: Bindings,
    selections: Selections,
    // These upper generic functions introduce arbitrary parameters. Lower
    // selections can use their parameters while checking their bodies.
    arbitrary: BTreeSet<usize>,
}

#[derive(Debug, Clone, Copy)]
enum Edge {
    Ordinary,
    Constructor,
    Superclass,
}

struct Child {
    goal: Goal,
    edge: Edge,
}
enum Rule {
    Done(bool),
    All(Vec<Child>),
    Any(Vec<Child>),
}
struct Frame {
    goal: Goal,
    edge: Edge,
    all: bool,
    children: IntoIter<Child>,
}

struct Comparer<'a> {
    graph: &'a mut Graph,
    // A substitution can change both factors and the number of Boolean arms.
    forms: BTreeMap<(usize, Selections), Option<Vec<Vec<usize>>>>,
    instances: BTreeMap<(usize, usize), usize>,
    select_parameters: bool,
    free: Vec<BTreeSet<usize>>,
    equal: BTreeMap<Goal, bool>,
}

fn child(goal: &Goal, check: Check, edge: Edge) -> Child {
    Child {
        goal: Goal {
            check,
            bindings: goal.bindings.clone(),
            selections: goal.selections.clone(),
            arbitrary: goal.arbitrary.clone(),
        },
        edge,
    }
}

impl Comparer<'_> {
    // A recursive reference returns to its saved parameter owners. Previous
    // introductions that the compared expressions do not use have no effect
    // on this check. Keeping them would hide a repeated comparison.
    fn saved_bindings(&mut self, goal: &mut Goal) {
        if self.free.len() != self.graph.nodes.len() {
            self.free = self.graph.free_parameters();
        }
        let ids = match &goal.check {
            Check::Values(_, lower, upper) | Check::Factors(_, lower, upper) => {
                vec![*lower, *upper]
            }
            Check::ArmToValue(_, lower, upper) | Check::ArmToFactor(_, lower, upper) => {
                lower.iter().copied().chain([*upper]).collect()
            }
            Check::Arms(_, lower, upper) => lower.iter().chain(upper).copied().collect(),
            Check::GenericBodies(lower, upper) => self.graph.nodes[*lower]
                .kind
                .children()
                .into_iter()
                .chain(self.graph.nodes[*upper].kind.children())
                .collect(),
            Check::SelectedBody { owner, other, .. } => self.graph.nodes[*owner]
                .kind
                .children()
                .into_iter()
                .chain(self.graph.nodes[*other].kind.children())
                .collect(),
        };
        let mut used = ids
            .iter()
            .flat_map(|id| self.free[*id].iter().copied())
            .collect::<BTreeSet<_>>();
        loop {
            let old = used.len();
            for (owner, values) in &goal.selections {
                if used.contains(owner) {
                    used.extend(values.iter().flat_map(|id| self.free[*id].iter().copied()));
                }
            }
            if used.len() == old {
                break;
            }
        }
        goal.bindings
            .retain(|(lower, upper)| used.contains(lower) || used.contains(upper));
        goal.bindings.sort_unstable();
        goal.bindings.dedup();
        goal.selections.retain(|owner, _| used.contains(owner));
        goal.arbitrary.retain(|owner| used.contains(owner));
    }

    fn form(&mut self, id: usize, selections: &Selections) -> Option<Vec<Vec<usize>>> {
        self.forms
            .entry((id, selections.clone()))
            .or_insert_with(|| arms(self.graph, id, selections))
            .clone()
    }

    fn rule(&mut self, goal: &Goal) -> Rule {
        match &goal.check {
            Check::Values(equal, lower, upper) => {
                let Some(lower_arms) = self.form(*lower, &goal.selections) else {
                    return Rule::Done(false);
                };
                let mut children = lower_arms
                    .into_iter()
                    .map(|arm| child(goal, Check::ArmToValue(*equal, arm, *upper), Edge::Ordinary))
                    .collect::<Vec<_>>();
                if *equal {
                    let Some(upper_arms) = self.form(*upper, &goal.selections) else {
                        return Rule::Done(false);
                    };
                    children.extend(upper_arms.into_iter().map(|arm| {
                        child(goal, Check::ArmToValue(true, arm, *lower), Edge::Ordinary)
                    }));
                }
                Rule::All(children)
            }
            Check::ArmToValue(equal, lower, upper) => {
                let Some(upper_arms) = self.form(*upper, &goal.selections) else {
                    return Rule::Done(false);
                };
                Rule::Any(
                    upper_arms
                        .into_iter()
                        .map(|upper| {
                            child(
                                goal,
                                Check::Arms(*equal, lower.clone(), upper),
                                Edge::Ordinary,
                            )
                        })
                        .collect(),
                )
            }
            Check::Arms(equal, lower, upper) => {
                let mut children = upper
                    .iter()
                    .map(|upper| {
                        child(
                            goal,
                            Check::ArmToFactor(*equal, lower.clone(), *upper),
                            Edge::Ordinary,
                        )
                    })
                    .collect::<Vec<_>>();
                if *equal {
                    children.extend(lower.iter().map(|lower| {
                        child(
                            goal,
                            Check::ArmToFactor(true, upper.clone(), *lower),
                            Edge::Ordinary,
                        )
                    }));
                }
                Rule::All(children)
            }
            Check::ArmToFactor(equal, lower, upper) => Rule::Any(
                lower
                    .iter()
                    .map(|lower| {
                        child(goal, Check::Factors(*equal, *lower, *upper), Edge::Ordinary)
                    })
                    .collect(),
            ),
            Check::Factors(equal, lower, upper) => self.factors(goal, *equal, *lower, *upper),
            Check::SelectedBody {
                owner,
                other,
                upper,
            } => self.selected_body(goal, *owner, *other, *upper),
            Check::GenericBodies(lower, upper) => {
                let (Type::Generic { body: lower, .. }, Type::Generic { body: upper, .. }) = (
                    &self.graph.nodes[*lower].kind,
                    &self.graph.nodes[*upper].kind,
                ) else {
                    return Rule::Done(false);
                };
                if lower.params.len() != upper.params.len() {
                    return Rule::Done(false);
                }
                Rule::All(
                    lower
                        .children()
                        .zip(upper.children())
                        .map(|(lower, upper)| {
                            child(goal, Check::Values(true, *lower, *upper), Edge::Constructor)
                        })
                        .collect(),
                )
            }
        }
    }

    fn generics(goal: &Goal, lower: usize, upper: usize) -> Rule {
        let mut next = child(goal, Check::GenericBodies(lower, upper), Edge::Constructor);
        if !next.goal.bindings.contains(&(lower, upper)) {
            next.goal.bindings.push((lower, upper));
        }
        Rule::All(vec![next])
    }

    // Candidates come from the evaluator's graph. They contain no generic
    // function and use only arbitrary parameters visible in this comparison.
    // Revisiting a selection keeps its chosen values. This finite pool can
    // miss a valid witness.
    fn lower_generic(&mut self, goal: &Goal, owner: usize, other: usize, count: usize) -> Rule {
        if goal.selections.contains_key(&owner) {
            return Rule::All(vec![child(
                goal,
                Check::SelectedBody {
                    owner,
                    other,
                    upper: false,
                },
                Edge::Ordinary,
            )]);
        }
        let candidates = generic_free_candidates(self.graph, &goal.arbitrary);
        let mut tuples = vec![Vec::new()];
        for _ in 0..count {
            tuples = tuples
                .into_iter()
                .flat_map(|prefix| {
                    candidates.iter().map(move |candidate| {
                        let mut tuple = prefix.clone();
                        tuple.push(*candidate);
                        tuple
                    })
                })
                .collect();
        }
        // Object contains every value. Try it before checking the other
        // value tuples. The complete comparison must still pass.
        if let Some(object) = self.graph.nodes.iter().position(|node| match &node.kind {
            Type::Class { class, arguments } => *class == OBJECT_INDEX && arguments.is_empty(),
            _ => false,
        }) && let Some(index) = tuples
            .iter()
            .position(|tuple| tuple.iter().all(|id| *id == object))
        {
            tuples.swap(0, index);
        }
        // First try the upper parameters in declaration order. Equal types
        // with different parameter names then need no other selection.
        if let Type::Generic { parameters, .. } = self.graph.nodes[other].kind
            && parameters == count
            && let Some(preferred) = (0..count)
                .map(|position| {
                    self.graph.nodes.iter().position(|node| match node.kind {
                        Type::Bound {
                            owner,
                            position: at,
                        } => owner == other && at == position,
                        _ => false,
                    })
                })
                .collect::<Option<Vec<_>>>()
        {
            tuples.retain(|tuple| *tuple != preferred);
            tuples.insert(0, preferred);
        }
        Rule::Any(
            tuples
                .into_iter()
                .map(|arguments| {
                    let mut next = child(
                        goal,
                        Check::SelectedBody {
                            owner,
                            other,
                            upper: false,
                        },
                        Edge::Ordinary,
                    );
                    next.goal.selections.insert(owner, arguments);
                    next
                })
                .collect(),
        )
    }

    fn selected_body(&self, goal: &Goal, owner: usize, other: usize, upper: bool) -> Rule {
        let Type::Generic { body, .. } = &self.graph.nodes[owner].kind else {
            return Rule::Done(false);
        };
        let (Type::Callable(target) | Type::Generic { body: target, .. }) =
            &self.graph.nodes[other].kind
        else {
            return Rule::Done(false);
        };
        if body.params.len() != target.params.len() {
            return Rule::Done(false);
        }
        let mut children = body
            .params
            .iter()
            .zip(&target.params)
            .map(|(body, target)| {
                let (lower, upper) = if upper {
                    (*body, *target)
                } else {
                    (*target, *body)
                };
                child(goal, Check::Values(false, lower, upper), Edge::Constructor)
            })
            .collect::<Vec<_>>();
        let (lower, upper) = if upper {
            (target.ret, body.ret)
        } else {
            (body.ret, target.ret)
        };
        children.push(child(
            goal,
            Check::Values(false, lower, upper),
            Edge::Constructor,
        ));
        Rule::All(children)
    }

    fn ancestors(
        &mut self,
        goal: &Goal,
        lower: usize,
        upper: usize,
        class: usize,
        arguments: &[usize],
    ) -> Rule {
        let mut alternatives = Vec::new();
        for index in 0..self.graph.classes[class].direct.len() {
            let key = (lower, index);
            let instance = if let Some(id) = self.instances.get(&key) {
                *id
            } else {
                let (parent, templates) = &self.graph.classes[class].direct[index];
                let parent = *parent;
                let templates = templates.clone();
                let scope = self.graph.nodes[lower].scope.clone();
                let arguments =
                    instantiate_arguments(self.graph, class, &templates, arguments, &scope);
                let id = self.graph.intern(
                    Type::Class {
                        class: parent,
                        arguments,
                    },
                    scope,
                );
                self.instances.insert(key, id);
                id
            };
            alternatives.push(child(
                goal,
                Check::Values(false, instance, upper),
                Edge::Superclass,
            ));
        }
        Rule::Any(alternatives)
    }

    fn generic_selection(
        &mut self,
        goal: &Goal,
        equal: bool,
        lower: usize,
        upper: usize,
    ) -> Option<Rule> {
        if !equal && self.select_parameters {
            match (&self.graph.nodes[lower].kind, &self.graph.nodes[upper].kind) {
                (Type::Generic { parameters, .. }, Type::Generic { .. }) => {
                    let mut goal = goal.clone();
                    goal.arbitrary.insert(upper);
                    return Some(self.lower_generic(&goal, lower, upper, *parameters));
                }
                (Type::Generic { parameters, .. }, Type::Callable(_)) => {
                    return Some(self.lower_generic(goal, lower, upper, *parameters));
                }
                (Type::Callable(_), Type::Generic { .. }) => {
                    let mut goal = goal.clone();
                    goal.arbitrary.insert(upper);
                    return Some(Rule::All(vec![child(
                        &goal,
                        Check::SelectedBody {
                            owner: upper,
                            other: lower,
                            upper: true,
                        },
                        Edge::Ordinary,
                    )]));
                }
                _ => {}
            }
        }
        None
    }

    fn factors(&mut self, goal: &Goal, equal: bool, lower: usize, upper: usize) -> Rule {
        if lower == upper {
            return Rule::Done(true);
        }
        if let Some(rule) = self.generic_selection(goal, equal, lower, upper) {
            return rule;
        }
        let mut required = Vec::new();
        let mut add = |lower, upper| {
            required.push(child(
                goal,
                Check::Values(equal, lower, upper),
                Edge::Constructor,
            ));
        };
        match (
            self.graph.nodes[lower].kind.clone(),
            self.graph.nodes[upper].kind.clone(),
        ) {
            (
                Type::Bound {
                    owner: l,
                    position: lp,
                },
                Type::Bound {
                    owner: u,
                    position: up,
                },
            ) => {
                return Rule::Done(
                    lp == up
                        && (l == u
                            || goal.bindings.contains(&(l, u))
                            || goal.bindings.contains(&(u, l))),
                );
            }
            (
                Type::Class {
                    class: l,
                    arguments: lower,
                },
                Type::Class {
                    class: u,
                    arguments: upper,
                },
            ) if l == u => {
                for ((lower, upper), variance) in lower
                    .into_iter()
                    .zip(upper)
                    .zip(&self.graph.classes[l].variances)
                {
                    if equal || *variance != ClassVariance::Contravariant {
                        add(lower, upper);
                    }
                    if !equal && *variance != ClassVariance::Covariant {
                        add(upper, lower);
                    }
                }
            }
            (Type::Class { class, arguments }, Type::Class { .. }) if !equal => {
                return self.ancestors(goal, lower, upper, class, &arguments);
            }
            (Type::Tuple(lower), Type::Tuple(upper)) if lower.len() == upper.len() => {
                for (lower, upper) in lower.into_iter().zip(upper) {
                    add(lower, upper);
                }
            }
            (Type::Callable(lower), Type::Callable(upper))
                if lower.params.len() == upper.params.len() =>
            {
                for (lower, upper) in lower.params.into_iter().zip(upper.params) {
                    if equal {
                        add(lower, upper);
                    } else {
                        add(upper, lower);
                    }
                }
                add(lower.ret, upper.ret);
            }
            (Type::Generic { parameters: l, .. }, Type::Generic { parameters: u, .. })
                if l == u =>
            {
                return Self::generics(goal, lower, upper);
            }
            _ => return Rule::Done(false),
        }
        Rule::All(required)
    }
}

fn repeated(frames: &[Frame], next: &Child) -> Option<bool> {
    let start = frames.iter().position(|frame| frame.goal == next.goal)?;
    let edges = frames[start + 1..]
        .iter()
        .map(|frame| frame.edge)
        .chain([next.edge])
        .collect::<Vec<_>>();
    Some(
        edges.iter().any(|edge| matches!(edge, Edge::Constructor))
            && !edges.iter().any(|edge| matches!(edge, Edge::Superclass)),
    )
}

pub fn is_subtype(graph: &mut Graph, lower: usize, upper: usize) -> bool {
    compare(graph, lower, upper, false)
}

pub fn model_is_subtype(graph: &mut Graph, lower: usize, upper: usize) -> bool {
    compare(graph, lower, upper, true)
}

fn compare(graph: &mut Graph, lower: usize, upper: usize, select_parameters: bool) -> bool {
    if select_parameters {
        graph.intern(Type::Never, Vec::new());
        graph.intern(
            Type::Class {
                class: OBJECT_INDEX,
                arguments: Vec::new(),
            },
            Vec::new(),
        );
    }
    let free = graph.free_parameters();
    let mut comparer = Comparer {
        free,
        graph,
        forms: BTreeMap::new(),
        instances: BTreeMap::new(),
        select_parameters,
        equal: BTreeMap::new(),
    };
    run(&mut comparer, lower, upper)
}

fn run(comparer: &mut Comparer<'_>, lower: usize, upper: usize) -> bool {
    let mut frames = Vec::new();
    let mut next = Some(Child {
        goal: Goal {
            check: Check::Values(false, lower, upper),
            bindings: Vec::new(),
            selections: BTreeMap::new(),
            arbitrary: BTreeSet::new(),
        },
        edge: Edge::Ordinary,
    });
    let mut result = None;
    loop {
        if let Some(mut child) = next.take() {
            comparer.saved_bindings(&mut child.goal);
            if equality::holds(comparer, &child.goal) {
                result = Some(true);
            } else if let Some(accepted) = repeated(&frames, &child) {
                result = Some(accepted);
            } else {
                let rule = comparer.rule(&child.goal);
                match rule {
                    Rule::Done(accepted) => result = Some(accepted),
                    Rule::All(children) => {
                        let mut children = children.into_iter();
                        next = children.next();
                        if next.is_none() {
                            result = Some(true);
                        } else {
                            frames.push(Frame {
                                goal: child.goal,
                                edge: child.edge,
                                all: true,
                                children,
                            });
                            continue;
                        }
                    }
                    Rule::Any(children) => {
                        let mut children = children.into_iter();
                        next = children.next();
                        if next.is_none() {
                            result = Some(false);
                        } else {
                            frames.push(Frame {
                                goal: child.goal,
                                edge: child.edge,
                                all: false,
                                children,
                            });
                            continue;
                        }
                    }
                }
            }
        }
        let Some(accepted) = result.take() else {
            return false;
        };
        let Some(frame) = frames.last_mut() else {
            return accepted;
        };
        if accepted == frame.all {
            next = frame.children.next();
            if next.is_some() {
                continue;
            }
        }
        frames.pop();
        result = Some(accepted);
    }
}

fn generic_free_candidates(graph: &mut Graph, arbitrary: &BTreeSet<usize>) -> Vec<usize> {
    // Snapshot constructor children before interning candidates. New candidates
    // do not extend the snapshot or create further intersection combinations.
    let intersections = graph
        .nodes
        .iter()
        .filter_map(|node| {
            let children = match &node.kind {
                Type::Tuple(children) => children,
                Type::Class { arguments, .. } if arguments.len() > 1 => arguments,
                _ => return None,
            };
            Some((children.clone(), node.scope.clone()))
        })
        .collect::<Vec<_>>();
    for (children, scope) in intersections {
        graph.intern(Type::Intersection(children), scope);
    }
    (0..graph.nodes.len())
        .filter(|root| {
            let mut pending = vec![*root];
            let mut seen = BTreeSet::new();
            while let Some(id) = pending.pop() {
                if !seen.insert(id) {
                    continue;
                }
                if matches!(graph.nodes[id].kind, Type::Generic { .. })
                    || matches!(graph.nodes[id].kind, Type::Bound { owner, .. } if !arbitrary.contains(&owner))
                {
                    return false;
                }
                pending.extend(graph.nodes[id].kind.children());
            }
            true
        })
        .collect()
}
