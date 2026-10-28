//! Scope conversions and generic uses in one comparison branch.
//!
//! Conversion choices depend on written types and visibility. They do not read
//! candidate values. All required links and instance routes survive together.

use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};

use super::super::super::ClassRelation;
use super::super::generics::{normalize_generic, substitute_callable};
use super::super::graph::{ChoiceCopy, FactorNode, Graph, SArm, SFactor, SValue};
use super::super::identities::{
    ChoiceId, ChoiceSite, Direction, GenericSide, GenericSite, Identities, PathStep, RequirementId,
    RequirementSite, RigidId, ScopeId, SiteId, TypePath, ValueKind, VarId, VarSite,
};
use super::{Alternative, Comparison, EdgeKind, Rule, State, Step, Undo, bare_variable};
use crate::frontend::problem::{AtomId, Callable, ClassId, ClassType, ClassVariance, Generic};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Context {
    pub check: AtomId,
    pub path: TypePath,
    pub scope: ScopeId,
}

impl Context {
    pub fn child(&self, step: PathStep) -> Self {
        let mut context = self.clone();
        context.path.push(step);
        context
    }
}

/// Rigid parameters introduced together in one branch's scope.
///
/// The parameters follow binder position order and belong to the stored scope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Introduction {
    /// Scope that owns these rigid parameters.
    pub scope: ScopeId,
    /// Parameters in the generic binder's position order.
    pub rigids: Vec<RigidId>,
}

impl Introduction {
    /// Arguments preserve each rigid parameter's identity and binder position.
    fn arguments(&self, graph: &Graph) -> Vec<SValue> {
        self.rigids
            .iter()
            .map(|rigid| graph.factor(FactorNode::Rigid(*rigid)))
            .collect()
    }
}

/// A deferred generic's converted source in its home scope for one branch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChoiceRecord {
    pub home: ScopeId,
    pub source: Generic<SValue>,
}

/// Instances and the comparisons that must repeat when an instance is added.
///
/// Reader indices refer to [`State::goals`] in the same branch. Registration
/// creates both fields. Rollback removes the route after undoing its edits.
#[derive(Debug, Default)]
struct Route {
    instances: BTreeMap<RequirementId, SValue>,
    readers: BTreeSet<usize>,
}

#[derive(Debug, Default)]
pub struct ScopeState {
    pub introductions: BTreeMap<SiteId, Introduction>,
    pub choices: BTreeMap<ChoiceId, ChoiceRecord>,
    routes: BTreeMap<ChoiceCopy, Route>,
}

#[derive(Debug)]
pub enum ScopeUndo {
    Introduction(SiteId),
    Choice(ChoiceId),
    Route(ChoiceCopy),
    Instance(ChoiceCopy, RequirementId),
    Reader(ChoiceCopy, usize),
}

impl ScopeState {
    /// Instances for a registered route. A missing route is a programming error.
    pub fn instances(&self, copy: &ChoiceCopy) -> &BTreeMap<RequirementId, SValue> {
        let Some(route) = self.routes.get(copy) else {
            panic!("a deferred instance table requires a registered route");
        };
        &route.instances
    }

    /// Registered copies and their instance tables, in route order.
    #[cfg(test)]
    pub fn instance_routes(
        &self,
    ) -> impl Iterator<Item = (&ChoiceCopy, &BTreeMap<RequirementId, SValue>)> {
        self.routes
            .iter()
            .map(|(copy, route)| (copy, &route.instances))
    }

    /// Undo edits before removing their route. Reader undo can leave an empty
    /// reader set; only route-registration undo removes the whole record.
    pub fn restore(&mut self, change: ScopeUndo) {
        match change {
            ScopeUndo::Introduction(site) => {
                self.introductions.remove(&site);
            }
            ScopeUndo::Choice(choice) => {
                self.choices.remove(&choice);
            }
            ScopeUndo::Route(copy) => {
                self.routes.remove(&copy);
            }
            ScopeUndo::Instance(copy, requirement) => {
                if let Some(route) = self.routes.get_mut(&copy) {
                    route.instances.remove(&requirement);
                }
            }
            ScopeUndo::Reader(copy, goal) => {
                if let Some(route) = self.routes.get_mut(&copy) {
                    route.readers.remove(&goal);
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Operation {
    Check(Comparison, Context, EdgeKind),
    Choice(ChoiceId, ChoiceRecord),
    Route(ChoiceCopy),
    Introduction(SiteId, Introduction),
}

/// A converted expression and the checks that make it valid at its destination.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Conversion {
    pub value: SValue,
    operations: Vec<Operation>,
}

impl Conversion {
    fn unchanged(value: SValue) -> Self {
        Self {
            value,
            operations: Vec::new(),
        }
    }
}

#[derive(Clone)]
struct Destination {
    context: Context,
    scope: ScopeId,
    owner: VarId,
    kind: ValueKind,
    bound_depth: u32,
}

impl Destination {
    fn child(&self, step: PathStep) -> Self {
        Self {
            context: self.context.child(step),
            ..self.clone()
        }
    }
}

fn site(
    generic: &Generic<SValue>,
    side: GenericSide,
    context: &Context,
    identities: &mut Identities,
) -> SiteId {
    identities.generic_site(GenericSite {
        check: context.check,
        path: context.path.clone(),
        side,
        scope: context.scope,
        generic: generic.clone(),
    })
}

/// Select generic-free arguments for a lower use in its existing scope.
/// Persistent identities survive rollback. Branch state must register each
/// variable so its bounds can be undone after a failed choice.
fn selection_arguments(
    graph: &Graph,
    site: SiteId,
    state: &mut State,
    identities: &mut Identities,
) -> Vec<SValue> {
    let generic = identities.generic(site);
    let scope = generic.scope;
    let count = generic.generic.parameters.get();
    (0..count)
        .map(|position| {
            let variable = identities.variable(VarSite::Selection { site, position }, scope);
            state.variable(variable);
            graph.factor(FactorNode::Ref(variable))
        })
        .collect()
}

/// Return persistent rigid identities in a child of the requested parent scope.
/// An adaptation's destination scope can differ from its comparison scope.
/// Branch registration belongs to the caller, so discarded conversion choices
/// leave no introduction in the witness.
fn introduce_rigids(site: SiteId, parent: ScopeId, identities: &mut Identities) -> Introduction {
    let count = identities.generic(site).generic.parameters.get();
    let scope = identities.child_scope(site, parent);
    let rigids = (0..count)
        .map(|position| identities.rigid(site, position, scope))
        .collect();
    Introduction { scope, rigids }
}

/// Record an introduction once per branch. Only its first insertion adds an
/// undo entry, so rollback retains introductions from before the checkpoint.
fn register_introduction(site: SiteId, introduction: &Introduction, state: &mut State) {
    if let Entry::Vacant(entry) = state.scopes.introductions.entry(site) {
        entry.insert(introduction.clone());
        state.undo.push(Undo::Scope(ScopeUndo::Introduction(site)));
    }
}

pub fn generic_comparison(
    graph: &Graph,
    id: usize,
    lower: &SFactor,
    upper: &SFactor,
    state: &mut State,
    identities: &mut Identities,
) -> Option<Step> {
    let context = state.goals[id].context.clone();
    if let Some(step) = deferred_comparison(graph, id, lower, upper, state, identities) {
        return Some(step);
    }
    if let FactorNode::Generic(generic) = upper.node() {
        let site = site(generic, GenericSide::Upper, &context, identities);
        let introduction = introduce_rigids(site, context.scope, identities);
        register_introduction(site, &introduction, state);
        let arguments = introduction.arguments(graph);
        state.rule(
            id,
            Rule::UpperGeneric {
                arguments: arguments.clone(),
            },
        );
        let mut inner = context.child(PathStep::GenericBody);
        inner.scope = introduction.scope;
        state.child_in(
            id,
            Comparison {
                lower: graph.value(lower.clone()),
                upper: graph.factor(FactorNode::Callable(substitute_callable(
                    graph,
                    &generic.body,
                    0,
                    &arguments,
                ))),
            },
            EdgeKind::Ordinary,
            inner,
        );
        return Some(Step::Done);
    }
    if let FactorNode::Generic(generic) = lower.node() {
        let site = site(generic, GenericSide::Lower, &context, identities);
        let arguments = selection_arguments(graph, site, state, identities);
        state.rule(
            id,
            Rule::LowerGeneric {
                arguments: arguments.clone(),
            },
        );
        let inner = context.child(PathStep::GenericBody);
        state.child_in(
            id,
            Comparison {
                lower: graph.factor(FactorNode::Callable(substitute_callable(
                    graph,
                    &generic.body,
                    0,
                    &arguments,
                ))),
                upper: graph.value(upper.clone()),
            },
            EdgeKind::Ordinary,
            inner,
        );
        return Some(Step::Done);
    }
    None
}

fn deferred_comparison(
    graph: &Graph,
    id: usize,
    lower: &SFactor,
    upper: &SFactor,
    state: &mut State,
    identities: &mut Identities,
) -> Option<Step> {
    let context = state.goals[id].context.clone();
    if let FactorNode::Choice(copy) = upper.node() {
        let Some(route) = state.scopes.routes.get_mut(copy) else {
            panic!("a deferred comparison requires a registered route");
        };
        if route.readers.insert(id) {
            state
                .undo
                .push(Undo::Scope(ScopeUndo::Reader(copy.clone(), id)));
        }
        let instances = state
            .scopes
            .instances(copy)
            .values()
            .cloned()
            .collect::<Vec<_>>();
        state.rule(id, Rule::Expansion);
        for instance in instances {
            state.child(
                id,
                Comparison {
                    lower: graph.value(lower.clone()),
                    upper: instance,
                },
                EdgeKind::Ordinary,
            );
        }
        return Some(Step::Done);
    }
    if let FactorNode::Choice(copy) = lower.node() {
        let requirement = identities.requirement(RequirementSite {
            check: context.check,
            path: context.path.clone(),
            upper: upper.clone(),
            route: copy.clone(),
        });
        ensure_instance(graph, id, copy, requirement, state, identities);
        let instance = state.scopes.instances(copy)[&requirement].clone();
        state.rule(
            id,
            Rule::Instance {
                copy: copy.clone(),
                requirement,
            },
        );
        state.child(
            id,
            Comparison {
                lower: instance,
                upper: graph.value(upper.clone()),
            },
            EdgeKind::Ordinary,
        );
        return Some(Step::Done);
    }
    None
}

/// A variable transfer follows its recorded lower contributions. Its source
/// reference must not be stored where it is hidden or has the wrong kind.
pub fn store(
    graph: &Graph,
    id: usize,
    variable: VarId,
    lower: &SValue,
    state: &mut State,
    identities: &mut Identities,
    relation: &ClassRelation<'_>,
) -> Step {
    let destination = Destination {
        context: state.goals[id].context.clone(),
        scope: identities.variable_scope(variable),
        owner: variable,
        kind: identities.variable_kind(variable),
        bound_depth: 0,
    };
    if can_reuse(lower, &destination, identities) {
        state.rule(id, Rule::Equation { variable });
        state.lower(variable, lower);
        return Step::Done;
    }
    if let Some(source) = bare_variable(lower) {
        state.rule(id, Rule::Transfer);
        state.reader(source, id);
        let contributions = state
            .bounds
            .entry(source)
            .or_default()
            .lower
            .iter()
            .cloned()
            .collect::<Vec<_>>();
        for lower in contributions {
            state.child(
                id,
                Comparison {
                    lower,
                    upper: graph.factor(FactorNode::Ref(variable)),
                },
                EdgeKind::Ordinary,
            );
        }
        return Step::Done;
    }
    let alternatives = convert_value(
        graph,
        lower,
        &destination,
        Direction::Widen,
        identities,
        state,
        relation,
    )
    .into_iter()
    .map(|conversion| Alternative::Conversion {
        variable,
        conversion,
    })
    .collect();
    Step::Choose(alternatives)
}

pub fn apply(
    graph: &Graph,
    parent: usize,
    variable: VarId,
    conversion: Conversion,
    state: &mut State,
    identities: &mut Identities,
) {
    for operation in &conversion.operations {
        match operation {
            Operation::Check(comparison, context, kind) => {
                state.child_in(parent, comparison.clone(), *kind, context.clone());
            }
            Operation::Choice(choice, record) => {
                if let Entry::Vacant(entry) = state.scopes.choices.entry(*choice) {
                    entry.insert(record.clone());
                    state.undo.push(Undo::Scope(ScopeUndo::Choice(*choice)));
                }
            }
            Operation::Route(copy) => {
                register_route(graph, parent, copy, state, identities);
            }
            Operation::Introduction(site, introduction) => {
                register_introduction(*site, introduction, state);
            }
        }
    }
    state.lower(variable, &conversion.value);
    state.rule(parent, Rule::Conversion(conversion));
}

fn can_reuse(value: &SValue, destination: &Destination, identities: &Identities) -> bool {
    let mut pending = vec![(value, destination.bound_depth)];
    while let Some((value, depth)) = pending.pop() {
        for factor in value.arms().iter().flat_map(SArm::factors) {
            match factor.node() {
                FactorNode::Ref(variable)
                    if !identities
                        .is_ancestor(identities.variable_scope(*variable), destination.scope)
                        || (destination.kind == ValueKind::GenericFree
                            && identities.variable_kind(*variable) == ValueKind::General) =>
                {
                    return false;
                }
                FactorNode::Rigid(rigid)
                    if !identities
                        .is_ancestor(identities.rigid_scope(*rigid), destination.scope) =>
                {
                    return false;
                }
                FactorNode::Bound(reference) if reference.binder() >= depth => return false,
                FactorNode::Generic(_) if destination.kind == ValueKind::GenericFree => {
                    return false;
                }
                FactorNode::Choice(_) => return false,
                node => {
                    let depth = depth + u32::from(matches!(node, FactorNode::Generic(_)));
                    pending.extend(node.children().map(|child| (child, depth)));
                }
            }
        }
    }
    true
}

fn mark_contents(operations: &mut [Operation], kind: EdgeKind) {
    for operation in operations {
        if let Operation::Check(_, _, edge) = operation
            && *edge != EdgeKind::Superclass
        {
            *edge = kind;
        }
    }
}

fn combine(parts: Vec<Vec<Conversion>>) -> Vec<(Vec<SValue>, Vec<Operation>)> {
    let mut combinations = vec![(Vec::new(), Vec::new())];
    for alternatives in parts {
        combinations = combinations
            .into_iter()
            .flat_map(|(values, operations)| {
                alternatives.iter().map(move |alternative| {
                    let mut values = values.clone();
                    values.push(alternative.value.clone());
                    let mut operations = operations.clone();
                    operations.extend(alternative.operations.clone());
                    (values, operations)
                })
            })
            .collect();
    }
    combinations
}

fn convert_value(
    graph: &Graph,
    value: &SValue,
    destination: &Destination,
    direction: Direction,
    identities: &mut Identities,
    state: &State,
    relation: &ClassRelation<'_>,
) -> Vec<Conversion> {
    let arms = value
        .arms()
        .iter()
        .map(|arm| {
            let factors = arm
                .factors()
                .iter()
                .enumerate()
                .map(|(position, factor)| {
                    convert_factor(
                        graph,
                        factor,
                        &destination.child(PathStep::UpperFactor(position)),
                        direction,
                        identities,
                        state,
                        relation,
                    )
                })
                .collect();
            combine(factors)
                .into_iter()
                .map(|(values, operations)| Conversion {
                    value: graph.intersection(values),
                    operations,
                })
                .collect()
        })
        .collect();
    combine(arms)
        .into_iter()
        .map(|(values, operations)| Conversion {
            value: graph.union(values),
            operations,
        })
        .collect()
}

/// Convert a callable body while retaining its callable type.
///
/// Every child must be visited before the product is formed. Child conversion
/// can allocate persistent identities even when another child has no alternatives.
/// Return alternatives vary fastest, after each complete parameter combination.
fn convert_callable(
    graph: &Graph,
    body: &Callable<SValue>,
    destination: &Destination,
    direction: Direction,
    identities: &mut Identities,
    state: &State,
    relation: &ClassRelation<'_>,
) -> Vec<(Callable<SValue>, Vec<Operation>)> {
    let parameter_alternatives = body
        .params
        .iter()
        .enumerate()
        .map(|(index, param)| {
            convert_value(
                graph,
                param,
                &destination.child(PathStep::Parameter(index)),
                direction.reverse(),
                identities,
                state,
                relation,
            )
        })
        .collect::<Vec<_>>();
    let returns = convert_value(
        graph,
        &body.ret,
        &destination.child(PathStep::Return),
        direction,
        identities,
        state,
        relation,
    );
    let mut alternatives = Vec::new();
    for (params, parameter_operations) in combine(parameter_alternatives) {
        for returned in &returns {
            let mut operations = parameter_operations.clone();
            operations.extend(returned.operations.clone());
            mark_contents(&mut operations, EdgeKind::Constructor);
            alternatives.push((
                Callable {
                    params: params.clone(),
                    ret: returned.value.clone(),
                },
                operations,
            ));
        }
    }
    alternatives
}

fn convert_variable(
    graph: &Graph,
    variable: VarId,
    destination: &Destination,
    direction: Direction,
    identities: &mut Identities,
) -> Conversion {
    let source = graph.factor(FactorNode::Ref(variable));
    if can_reuse(&source, destination, identities) {
        return Conversion::unchanged(source);
    }
    let scope = destination.scope;
    let site = VarSite::Proxy {
        source: variable,
        scope,
        direction,
        kind: destination.kind,
    };
    let copy = identities.variable(site, scope);
    let result = graph.factor(FactorNode::Ref(copy));
    let mut context = destination.context.clone();
    context.scope = identities.youngest(identities.variable_scope(variable), scope);
    let mut operations = Vec::new();
    if direction != Direction::Narrow {
        operations.push(Operation::Check(
            Comparison {
                lower: source.clone(),
                upper: result.clone(),
            },
            context.clone(),
            EdgeKind::Ordinary,
        ));
    }
    if direction != Direction::Widen {
        operations.push(Operation::Check(
            Comparison {
                lower: result.clone(),
                upper: source,
            },
            context,
            EdgeKind::Ordinary,
        ));
    }
    Conversion {
        value: result,
        operations,
    }
}

fn retained_class(
    graph: &Graph,
    class: &ClassType<SValue>,
    destination: &Destination,
    direction: Direction,
    identities: &mut Identities,
    state: &State,
    relation: &ClassRelation<'_>,
) -> Vec<Conversion> {
    let parts = class
        .arguments
        .iter()
        .zip(relation.declarations.class_parameters(class.class))
        .enumerate()
        .map(|(index, (argument, parameter))| {
            let direction = match parameter.variance() {
                ClassVariance::Invariant => Direction::Exact,
                ClassVariance::Covariant => direction,
                ClassVariance::Contravariant => direction.reverse(),
            };
            convert_value(
                graph,
                argument,
                &destination.child(PathStep::ClassArgument(index)),
                direction,
                identities,
                state,
                relation,
            )
        })
        .collect();
    combine(parts)
        .into_iter()
        .map(|(arguments, mut operations)| {
            mark_contents(&mut operations, EdgeKind::Constructor);
            Conversion {
                value: graph.factor(FactorNode::Class(ClassType {
                    class: class.class,
                    arguments,
                })),
                operations,
            }
        })
        .collect()
}

fn convert_class(
    graph: &Graph,
    class: &ClassType<SValue>,
    destination: &Destination,
    direction: Direction,
    identities: &mut Identities,
    state: &State,
    relation: &ClassRelation<'_>,
) -> Vec<Conversion> {
    let original = graph.factor(FactorNode::Class(class.clone()));
    if can_reuse(&original, destination, identities) {
        return vec![Conversion::unchanged(original)];
    }
    let mut alternatives = retained_class(
        graph,
        class,
        destination,
        direction,
        identities,
        state,
        relation,
    );
    if direction == Direction::Exact {
        return alternatives;
    }
    if direction == Direction::Widen {
        let mut ancestors = relation
            .hierarchy
            .ancestors(class.class)
            .iter()
            .filter(|template| template.class != ClassId::OBJECT)
            .map(|template| ClassType {
                class: template.class,
                arguments: graph.ancestor_arguments(class.class, template, &class.arguments),
            })
            .collect::<Vec<_>>();
        // Templates follow C3 lookup order. Keep search alternatives in structural order.
        ancestors.sort_by_key(|class| graph.factor(FactorNode::Class(class.clone())));
        let independent = ancestors
            .iter()
            .filter(|class| {
                class
                    .arguments
                    .iter()
                    .zip(relation.declarations.class_parameters(class.class))
                    .all(|(argument, parameter)| {
                        parameter.variance() != ClassVariance::Invariant
                            || can_reuse(argument, destination, identities)
                    })
            })
            .cloned()
            .collect::<Vec<_>>();
        if !independent.is_empty() {
            let parts = independent
                .iter()
                .map(|class| {
                    retained_class(
                        graph,
                        class,
                        destination,
                        direction,
                        identities,
                        state,
                        relation,
                    )
                })
                .collect();
            alternatives.extend(combine(parts).into_iter().map(|(values, mut operations)| {
                mark_contents(&mut operations, EdgeKind::Superclass);
                Conversion {
                    value: graph.intersection(values),
                    operations,
                }
            }));
        }
        for ancestor in ancestors {
            let mut converted = retained_class(
                graph,
                &ancestor,
                destination,
                direction,
                identities,
                state,
                relation,
            );
            for alternative in &mut converted {
                mark_contents(&mut alternative.operations, EdgeKind::Superclass);
            }
            alternatives.extend(converted);
        }
        alternatives.push(Conversion::unchanged(graph.object()));
    } else {
        alternatives.push(Conversion::unchanged(graph.never()));
    }
    let mut unique = Vec::new();
    for alternative in alternatives {
        if !unique.contains(&alternative) {
            unique.push(alternative);
        }
    }
    unique
}

fn convert_generic(
    graph: &Graph,
    generic: &Generic<SValue>,
    destination: &Destination,
    direction: Direction,
    identities: &mut Identities,
    state: &State,
    relation: &ClassRelation<'_>,
) -> Vec<Conversion> {
    if destination.kind == ValueKind::GenericFree && direction == Direction::Exact {
        return Vec::new();
    }
    if destination.kind == ValueKind::GenericFree && direction == Direction::Narrow {
        return narrow_generic(graph, generic, destination, identities, state, relation);
    }
    let mut inner = destination.child(PathStep::GenericBody);
    inner.kind = ValueKind::General;
    inner.bound_depth += 1;
    convert_callable(
        graph,
        &generic.body,
        &inner,
        direction,
        identities,
        state,
        relation,
    )
    .into_iter()
    .flat_map(|(body, mut operations)| {
        let factor = normalize_generic(graph, generic.parameters, &body);
        if destination.kind == ValueKind::General {
            return vec![Conversion {
                value: graph.value(factor),
                operations,
            }];
        }
        let FactorNode::Generic(source) = factor.node() else {
            // Removing the binder leaves a callable whose children were
            // converted for general storage. Convert those children for the
            // actual destination before storing the callable.
            return convert_value(
                graph,
                &graph.value(factor),
                destination,
                direction,
                identities,
                state,
                relation,
            )
            .into_iter()
            .map(|mut result| {
                let mut combined = operations.clone();
                combined.append(&mut result.operations);
                result.operations = combined;
                result
            })
            .collect();
        };
        let choice = identities.choice(ChoiceSite {
            owner: destination.owner,
            check: destination.context.check,
            path: destination.context.path.clone(),
            source: generic.clone(),
        });
        operations.push(Operation::Choice(
            choice,
            ChoiceRecord {
                home: destination.scope,
                source: source.clone(),
            },
        ));
        let copy = ChoiceCopy::home(choice);
        operations.push(Operation::Route(copy.clone()));
        vec![Conversion {
            value: graph.factor(FactorNode::Choice(copy)),
            operations,
        }]
    })
    .collect()
}

fn narrow_generic(
    graph: &Graph,
    generic: &Generic<SValue>,
    destination: &Destination,
    identities: &mut Identities,
    state: &State,
    relation: &ClassRelation<'_>,
) -> Vec<Conversion> {
    let site = site(
        generic,
        GenericSide::Adaptation,
        &destination.context,
        identities,
    );
    let introduction = introduce_rigids(site, destination.scope, identities);
    let arguments = introduction.arguments(graph);
    let substituted = substitute_callable(graph, &generic.body, 0, &arguments);
    let mut inner = destination.clone();
    inner.context.scope = introduction.scope;
    convert_callable(
        graph,
        &substituted,
        &inner,
        Direction::Narrow,
        identities,
        state,
        relation,
    )
    .into_iter()
    .map(|(body, mut operations)| {
        let value = graph.factor(FactorNode::Callable(body));
        operations.push(Operation::Check(
            Comparison {
                lower: value.clone(),
                upper: graph.factor(FactorNode::Callable(substituted.clone())),
            },
            inner.context.clone(),
            EdgeKind::Ordinary,
        ));
        operations.push(Operation::Introduction(site, introduction.clone()));
        Conversion { value, operations }
    })
    .collect()
}

fn convert_factor(
    graph: &Graph,
    factor: &SFactor,
    destination: &Destination,
    direction: Direction,
    identities: &mut Identities,
    state: &State,
    relation: &ClassRelation<'_>,
) -> Vec<Conversion> {
    match factor.node() {
        FactorNode::Bound(reference) if reference.binder() < destination.bound_depth => {
            vec![Conversion::unchanged(graph.value(factor.clone()))]
        }
        FactorNode::Bound(_) => Vec::new(),
        FactorNode::Rigid(rigid) => {
            if identities.is_ancestor(identities.rigid_scope(*rigid), destination.scope) {
                vec![Conversion::unchanged(graph.value(factor.clone()))]
            } else {
                match direction {
                    Direction::Widen => vec![Conversion::unchanged(graph.object())],
                    Direction::Narrow => vec![Conversion::unchanged(graph.never())],
                    Direction::Exact => Vec::new(),
                }
            }
        }
        FactorNode::Ref(variable) => vec![convert_variable(
            graph,
            *variable,
            destination,
            direction,
            identities,
        )],
        FactorNode::Class(class) => convert_class(
            graph,
            class,
            destination,
            direction,
            identities,
            state,
            relation,
        ),
        FactorNode::Tuple(children) => {
            let parts = children
                .iter()
                .enumerate()
                .map(|(index, child)| {
                    convert_value(
                        graph,
                        child,
                        &destination.child(PathStep::Tuple(index)),
                        direction,
                        identities,
                        state,
                        relation,
                    )
                })
                .collect();
            combine(parts)
                .into_iter()
                .map(|(children, mut operations)| {
                    mark_contents(&mut operations, EdgeKind::Constructor);
                    Conversion {
                        value: graph.factor(FactorNode::Tuple(children)),
                        operations,
                    }
                })
                .collect()
        }
        FactorNode::Callable(body) => convert_callable(
            graph,
            body,
            destination,
            direction,
            identities,
            state,
            relation,
        )
        .into_iter()
        .map(|(body, operations)| Conversion {
            value: graph.factor(FactorNode::Callable(body)),
            operations,
        })
        .collect(),
        FactorNode::Generic(generic) => convert_generic(
            graph,
            generic,
            destination,
            direction,
            identities,
            state,
            relation,
        ),
        FactorNode::Choice(copy) => {
            let home = state.scopes.choices[&copy.choice].home;
            let previous = copy.route.last().copied().unwrap_or(home);
            let target = identities.lowest_common_ancestor(previous, destination.scope);
            // Outward routes widen instances. They cannot supply a lower
            // or exact conversion in the opposite direction.
            if target != previous && direction != Direction::Widen {
                return Vec::new();
            }
            let mut copy = copy.clone();
            if target != previous {
                copy.route.push(target);
            }
            vec![Conversion {
                value: graph.factor(FactorNode::Choice(copy.clone())),
                operations: vec![Operation::Route(copy)],
            }]
        }
    }
}

fn instance_variable(
    copy: &ChoiceCopy,
    requirement: RequirementId,
    scope: ScopeId,
    identities: &mut Identities,
) -> VarId {
    identities.variable(
        VarSite::StoredInstance {
            copy: copy.clone(),
            requirement,
        },
        scope,
    )
}

/// Register a route before adding instances or readers.
///
/// Home routes use this operation too. An outward route requires its prefixes
/// to be registered. Existing home requirements are converted in prefix order.
fn register_route(
    graph: &Graph,
    parent: usize,
    copy: &ChoiceCopy,
    state: &mut State,
    identities: &mut Identities,
) {
    if state.scopes.routes.contains_key(copy) {
        return;
    }
    state.scopes.routes.insert(copy.clone(), Route::default());
    state.undo.push(Undo::Scope(ScopeUndo::Route(copy.clone())));
    let home = ChoiceCopy::home(copy.choice);
    let requirements = state
        .scopes
        .instances(&home)
        .keys()
        .copied()
        .collect::<Vec<_>>();
    for requirement in requirements {
        ensure_instance(graph, parent, copy, requirement, state, identities);
    }
}

/// The route must be registered. Release its borrow before queuing readers,
/// because queuing a comparison changes the branch state.
fn publish_instance(
    copy: &ChoiceCopy,
    requirement: RequirementId,
    value: SValue,
    state: &mut State,
) {
    let readers = {
        let Some(route) = state.scopes.routes.get_mut(copy) else {
            panic!("a deferred instance requires a registered route");
        };
        route.instances.insert(requirement, value);
        route.readers.iter().copied().collect::<Vec<_>>()
    };
    state
        .undo
        .push(Undo::Scope(ScopeUndo::Instance(copy.clone(), requirement)));
    for reader in readers {
        state.enqueue(reader);
    }
}

fn ensure_instance(
    graph: &Graph,
    parent: usize,
    copy: &ChoiceCopy,
    requirement: RequirementId,
    state: &mut State,
    identities: &mut Identities,
) {
    let record = state.scopes.choices[&copy.choice].clone();
    let home = ChoiceCopy::home(copy.choice);
    if !state.scopes.instances(&home).contains_key(&requirement) {
        let arguments = (0..record.source.parameters.get())
            .map(|position| {
                let variable = identities.variable(
                    VarSite::Instance {
                        choice: copy.choice,
                        requirement,
                        position,
                    },
                    record.home,
                );
                state.variable(variable);
                graph.factor(FactorNode::Ref(variable))
            })
            .collect::<Vec<_>>();
        let instance = graph.factor(FactorNode::Callable(substitute_callable(
            graph,
            &record.source.body,
            0,
            &arguments,
        )));
        let variable = instance_variable(&home, requirement, record.home, identities);
        let mut context = state.goals[parent].context.clone();
        context.scope = record.home;
        let target = graph.factor(FactorNode::Ref(variable));
        let source = graph.factor(FactorNode::Generic(record.source.clone()));
        let generic_goal = state.child_in(
            parent,
            Comparison {
                lower: source,
                upper: target.clone(),
            },
            EdgeKind::Ordinary,
            context.clone(),
        );
        state.rule(generic_goal, Rule::LowerGeneric { arguments });
        state.child_in(
            generic_goal,
            Comparison {
                lower: instance,
                upper: target,
            },
            EdgeKind::Ordinary,
            context,
        );
        publish_instance(
            &home,
            requirement,
            graph.factor(FactorNode::Ref(variable)),
            state,
        );
    }
    let routes = state
        .scopes
        .routes
        .keys()
        .filter(|route| route.choice == copy.choice && !route.route.is_empty())
        .cloned()
        .collect::<Vec<_>>();
    for route in routes {
        if state.scopes.instances(&route).contains_key(&requirement) {
            continue;
        }
        let Some((target, prefix)) = route.route.split_last() else {
            continue;
        };
        let prefix = ChoiceCopy {
            choice: copy.choice,
            route: prefix.to_vec(),
        };
        let source = state.scopes.instances(&prefix)[&requirement].clone();
        let variable = instance_variable(&route, requirement, *target, identities);
        let mut context = state.goals[parent].context.clone();
        context.scope = identities.youngest(record.home, *target);
        state.child_in(
            parent,
            Comparison {
                lower: source,
                upper: graph.factor(FactorNode::Ref(variable)),
            },
            EdgeKind::Ordinary,
            context,
        );
        publish_instance(
            &route,
            requirement,
            graph.factor(FactorNode::Ref(variable)),
            state,
        );
    }
}

impl Conversion {
    pub fn checks(&self) -> impl Iterator<Item = (&Comparison, &Context, EdgeKind)> {
        self.operations
            .iter()
            .filter_map(|operation| match operation {
                Operation::Check(comparison, context, kind) => Some((comparison, context, *kind)),
                _ => None,
            })
    }
}
