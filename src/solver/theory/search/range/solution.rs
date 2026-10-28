//! Build and check the values of an accepted comparison branch.

use super::super::super::ClassRelation;
use super::super::super::closed::{Builder, Normalization, Value, is_subtype, normalize_finite};
use super::super::generics::substitute_callable;
use super::super::graph::{FactorNode, Graph, SArm, SValue};
use super::super::identities::{Identities, RigidId, ScopeId, ValueKind, VarId};
use super::compare::constructor_children;
use super::holds_by_written_form;
use super::scopes::{Context, ScopeState};
use super::{Bounds, Comparison, EdgeKind, Goal, Rule, State, bare_variable, expand_arm};
use crate::frontend::problem::{Generic, MetaVarId};
use std::collections::{BTreeMap, BTreeSet};

/// Accepted choices and equations for building and checking one assignment.
///
/// Comparison records remain available until validation and output construction
/// finish. The returned solution owns the checked assignment. Test builds also
/// retain the original values from before normalization. The comparison records
/// are released before the solution is returned.
#[derive(Debug)]
pub struct Witness {
    equations: BTreeMap<VarId, SValue>,
    variables: BTreeMap<MetaVarId, VarId>,
    goals: Vec<Goal>,
    scopes: ScopeState,
    bounds: BTreeMap<VarId, Bounds>,
}

#[derive(Debug)]
struct Record<T> {
    source: Comparison,
    required: Vec<Comparison>,
    materialized: Comparison,
    context: Context,
    rule: Rule,
    endpoints: T,
    children: BTreeSet<(EdgeKind, usize)>,
}

#[derive(Debug)]
pub struct Prepared {
    internal: BTreeMap<VarId, usize>,
    introductions: Vec<(ScopeId, Vec<RigidId>)>,
    variables: BTreeMap<MetaVarId, VarId>,
    goals: Vec<Record<Comparison<usize>>>,
}

#[derive(Debug)]
struct CheckedValues {
    original: Comparison<Value>,
    normalized: Comparison<Value>,
}

#[derive(Debug)]
pub struct Checked {
    internal: BTreeMap<VarId, Value>,
    introductions: Vec<(ScopeId, Vec<RigidId>)>,
    variables: BTreeMap<MetaVarId, VarId>,
    goals: Vec<Record<CheckedValues>>,
    normalizations: BTreeMap<VarId, Normalization>,
}

impl Witness {
    pub fn from_state(
        equations: BTreeMap<VarId, SValue>,
        variables: BTreeMap<MetaVarId, VarId>,
        state: State,
    ) -> Self {
        Self {
            equations,
            variables,
            goals: state.goals,
            scopes: state.scopes,
            bounds: state.bounds,
        }
    }

    pub fn introductions(&self) -> Vec<(ScopeId, Vec<RigidId>)> {
        self.scopes
            .introductions
            .values()
            .map(|introduction| (introduction.scope, introduction.rigids.clone()))
            .collect()
    }

    pub fn variable_ids(&self) -> impl Iterator<Item = VarId> + '_ {
        self.equations.keys().copied()
    }

    pub fn prepare(
        self,
        graph: &Graph,
        builder: &mut Builder,
        roots: &mut Vec<usize>,
        identities: &Identities,
    ) -> Prepared {
        let introductions = self.introductions();
        builder.equations(&self.equations);
        let mut internal = BTreeMap::new();
        for variable in self.equations.keys() {
            let index = roots.len();
            roots.push(builder.scoped_root(
                &graph.factor(FactorNode::Ref(*variable)),
                identities.variable_scope(*variable),
                identities,
            ));
            internal.insert(*variable, index);
        }
        let goals = self
            .goals
            .into_iter()
            .map(|goal| {
                let source = Comparison {
                    lower: materialize(graph, &goal.comparison.lower, &self.scopes),
                    upper: materialize(graph, &goal.comparison.upper, &self.scopes),
                };
                let lower = roots.len();
                roots.push(builder.scoped_root(&source.lower, goal.context.scope, identities));
                let upper = roots.len();
                roots.push(builder.scoped_root(&source.upper, goal.context.scope, identities));
                let required = required_expansions(graph, &goal, &self.bounds, &self.scopes);
                Record {
                    required,
                    materialized: source,
                    source: goal.comparison,
                    context: goal.context,
                    rule: goal.rule,
                    endpoints: Comparison { lower, upper },
                    children: goal.children,
                }
            })
            .collect();
        Prepared {
            introductions,
            internal,
            variables: self.variables,
            goals,
        }
    }
}

/// Expand recorded expressions, rather than witness values. This also checks
/// requirements added after a variable or deferred record was first read.
fn required_expansions(
    graph: &Graph,
    goal: &Goal,
    bounds: &BTreeMap<VarId, Bounds>,
    scopes: &ScopeState,
) -> Vec<Comparison> {
    let source = &goal.comparison;
    match &goal.rule {
        Rule::Instance { copy, requirement } => vec![Comparison {
            lower: scopes.instances(copy)[requirement].clone(),
            upper: source.upper.clone(),
        }],
        Rule::Expansion | Rule::Transfer => {
            if let Some(variable) = bare_variable(&source.lower) {
                return bounds[&variable]
                    .lower
                    .iter()
                    .map(|lower| Comparison {
                        lower: lower.clone(),
                        upper: source.upper.clone(),
                    })
                    .collect();
            }
            let [arm] = source.lower.arms() else {
                panic!("left expansion has one arm");
            };
            if arm
                .factors()
                .iter()
                .any(|factor| matches!(factor.node(), FactorNode::Ref(_)))
            {
                return expand_arm(graph, arm, bounds)
                    .0
                    .into_iter()
                    .map(|arm| Comparison {
                        lower: graph.arm_value(arm),
                        upper: source.upper.clone(),
                    })
                    .collect();
            }
            let Some(factor) = source.upper.single_factor() else {
                panic!("deferred expansion has one factor");
            };
            let FactorNode::Choice(copy) = factor.node() else {
                panic!("expansion has no variable or deferred record");
            };
            scopes
                .instances(copy)
                .values()
                .map(|upper| Comparison {
                    lower: source.lower.clone(),
                    upper: upper.clone(),
                })
                .collect()
        }
        _ => Vec::new(),
    }
}

impl Prepared {
    pub fn check(
        self,
        values: &[Value],
        graph: &Graph,
        identities: &Identities,
        relation: &ClassRelation<'_>,
    ) -> Checked {
        let goals = self
            .goals
            .into_iter()
            .map(|goal| {
                let comparison = Comparison {
                    lower: values[goal.endpoints.lower].clone(),
                    upper: values[goal.endpoints.upper].clone(),
                };
                Record {
                    required: goal.required,
                    source: goal.source,
                    materialized: goal.materialized,
                    context: goal.context,
                    rule: goal.rule,
                    endpoints: CheckedValues {
                        original: comparison.clone(),
                        normalized: comparison,
                    },
                    children: goal.children,
                }
            })
            .collect();
        let internal = self
            .internal
            .into_iter()
            .map(|(id, root)| (id, values[root].clone()))
            .collect::<BTreeMap<_, _>>();
        for (variable, value) in &internal {
            assert!(
                identities.variable_kind(*variable) != ValueKind::GenericFree
                    || value.is_generic_free(),
                "a quantifier selection contains a generic callable"
            );
        }
        let checked = Checked {
            introductions: self.introductions,
            internal,
            variables: self.variables,
            goals,
            normalizations: BTreeMap::new(),
        };
        checked.validate_records(graph, relation, false);
        checked
    }
}

impl Checked {
    fn contains_recursion(&self) -> bool {
        self.internal.values().any(Value::contains_recursion)
            || self.goals.iter().any(|goal| {
                goal.endpoints.original.lower.contains_recursion()
                    || goal.endpoints.original.upper.contains_recursion()
            })
    }

    /// Return whether this witness must retain only structural normalization.
    ///
    /// If any witness returns true, the caller skips [`Self::normalize`] for
    /// every witness in the solution. Finite subtype removal requires acyclic
    /// values and class references.
    pub fn needs_structural_normalization(&self, relation: &ClassRelation<'_>) -> bool {
        let values = self
            .internal
            .values()
            .chain(self.goals.iter().flat_map(|goal| {
                [
                    &goal.endpoints.original.lower,
                    &goal.endpoints.original.upper,
                ]
            }));
        self.contains_recursion() || relation.has_reference_cycle(values.flat_map(Value::classes))
    }

    /// Remove finite parts covered by the remaining parts.
    ///
    /// Call only when [`Self::needs_structural_normalization`] is false for every
    /// witness in the solution. Recursive values and reachable cycles through
    /// class references retain the structural values already produced by closure.
    pub fn normalize(
        mut self,
        graph: &Graph,
        identities: &Identities,
        relation: &ClassRelation<'_>,
    ) -> Self {
        for (variable, value) in &mut self.internal {
            let normalization = normalize_finite(value, relation);
            normalization.validate(relation);
            *value = normalization.result().clone();
            self.normalizations.insert(*variable, normalization);
        }
        if self
            .normalizations
            .values()
            .all(|normalization| normalization.original() == normalization.result())
        {
            // Every assignment equals its checked value. Its accepted
            // comparisons remain valid.
            return self;
        }
        let mut builder = Builder::new(relation.declarations);
        builder.scopes(
            &self.introductions,
            self.internal.keys().copied(),
            identities,
        );
        builder.assigned_equations(&self.internal);
        let roots = self
            .goals
            .iter()
            .flat_map(|goal| {
                [
                    builder.scoped_root(&goal.materialized.lower, goal.context.scope, identities),
                    builder.scoped_root(&goal.materialized.upper, goal.context.scope, identities),
                ]
            })
            .collect::<Vec<_>>();
        let values = builder.finish(&roots);
        for (index, goal) in self.goals.iter_mut().enumerate() {
            // Source expressions stay unchanged. Only their variable values
            // come from the normalized witness. Structural graph construction
            // preserves the source binders and comparison identities.
            goal.endpoints.normalized = Comparison {
                lower: values[index * 2].clone(),
                upper: values[index * 2 + 1].clone(),
            };
        }
        self.validate_records(graph, relation, true);
        self
    }

    /// Values for declared metavariables at the current normalization stage.
    /// Each declared variable has a checked internal value. The cloned handles
    /// retain its graph and parameter owners after the records are dropped.
    pub fn witness_values(&self) -> BTreeMap<MetaVarId, Value> {
        self.variables
            .iter()
            .map(|(id, variable)| (*id, self.internal[variable].clone()))
            .collect()
    }
}

pub fn materialize(graph: &Graph, value: &SValue, scopes: &ScopeState) -> SValue {
    graph.union(value.arms().iter().map(|arm| {
        graph.intersection(arm.factors().iter().map(|factor| {
            match factor.node() {
                FactorNode::Choice(copy) => {
                    graph.intersection(scopes.instances(copy).values().cloned())
                }
                FactorNode::Class(class) => graph.factor(FactorNode::Class(
                    class.map(|child| materialize(graph, child, scopes)),
                )),
                FactorNode::Tuple(children) => graph.factor(FactorNode::Tuple(
                    children
                        .iter()
                        .map(|child| materialize(graph, child, scopes))
                        .collect(),
                )),
                FactorNode::Callable(body) => graph.factor(FactorNode::Callable(
                    body.map(|child| materialize(graph, child, scopes)),
                )),
                FactorNode::Generic(generic) => graph.factor(FactorNode::Generic(Generic {
                    parameters: generic.parameters,
                    body: generic.body.map(|child| materialize(graph, child, scopes)),
                })),
                _ => graph.value(factor.clone()),
            }
        }))
    }))
}

impl Checked {
    /// Read the selected rules with the supplied values. A generic rule checks
    /// its recorded substitution. It must not choose parameters again.
    fn validate_records(&self, graph: &Graph, relation: &ClassRelation<'_>, normalized: bool) {
        for goal in &self.goals {
            let values = if normalized {
                &goal.endpoints.normalized
            } else {
                &goal.endpoints.original
            };
            match &goal.rule {
                Rule::Pending => panic!("accepted comparison has no rule"),
                Rule::Written => {
                    assert!(
                        holds_by_written_form(&goal.source.lower, &goal.source.upper)
                            || goal.source.upper == graph.object(),
                        "written-form proof changed its comparison"
                    );
                    assert!(
                        is_subtype(&values.lower, &values.upper, relation),
                        "written-form proof failed after substitution: {:?}",
                        goal.source
                    );
                }
                Rule::Equation { variable } => {
                    assert_eq!(
                        bare_variable(&goal.source.upper),
                        Some(*variable),
                        "equation target changed"
                    );
                    if normalized {
                        let mapping = &self.normalizations[variable];
                        assert_eq!(&goal.endpoints.original.upper, mapping.original());
                        assert_eq!(&values.upper, mapping.result());
                        // Original membership has already passed. Both source
                        // expressions now use the same variable identifiers,
                        // mapped to equivalent values by checked removals.
                        // Substitution preserves that membership, including
                        // generic bodies. It needs no new parameter selection.
                    } else {
                        assert!(
                            is_subtype(&values.lower, &values.upper, relation),
                            "equation membership failed after substitution: {:?}",
                            goal.source
                        );
                    }
                }
                Rule::LowerGeneric { arguments } => {
                    let lower = instantiate_generic_body(graph, &goal.source.lower, arguments);
                    self.require_child(
                        goal,
                        &Comparison {
                            lower,
                            upper: goal.source.upper.clone(),
                        },
                        EdgeKind::Ordinary,
                    );
                }
                Rule::UpperGeneric { arguments } => {
                    let upper = instantiate_generic_body(graph, &goal.source.upper, arguments);
                    self.require_child(
                        goal,
                        &Comparison {
                            lower: goal.source.lower.clone(),
                            upper,
                        },
                        EdgeKind::Ordinary,
                    );
                }
                Rule::Constructor => {
                    let Some(lower) = goal.source.lower.single_factor() else {
                        panic!("constructor lower has one factor");
                    };
                    let Some(upper) = goal.source.upper.single_factor() else {
                        panic!("constructor upper has one factor");
                    };
                    let children = constructor_children(graph, lower, upper, relation)
                        .expect("accepted constructor rule exists");
                    for child in children {
                        self.require_child(goal, &child.comparison, child.kind);
                    }
                    if goal.children.is_empty() {
                        assert!(
                            is_subtype(&values.lower, &values.upper, relation),
                            "constructor leaf failed: {:?}",
                            goal.source
                        );
                    }
                }
                Rule::Exact | Rule::Stronger => {
                    self.validate_split(graph, goal, relation, normalized);
                }
                Rule::Conversion(conversion) => {
                    for (comparison, _, kind) in conversion.checks() {
                        self.require_child(goal, comparison, kind);
                    }
                }
                Rule::Instance { .. } | Rule::Expansion | Rule::Transfer => {
                    for comparison in &goal.required {
                        self.require_child(goal, comparison, EdgeKind::Ordinary);
                    }
                }
            }
        }
    }

    fn require_child(
        &self,
        parent: &Record<CheckedValues>,
        comparison: &Comparison,
        kind: EdgeKind,
    ) {
        assert!(
            parent
                .children
                .iter()
                .any(|(edge, child)| *edge == kind && self.goals[*child].source == *comparison),
            "accepted rule lost a required child comparison"
        );
    }

    fn validate_split(
        &self,
        graph: &Graph,
        goal: &Record<CheckedValues>,
        relation: &ClassRelation<'_>,
        normalized: bool,
    ) {
        if goal.source.lower.arms().len() > 1 {
            for arm in goal.source.lower.arms() {
                self.require_child(
                    goal,
                    &Comparison {
                        lower: graph.arm_value(arm.clone()),
                        upper: goal.source.upper.clone(),
                    },
                    EdgeKind::Ordinary,
                );
            }
            return;
        }
        let [upper_arm] = goal.source.upper.arms() else {
            assert!(
                goal.children
                    .iter()
                    .any(
                        |(_, child)| goal.source.upper.arms().iter().any(|arm| self.goals[*child]
                            .source
                            == Comparison {
                                lower: goal.source.lower.clone(),
                                upper: graph.arm_value(arm.clone())
                            })
                    ),
                "upper union lost its selected arm"
            );
            return;
        };
        if upper_arm.factors().len() != 1 {
            for factor in upper_arm.factors() {
                self.require_child(
                    goal,
                    &Comparison {
                        lower: goal.source.lower.clone(),
                        upper: graph.value(factor.clone()),
                    },
                    EdgeKind::Ordinary,
                );
            }
            return;
        }
        let selected = goal
            .children
            .iter()
            .find_map(|(_, child)| {
                let child = &self.goals[*child];
                (child.source.upper == goal.source.upper
                    && goal
                        .source
                        .lower
                        .arms()
                        .iter()
                        .flat_map(SArm::factors)
                        .any(|factor| graph.value(factor.clone()) == child.source.lower))
                .then_some(child)
            })
            .expect("lower intersection retains its selected factor");
        if normalized && goal.rule == Rule::Exact {
            // The selected factor can be removed from a finite intersection.
            // This read-only step supplies the middle type. The selected child's
            // proof retains its generic choices, so no new selection is needed.
            // Stronger checks expand a deferred choice in the lower expression.
            // Applying this check to them requires a proof that normalization
            // preserves the selected factor in intersections with deferred choices.
            assert!(
                is_subtype(
                    &goal.endpoints.normalized.lower,
                    &selected.endpoints.normalized.lower,
                    relation
                ),
                "normalized intersection lost its selected factor and removal proof"
            );
        }
    }
}

/// Instantiate the generic recorded by a lower selection or an upper introduction.
fn instantiate_generic_body(graph: &Graph, source: &SValue, arguments: &[SValue]) -> SValue {
    let Some(factor) = source.single_factor() else {
        panic!("recorded generic has one factor");
    };
    let FactorNode::Generic(generic) = factor.node() else {
        panic!("recorded rule lost its generic");
    };
    graph.factor(FactorNode::Callable(substitute_callable(
        graph,
        &generic.body,
        0,
        arguments,
    )))
}
