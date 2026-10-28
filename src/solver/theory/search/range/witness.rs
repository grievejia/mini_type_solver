//! Build variable values from all recorded `<:` rules.
//!
//! Resolve loops through `&` and `|` first. Keep class, tuple, and function types
//! whole during that step. Then fill in their variables and check every original
//! and added comparison.

use std::collections::{BTreeMap, BTreeSet};

use crate::solver::reachability;

use super::super::graph::{FactorNode, Graph, SArm, SValue};
use super::super::identities::VarId;

fn bare_dependencies(value: &SValue) -> BTreeSet<VarId> {
    value
        .arms()
        .iter()
        .flat_map(SArm::factors)
        .filter_map(|factor| match factor.node() {
            FactorNode::Ref(variable) => Some(*variable),
            _ => None,
        })
        .collect()
}

/// Group variables that refer back to one another through `&` and `|`.
/// Occurrences inside classes, tuples, and functions are handled when values
/// are filled in.
///
/// Every bare variable reference must have an equation. Groups use their
/// smallest `VarId` for ordering. Members use increasing `VarId` order.
fn components(equations: &BTreeMap<VarId, SValue>) -> Vec<Vec<VarId>> {
    let variables = equations.keys().copied().collect::<Vec<_>>();
    let positions = variables
        .iter()
        .enumerate()
        .map(|(index, variable)| (*variable, index))
        .collect::<BTreeMap<_, _>>();
    let edges = equations
        .values()
        .map(|value| {
            bare_dependencies(value)
                .into_iter()
                .map(|variable| positions[&variable])
                .collect()
        })
        .collect::<Vec<_>>();
    let groups = reachability::groups(&edges);
    let mut components = BTreeMap::<usize, Vec<VarId>>::new();
    for (variable, group) in variables.into_iter().zip(groups) {
        components.entry(group).or_default().push(variable);
    }
    components.into_values().collect()
}

fn substitute_bare(graph: &Graph, value: &SValue, variable: VarId, replacement: &SValue) -> SValue {
    graph.union(value.arms().iter().map(|arm| {
        graph.intersection(arm.factors().iter().map(|factor| {
            if factor.node() == &FactorNode::Ref(variable) {
                replacement.clone()
            } else {
                graph.value(factor.clone())
            }
        }))
    }))
}

pub fn eliminate(graph: &Graph, equations: &mut BTreeMap<VarId, SValue>) {
    for component in components(equations) {
        for (index, variable) in component.iter().enumerate() {
            let solved = graph.union(
                equations[variable]
                    .arms()
                    .iter()
                    .filter(|arm| {
                        !arm.factors()
                            .iter()
                            .any(|factor| factor.node() == &FactorNode::Ref(*variable))
                    })
                    .cloned()
                    .map(|arm| graph.arm_value(arm)),
            );
            equations.insert(*variable, solved.clone());
            for later in &component[index + 1..] {
                let substituted = substitute_bare(graph, &equations[later], *variable, &solved);
                equations.insert(*later, substituted);
            }
        }
        for (index, variable) in component.iter().enumerate().rev() {
            let solved = equations[variable].clone();
            for earlier in &component[..index] {
                let substituted = substitute_bare(graph, &equations[earlier], *variable, &solved);
                equations.insert(*earlier, substituted);
            }
        }
    }
}
