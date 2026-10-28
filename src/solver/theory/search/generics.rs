//! Generic binder substitution and ordered live parameter positions.

use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroU32;

use crate::frontend::problem::{BoundRef, Callable, Generic};
use crate::indices::{checked_u32, parameter_positions};

use super::graph::{FactorNode, Graph, SFactor, SValue};

/// Substitute one binder through complete callable children.
///
/// Replacements are returned directly, so their own bound references retain
/// their owners. Removing a binder lowers references to its outer binders
/// by one level.
pub fn substitute_callable(
    graph: &Graph,
    body: &Callable<SValue>,
    depth: u32,
    arguments: &[SValue],
) -> Callable<SValue> {
    map_bounds_callable(graph, body, depth, &mut |reference, depth| {
        if reference.binder() == depth {
            let Some(argument) = arguments.get(reference.position() as usize) else {
                panic!("bound reference exceeds substitution arguments: {reference:?}");
            };
            return argument.clone();
        }
        let binder = if reference.binder() > depth {
            reference.binder() - 1
        } else {
            reference.binder()
        };
        graph.factor(FactorNode::Bound(BoundRef::new(
            binder,
            reference.position(),
        )))
    })
}

fn renumber_callable(
    graph: &Graph,
    body: &Callable<SValue>,
    depth: u32,
    positions: &BTreeMap<u32, u32>,
) -> Callable<SValue> {
    map_bounds_callable(graph, body, depth, &mut |reference, depth| {
        let position = if reference.binder() == depth {
            let Some(position) = positions.get(&reference.position()) else {
                panic!("generic canonicalization lost a live parameter: {reference:?}");
            };
            *position
        } else {
            reference.position()
        };
        graph.factor(FactorNode::Bound(BoundRef::new(
            reference.binder(),
            position,
        )))
    })
}

fn map_bounds_callable(
    graph: &Graph,
    body: &Callable<SValue>,
    depth: u32,
    map_bound: &mut impl FnMut(BoundRef, u32) -> SValue,
) -> Callable<SValue> {
    body.map(|child| map_bounds_value(graph, child, depth, map_bound))
}

fn map_bounds_value(
    graph: &Graph,
    value: &SValue,
    depth: u32,
    map_bound: &mut impl FnMut(BoundRef, u32) -> SValue,
) -> SValue {
    graph.union(value.arms().iter().map(|arm| {
        graph.intersection(
            arm.factors()
                .iter()
                .map(|factor| map_bounds_factor(graph, factor, depth, map_bound)),
        )
    }))
}

/// Rebuild constructors with one rule for bound references.
///
/// Only nested generics increase depth. Their bodies are normalized after
/// mapping their children. A replacement value is not mapped again.
fn map_bounds_factor(
    graph: &Graph,
    factor: &SFactor,
    depth: u32,
    map_bound: &mut impl FnMut(BoundRef, u32) -> SValue,
) -> SValue {
    match factor.node() {
        FactorNode::Bound(reference) => map_bound(*reference, depth),
        FactorNode::Class(application) => graph.factor(FactorNode::Class(
            application.map(|argument| map_bounds_value(graph, argument, depth, map_bound)),
        )),
        FactorNode::Rigid(id) => graph.factor(FactorNode::Rigid(*id)),
        FactorNode::Ref(id) => graph.factor(FactorNode::Ref(*id)),
        FactorNode::Tuple(elements) => graph.factor(FactorNode::Tuple(
            elements
                .iter()
                .map(|element| map_bounds_value(graph, element, depth, map_bound))
                .collect(),
        )),
        FactorNode::Callable(body) => graph.factor(FactorNode::Callable(map_bounds_callable(
            graph, body, depth, map_bound,
        ))),
        FactorNode::Generic(generic) => {
            let body = map_bounds_callable(graph, &generic.body, depth + 1, map_bound);
            graph.value(normalize_generic(graph, generic.parameters, &body))
        }
        FactorNode::Choice(copy) => graph.factor(FactorNode::Choice(copy.clone())),
    }
}

/// Remove unused parameters and compact live positions in declaration order.
/// References to outer binders keep their positions.
pub fn normalize_generic(
    graph: &Graph,
    parameters: NonZeroU32,
    body: &Callable<SValue>,
) -> SFactor {
    let mut live = BTreeSet::new();
    for child in body.children() {
        collect_bound_positions_value(child, 0, parameters.get(), &mut live);
    }
    let Some(parameters) = NonZeroU32::new(checked_u32(live.len(), "live generic parameter count"))
    else {
        return graph.intern_factor(FactorNode::Callable(substitute_callable(
            graph,
            body,
            0,
            &[],
        )));
    };
    let positions = parameter_positions(&live);
    let body = renumber_callable(graph, body, 0, &positions);
    graph.intern_factor(FactorNode::Generic(Generic { parameters, body }))
}

fn collect_bound_positions_value(
    value: &SValue,
    depth: u32,
    parameters: u32,
    positions: &mut BTreeSet<u32>,
) {
    for arm in value.arms() {
        for factor in arm.factors() {
            collect_bound_positions_factor(factor, depth, parameters, positions);
        }
    }
}

fn collect_bound_positions_factor(
    factor: &SFactor,
    depth: u32,
    parameters: u32,
    positions: &mut BTreeSet<u32>,
) {
    match factor.node() {
        FactorNode::Bound(reference) if reference.binder() == depth => {
            assert!(
                reference.position() < parameters,
                "bound reference position exceeds its binder: {reference:?}"
            );
            positions.insert(reference.position());
        }
        node => {
            let depth = depth + u32::from(matches!(node, FactorNode::Generic(_)));
            for child in node.children() {
                collect_bound_positions_value(child, depth, parameters, positions);
            }
        }
    }
}
