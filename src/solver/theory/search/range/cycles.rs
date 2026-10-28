//! Remove comparison loops caused only by expanding recorded expressions.
//!
//! Each joined group keeps all checks outside that expansion. Constructor and
//! superclass steps are never removed. No chosen variable value is consulted.

use crate::solver::reachability;

use super::super::graph::FactorNode;
use super::{Comparison, EdgeKind, State};

// These steps only expand the left expression. They preserve the whole right
// expression and do not choose a factor, a union part, or a constructor rule.
fn expands_lower(parent: &Comparison, child: &Comparison) -> bool {
    parent.upper == child.upper
        && (parent.lower.arms().len() > 1
            || parent.lower.arms().iter().any(|arm| {
                arm.factors()
                    .iter()
                    .any(|factor| matches!(factor.node(), FactorNode::Ref(_)))
            }))
}

fn comparison_groups(state: &State) -> Vec<usize> {
    let mut edges = vec![Vec::new(); state.goals.len()];
    for (id, goal) in state.goals.iter().enumerate() {
        for (kind, child) in &goal.children {
            if *kind == EdgeKind::Ordinary
                && expands_lower(&goal.comparison, &state.goals[*child].comparison)
            {
                edges[id].push(*child);
            }
        }
    }
    reachability::groups(&edges)
}

/// Each removed step belongs to a loop of lower-expression expansions.
/// Adding comparisons can join more such loops. Every other step survives,
/// even when joining its endpoints makes it a self-edge.
pub fn cycles_pass(state: &State) -> bool {
    let groups = comparison_groups(state);
    // Group labels are original goal indices. Other indices stay isolated.
    let mut edges = vec![Vec::new(); state.goals.len()];
    for (id, goal) in state.goals.iter().enumerate() {
        for (kind, child) in &goal.children {
            if groups[id] != groups[*child]
                || *kind != EdgeKind::Ordinary
                || !expands_lower(&goal.comparison, &state.goals[*child].comparison)
            {
                edges[groups[id]].push((*kind, groups[*child]));
            }
        }
    }
    let all = edges
        .iter()
        .map(|children| children.iter().map(|(_, child)| *child).collect())
        .collect::<Vec<_>>();
    let full_groups = reachability::groups(&all);
    if edges.iter().enumerate().any(|(parent, children)| {
        children.iter().any(|(kind, child)| {
            *kind == EdgeKind::Superclass && full_groups[parent] == full_groups[*child]
        })
    }) {
        return false;
    }
    let ordinary = edges
        .iter()
        .map(|children| {
            children
                .iter()
                .filter_map(|(kind, child)| (*kind != EdgeKind::Constructor).then_some(*child))
                .collect()
        })
        .collect::<Vec<_>>();
    // After removing constructor steps, every remaining cycle is an unguarded loop.
    reachability::can_reach_cycle(&ordinary).is_empty()
}
