//! Structural ordering without recursive calls or reference unfolding.
//!
//! Canonical interning makes structural equality agree with identifier equality.
//! The visited-pair set skips repeated work on an acyclic graph. It does not
//! establish equality between separately interned recursive definitions.

use std::cmp::Ordering;
use std::collections::BTreeSet;

use crate::frontend::problem::Callable;

use super::{FactorNode, SArm, SFactor, SValue};

/// Comparison follows immutable constructor edges with a stack. References are leaves.
/// Shared node pairs are visited once, so sharing does not expand into type trees.
enum CompareTask<'a> {
    Value(&'a SValue, &'a SValue),
    Arm(&'a SArm, &'a SArm),
    Factor(&'a SFactor, &'a SFactor),
    Values(&'a [SValue], &'a [SValue]),
    Callable(&'a Callable<SValue>, &'a Callable<SValue>),
    Order(Ordering),
}

fn structural_order(first: CompareTask<'_>) -> Ordering {
    let mut pending = vec![first];
    let mut seen = BTreeSet::new();
    while let Some(task) = pending.pop() {
        match task {
            CompareTask::Order(order) if order != Ordering::Equal => return order,
            CompareTask::Order(_) => {}
            CompareTask::Value(left, right) => {
                if left == right || !seen.insert((left.0.id, right.0.id)) {
                    continue;
                }
                pending.push(CompareTask::Order(
                    left.arms().len().cmp(&right.arms().len()),
                ));
                pending.extend(
                    left.arms()
                        .iter()
                        .zip(right.arms())
                        .rev()
                        .map(|(left, right)| CompareTask::Arm(left, right)),
                );
            }
            CompareTask::Arm(left, right) => {
                if left == right || !seen.insert((left.0.id, right.0.id)) {
                    continue;
                }
                pending.push(CompareTask::Order(
                    left.factors().len().cmp(&right.factors().len()),
                ));
                pending.extend(
                    left.factors()
                        .iter()
                        .zip(right.factors())
                        .rev()
                        .map(|(left, right)| CompareTask::Factor(left, right)),
                );
            }
            CompareTask::Values(left, right) => {
                pending.push(CompareTask::Order(left.len().cmp(&right.len())));
                pending.extend(
                    left.iter()
                        .zip(right)
                        .rev()
                        .map(|(left, right)| CompareTask::Value(left, right)),
                );
            }
            CompareTask::Callable(left, right) => {
                pending.push(CompareTask::Value(&left.ret, &right.ret));
                pending.push(CompareTask::Values(&left.params, &right.params));
            }
            CompareTask::Factor(left, right) => {
                if left == right || !seen.insert((left.0.id, right.0.id)) {
                    continue;
                }
                let order = match (left.node(), right.node()) {
                    (FactorNode::Bound(left), FactorNode::Bound(right)) => left.cmp(right),
                    (FactorNode::Class(left), FactorNode::Class(right)) => {
                        pending.push(CompareTask::Values(&left.arguments, &right.arguments));
                        left.class.cmp(&right.class)
                    }
                    (FactorNode::Rigid(left), FactorNode::Rigid(right)) => left.cmp(right),
                    (FactorNode::Ref(left), FactorNode::Ref(right)) => left.cmp(right),
                    (FactorNode::Tuple(left), FactorNode::Tuple(right)) => {
                        pending.push(CompareTask::Values(left, right));
                        Ordering::Equal
                    }
                    (FactorNode::Callable(left), FactorNode::Callable(right)) => {
                        pending.push(CompareTask::Callable(left, right));
                        Ordering::Equal
                    }
                    (FactorNode::Generic(left), FactorNode::Generic(right)) => {
                        pending.push(CompareTask::Callable(&left.body, &right.body));
                        left.parameters.cmp(&right.parameters)
                    }
                    (FactorNode::Choice(left), FactorNode::Choice(right)) => left.cmp(right),
                    (left, right) => factor_rank(left).cmp(&factor_rank(right)),
                };
                if order != Ordering::Equal {
                    return order;
                }
            }
        }
    }
    Ordering::Equal
}

fn factor_rank(factor: &FactorNode) -> u8 {
    match factor {
        FactorNode::Bound(_) => 0,
        FactorNode::Class(_) => 1,
        FactorNode::Rigid(_) => 2,
        FactorNode::Ref(_) => 3,
        FactorNode::Tuple(_) => 4,
        FactorNode::Callable(_) => 5,
        FactorNode::Generic(_) => 6,
        FactorNode::Choice(_) => 7,
    }
}

impl PartialOrd for SFactor {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for SFactor {
    fn cmp(&self, other: &Self) -> Ordering {
        structural_order(CompareTask::Factor(self, other))
    }
}
impl PartialOrd for SArm {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for SArm {
    fn cmp(&self, other: &Self) -> Ordering {
        structural_order(CompareTask::Arm(self, other))
    }
}
impl PartialOrd for SValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for SValue {
    fn cmp(&self, other: &Self) -> Ordering {
        structural_order(CompareTask::Value(self, other))
    }
}
