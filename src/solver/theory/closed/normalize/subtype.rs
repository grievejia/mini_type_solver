//! Remove covered parts only after the complete witness has passed its checks.
//!
//! Each removal retains its containing union or intersection and the two
//! children that permit it. Recursive witnesses do not enter this pass.

use std::collections::BTreeSet;

use super::super::super::ClassRelation;
use super::super::{Builder, Node, Type, Value, is_subtype};

#[cfg(test)]
mod tests;

#[derive(Debug, Clone, PartialEq, Eq)]
struct Removal {
    removed: usize,
    other: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Rewrite {
    node: usize,
    removals: Vec<Removal>,
}

/// The complete value before and after its recorded finite removals.
/// Private records preserve each removal's position and binder owners.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Normalization {
    original: Value,
    result: Value,
    passes: Vec<Vec<Rewrite>>,
}

impl Normalization {
    pub fn original(&self) -> &Value {
        &self.original
    }

    pub fn result(&self) -> &Value {
        &self.result
    }

    /// Replay the recorded removals, including their containing types. This
    /// checks equivalence of the complete values without selecting parameters.
    pub fn validate(&self, relation: &ClassRelation<'_>) {
        let mut current = self.original.clone();
        for pass in &self.passes {
            let mut nodes = current.definition().nodes.clone();
            for rewrite in pass {
                let (children, union) = match &nodes[rewrite.node].kind {
                    Type::Union(children) => (children.clone(), true),
                    Type::Intersection(children) => (children.clone(), false),
                    _ => panic!("normalization removal has no containing lattice operation"),
                };
                let removed = rewrite
                    .removals
                    .iter()
                    .map(|removal| removal.removed)
                    .collect::<BTreeSet<_>>();
                for removal in &rewrite.removals {
                    assert!(
                        removal.removed != removal.other
                            && children.contains(&removal.removed)
                            && children.contains(&removal.other),
                        "normalization removal changed its children"
                    );
                    assert!(
                        !removed.contains(&removal.other),
                        "normalization removal refers to a removed child"
                    );
                    let roots = if union {
                        [removal.removed, removal.other]
                    } else {
                        [removal.other, removal.removed]
                    };
                    let values = snapshot(&nodes, &roots, relation);
                    assert!(
                        is_subtype(&values[0], &values[1], relation),
                        "normalization removal lost its read-only proof"
                    );
                }
                let children = children
                    .into_iter()
                    .filter(|child| !removed.contains(child))
                    .collect();
                nodes[rewrite.node].kind = if union {
                    Type::Union(children)
                } else {
                    Type::Intersection(children)
                };
            }
            current = snapshot(&nodes, &[current.node], relation).remove(0);
        }
        assert_eq!(
            current, self.result,
            "normalization records do not produce their complete result"
        );
    }
}

fn snapshot(nodes: &[Node], roots: &[usize], relation: &ClassRelation<'_>) -> Vec<Value> {
    let mut builder = Builder::new(relation.declarations);
    builder.nodes = nodes.to_vec();
    builder.finish(roots)
}

fn remove_covered(
    nodes: &mut [Node],
    id: usize,
    relation: &ClassRelation<'_>,
    rewrites: &mut Vec<Rewrite>,
) {
    let (children, union) = match &nodes[id].kind {
        Type::Union(children) => (children.clone(), true),
        Type::Intersection(children) => (children.clone(), false),
        _ => return,
    };
    let values = snapshot(nodes, &children, relation);
    let mut others = vec![None; children.len()];
    for (index, value) in values.iter().enumerate() {
        for (other, candidate) in values.iter().enumerate() {
            if index == other {
                continue;
            }
            let (lower, upper) = if union {
                (value, candidate)
            } else {
                (candidate, value)
            };
            if is_subtype(lower, upper, relation)
                && (other < index || !is_subtype(upper, lower, relation))
            {
                others[index] = Some(other);
                break;
            }
        }
    }
    if others.iter().all(Option::is_none) {
        return;
    }
    let mut removals = Vec::new();
    for (index, other) in others.iter().enumerate() {
        let Some(mut other) = *other else {
            continue;
        };
        // Equivalent children point to an earlier child. Each other step is
        // strict, so a chain ends at a child that stays in this operation.
        for _ in &children {
            let Some(next) = others[other] else {
                break;
            };
            other = next;
        }
        assert!(
            others[other].is_none(),
            "normalization removal chain has a cycle"
        );
        removals.push(Removal {
            removed: children[index],
            other: children[other],
        });
    }
    rewrites.push(Rewrite { node: id, removals });
    let children = children
        .into_iter()
        .zip(others)
        .filter_map(|(child, other)| other.is_none().then_some(child))
        .collect();
    nodes[id].kind = if union {
        Type::Union(children)
    } else {
        Type::Intersection(children)
    };
}

/// A finite pass can use transitivity with its recorded removal comparisons.
/// It changes no comparison choice or generic parameter selection.
pub fn normalize(value: &Value, relation: &ClassRelation<'_>) -> Normalization {
    assert!(
        !value.contains_recursion(),
        "recursive values use lattice normalization only"
    );
    let mut current = value.clone();
    let mut passes = Vec::new();
    loop {
        let mut rewrites = Vec::new();
        let mut nodes = current.definition().nodes.clone();
        let root = current.node;
        let mut pending = vec![(root, false)];
        let mut finished = BTreeSet::new();
        while let Some((id, ready)) = pending.pop() {
            if finished.contains(&id) {
                continue;
            }
            if ready {
                remove_covered(&mut nodes, id, relation, &mut rewrites);
                finished.insert(id);
            } else {
                pending.push((id, true));
                pending.extend(
                    nodes[id]
                        .kind
                        .children()
                        .into_iter()
                        .rev()
                        .map(|child| (child, false)),
                );
            }
        }
        // The checked input already has its structural normalization. Without
        // a removal, rebuilding it cannot change this value.
        if rewrites.is_empty() {
            return Normalization {
                original: value.clone(),
                result: current,
                passes,
            };
        }
        let mut builder = Builder::new(relation.declarations);
        builder.nodes = nodes;
        let mut values = builder.finish(&[root]);
        let next = values.remove(0);
        passes.push(rewrites);
        if current == next {
            return Normalization {
                original: value.clone(),
                result: next,
                passes,
            };
        }
        current = next;
    }
}
