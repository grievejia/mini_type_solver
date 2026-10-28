//! Rank fixed type descriptions without allocation identifiers in the result.

use std::collections::{BTreeMap, BTreeSet};

use crate::frontend::problem::{BoundRef, ClassId};

use super::super::super::search::identities::RigidId;
use super::super::{Node, Type, free_bindings, reachable};
use super::finite::finite_keys;
use super::{Keys, cycle_reaching_nodes};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Head {
    Never,
    Bound(BoundRef),
    Class(ClassId, usize),
    Arbitrary(RigidId),
    Tuple(usize),
    Callable(usize),
    Generic(u32, usize),
    Union,
    Intersection,
}

fn head(node: &Node) -> Head {
    match &node.kind {
        Type::Never => Head::Never,
        Type::Arbitrary { identity, .. } => Head::Arbitrary(*identity),
        Type::Class(class) => Head::Class(class.class, class.arguments.len()),
        Type::Tuple(children) => Head::Tuple(children.len()),
        Type::Callable(body) => Head::Callable(body.params.len()),
        Type::Generic {
            parameters, body, ..
        } => Head::Generic(*parameters, body.params.len()),
        Type::Bound { owner, position } => {
            let Some(depth) = node.scope.iter().rev().position(|id| id == owner) else {
                panic!("recursive key lost a parameter owner");
            };
            let Ok(depth) = u32::try_from(depth) else {
                panic!("recursive key binding depth exceeds u32");
            };
            Head::Bound(BoundRef::new(depth, *position))
        }
        Type::Union(_) => Head::Union,
        Type::Intersection(_) => Head::Intersection,
        Type::Reference(_) => panic!("reference wrapper reached recursive ranking"),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Signature {
    head: Head,
    children: Vec<usize>,
    owner: Option<usize>,
}

fn assign<T: Clone + Ord>(signatures: &BTreeMap<usize, T>) -> BTreeMap<usize, usize> {
    let unique = signatures.values().cloned().collect::<BTreeSet<_>>();
    let ranks = unique
        .into_iter()
        .enumerate()
        .map(|(rank, signature)| (signature, rank))
        .collect::<BTreeMap<_, _>>();
    signatures
        .iter()
        .map(|(id, signature)| (*id, ranks[signature]))
        .collect()
}

fn child_ranks(node: &Node, ranks: &BTreeMap<usize, usize>) -> Vec<usize> {
    let mut children = node
        .kind
        .children()
        .iter()
        .map(|id| ranks[id])
        .collect::<Vec<_>>();
    if matches!(node.kind, Type::Union(_) | Type::Intersection(_)) {
        children.sort_unstable();
        children.dedup();
    }
    children
}

fn owner_rank(node: &Node, ranks: &BTreeMap<usize, usize>) -> Option<usize> {
    match node.kind {
        Type::Bound { owner, .. } => ranks.get(&owner).copied(),
        _ => None,
    }
}

fn refine(nodes: &[Node], live: &BTreeSet<usize>) -> BTreeMap<usize, usize> {
    let initial = live.iter().map(|id| (*id, head(&nodes[*id]))).collect();
    let mut ranks = assign(&initial);
    loop {
        let signatures = live
            .iter()
            .map(|id| {
                (
                    *id,
                    (
                        ranks[id],
                        child_ranks(&nodes[*id], &ranks),
                        owner_rank(&nodes[*id], &ranks),
                    ),
                )
            })
            .collect();
        let next = assign(&signatures);
        let old_count = ranks.values().collect::<BTreeSet<_>>().len();
        let new_count = next.values().collect::<BTreeSet<_>>().len();
        ranks = next;
        if new_count == old_count {
            return ranks;
        }
    }
}

/// Equal open expressions must refer to the same binder occurrences.
/// Closed generic types can still compare equal after parameter renaming.
pub fn ranks(nodes: &[Node], memo: &mut Keys) -> Vec<usize> {
    let cyclic = cycle_reaching_nodes(nodes);
    // Finite keys describe every child completely. They give the same groups
    // without refining those groups once for each level of a finite type.
    // Hash order chooses lookup positions. Complete keys still decide equality.
    let ranks = if cyclic.is_empty() {
        let keys = finite_keys(nodes, &cyclic, memo)
            .into_iter()
            .map(|(id, key)| (id, (key.hash(), key)))
            .collect();
        assign(&keys)
    } else {
        refine(nodes, &(0..nodes.len()).collect())
    };
    let free = free_bindings(nodes);
    let signatures = (0..nodes.len())
        .map(|id| (id, (ranks[&id], free[id].clone())))
        .collect();
    let ranks = assign(&signatures);
    (0..nodes.len()).map(|id| ranks[&id]).collect()
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct RecursiveKey {
    root: usize,
    groups: Vec<Signature>,
}

pub fn recursive_key(nodes: &[Node], root: usize) -> RecursiveKey {
    let live = reachable(nodes, root);
    let ranks = refine(nodes, &live);
    let groups = live
        .iter()
        .map(|id| {
            (
                ranks[id],
                Signature {
                    head: head(&nodes[*id]),
                    children: child_ranks(&nodes[*id], &ranks),
                    owner: owner_rank(&nodes[*id], &ranks),
                },
            )
        })
        .collect::<BTreeMap<_, _>>()
        .into_values()
        .collect();
    RecursiveKey {
        root: ranks[&root],
        groups,
    }
}
