//! Normalize lattice operations before comparing recursive definitions.
//!
//! The passes remove lattice wrappers and unused parameters without unfolding
//! constructors. Live parameters keep declaration order. Position compaction
//! gives the binder a new owner identity. Scoped expressions retain their owners,
//! positions, and saved scopes.

mod finite;
mod refine;
pub mod subtype;

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use crate::frontend::problem::{Callable, ClassId, ClassType};
use crate::solver::reachability;

use super::super::Shape;
use super::{Definition, Node, Type, free_bindings, reachable};
pub use finite::Keys;
use finite::{FiniteKey, finite_keys};
use refine::{RecursiveKey, ranks, recursive_key};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Key {
    Finite(FiniteKey),
    Recursive(RecursiveKey),
}

type Arm = BTreeSet<usize>;
type Arms = BTreeSet<Arm>;

/// Closed values can discard unused positions and saved scopes. Open values
/// retain their parameter owners, positions, and saved scopes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ParameterMode {
    NormalizeParameters,
    PreserveScope,
}

fn prune(nodes: &[Node], root: usize, mode: ParameterMode) -> (Vec<Node>, usize) {
    let types = reachable(nodes, root);
    let mut live = types.clone();
    if mode == ParameterMode::PreserveScope {
        loop {
            let old = live.len();
            for id in live.clone() {
                live.extend(&nodes[id].scope);
            }
            if live.len() == old {
                break;
            }
        }
    }
    let ids = live
        .iter()
        .enumerate()
        .map(|(new, old)| (*old, new))
        .collect::<BTreeMap<_, _>>();
    let dummy = live.len();
    let mut result = live
        .iter()
        .map(|id| {
            let mut kind = if types.contains(id) {
                nodes[*id].kind.map_children(|child| ids[&child])
            } else {
                let Type::Generic {
                    binding,
                    parameters,
                    ..
                } = &nodes[*id].kind
                else {
                    panic!("a saved scope contains only binders");
                };
                Type::Generic {
                    binding: Rc::clone(binding),
                    parameters: *parameters,
                    body: Callable {
                        params: Vec::new(),
                        ret: dummy,
                    },
                }
            };
            if let Type::Bound { owner, .. } | Type::Arbitrary { owner, .. } = &mut kind {
                *owner = ids[owner];
            }
            Node {
                kind,
                scope: nodes[*id]
                    .scope
                    .iter()
                    .filter_map(|owner| ids.get(owner).copied())
                    .collect(),
            }
        })
        .collect::<Vec<_>>();
    if live != types {
        result.push(Node {
            kind: Type::Never,
            scope: Vec::new(),
        });
    }
    (result, ids[&root])
}

fn shape(kind: &Type) -> Shape {
    match kind {
        Type::Class(class) if class.class != ClassId::OBJECT => Shape::Class,
        Type::Tuple(children) => Shape::Tuple(children.len()),
        Type::Callable(body) | Type::Generic { body, .. } => Shape::Callable(body.params.len()),
        _ => Shape::Unknown,
    }
}

fn normalized_arm(nodes: &[Node], factors: Arm, groups: Option<&[usize]>) -> Option<Arm> {
    if Shape::conflict(factors.iter().map(|factor| shape(&nodes[*factor].kind))) {
        return None;
    }
    let mut arm = Arm::new();
    let mut seen = BTreeSet::new();
    for factor in factors {
        if let Type::Class(class) = &nodes[factor].kind {
            if class.class == ClassId::NEVER {
                return None;
            }
            if class.class == ClassId::OBJECT {
                continue;
            }
        }
        let group = groups.map_or(factor, |groups| groups[factor]);
        if seen.insert(group) {
            arm.insert(factor);
        }
    }
    Some(arm)
}

fn combine(nodes: &[Node], left: &Arms, right: &Arms, groups: Option<&[usize]>) -> Arms {
    left.iter()
        .flat_map(|left| {
            right.iter().filter_map(|right| {
                normalized_arm(nodes, left.union(right).copied().collect(), groups)
            })
        })
        .collect()
}

fn lattice_forms(nodes: &[Node], groups: Option<&[usize]>) -> Vec<Arms> {
    let mut forms: Vec<Option<Arms>> = vec![None; nodes.len()];
    for seed in 0..nodes.len() {
        let mut pending = vec![(seed, false)];
        while let Some((id, finished)) = pending.pop() {
            if forms[id].is_some() {
                continue;
            }
            let node = &nodes[id];
            if !finished
                && matches!(
                    node.kind,
                    Type::Reference(_) | Type::Union(_) | Type::Intersection(_)
                )
            {
                pending.push((id, true));
                pending.extend(
                    node.kind
                        .children()
                        .into_iter()
                        .rev()
                        .map(|child| (child, false)),
                );
                continue;
            }
            let get = |id: usize| {
                let Some(form) = &forms[id] else {
                    panic!("lattice child was not evaluated");
                };
                form
            };
            let form = match &node.kind {
                Type::Never => Arms::new(),
                Type::Reference(target) => get(*target).clone(),
                Type::Union(children) => children
                    .iter()
                    .flat_map(|child| get(*child).iter().cloned())
                    .collect(),
                Type::Intersection(children) => children
                    .iter()
                    .fold(Arms::from([Arm::new()]), |left, child| {
                        combine(nodes, &left, get(*child), groups)
                    }),
                _ => normalized_arm(nodes, Arm::from([id]), groups)
                    .into_iter()
                    .collect(),
            };
            let form = if form.contains(&Arm::new()) {
                Arms::from([Arm::new()])
            } else {
                form
            };
            let form = if let Some(groups) = groups {
                let mut unique = BTreeMap::new();
                for arm in form {
                    let key = arm
                        .iter()
                        .map(|factor| groups[*factor])
                        .collect::<BTreeSet<_>>();
                    unique.entry(key).or_insert(arm);
                }
                unique.into_values().collect()
            } else {
                form
            };
            forms[id] = Some(form);
        }
    }
    forms
        .into_iter()
        .map(|form| {
            let Some(form) = form else {
                panic!("lattice position was not evaluated");
            };
            form
        })
        .collect()
}

fn wrap(nodes: &mut Vec<Node>, kind: Type, scope: &[usize]) -> usize {
    match &kind {
        Type::Union(children) | Type::Intersection(children) if children.len() == 1 => {
            return children[0];
        }
        _ => {}
    }
    let id = nodes.len();
    nodes.push(Node {
        kind,
        scope: scope.to_vec(),
    });
    id
}

fn lattice(
    nodes: &[Node],
    root: usize,
    groups: Option<&[usize]>,
    mode: ParameterMode,
) -> (Vec<Node>, usize) {
    let forms = lattice_forms(nodes, groups);
    let mut next = nodes
        .iter()
        .map(|node| Node {
            kind: if matches!(
                node.kind,
                Type::Reference(_) | Type::Union(_) | Type::Intersection(_)
            ) {
                Type::Never
            } else {
                node.kind.clone()
            },
            scope: node.scope.clone(),
        })
        .collect::<Vec<_>>();
    let never = wrap(&mut next, Type::Never, &[]);
    let object = wrap(
        &mut next,
        Type::Class(ClassType::plain(ClassId::OBJECT)),
        &[],
    );
    let mut replacements = Vec::new();
    for (id, arms) in forms.iter().enumerate() {
        let mut children = Vec::new();
        for arm in arms {
            let arm = if arm.is_empty() {
                object
            } else {
                wrap(
                    &mut next,
                    Type::Intersection(arm.iter().copied().collect()),
                    &nodes[id].scope,
                )
            };
            children.push(arm);
        }
        let value = if children.is_empty() {
            never
        } else {
            wrap(&mut next, Type::Union(children), &nodes[id].scope)
        };
        replacements.push(value);
    }
    for (id, node) in nodes.iter().enumerate() {
        if node.kind.is_constructor() {
            next[id].kind = node.kind.map_children(|child| replacements[child]);
        }
    }
    prune(&next, replacements[root], mode)
}

fn remove_unused_parameters(nodes: &mut [Node]) -> bool {
    let mut live: BTreeMap<usize, BTreeSet<u32>> = BTreeMap::new();
    for node in nodes.iter() {
        if let Type::Bound { owner, position }
        | Type::Arbitrary {
            owner, position, ..
        } = node.kind
        {
            live.entry(owner).or_default().insert(position);
        }
    }
    let mut maps = BTreeMap::new();
    let mut removed = BTreeSet::new();
    let mut changed = false;
    for (id, node) in nodes.iter_mut().enumerate() {
        let Type::Generic {
            binding,
            parameters,
            body,
        } = &node.kind
        else {
            continue;
        };
        let positions = live.get(&id).cloned().unwrap_or_default();
        let Ok(count) = u32::try_from(positions.len()) else {
            panic!("generic count exceeds u32");
        };
        changed |= count != *parameters;
        let map = positions
            .into_iter()
            .enumerate()
            .map(|(new, old)| {
                let Ok(new) = u32::try_from(new) else {
                    panic!("generic position exceeds u32");
                };
                (old, new)
            })
            .collect::<BTreeMap<_, _>>();
        let positions_unchanged = map.iter().all(|(old, new)| old == new);
        maps.insert(id, map);
        node.kind = if count == 0 {
            removed.insert(id);
            Type::Callable(body.clone())
        } else {
            Type::Generic {
                binding: if positions_unchanged {
                    Rc::clone(binding)
                } else {
                    Rc::new(())
                },
                parameters: count,
                body: body.clone(),
            }
        };
    }
    for node in nodes {
        node.scope.retain(|owner| !removed.contains(owner));
        if let Type::Bound { owner, position } = &mut node.kind {
            *position = maps[owner][position];
        }
    }
    changed
}

/// Parameter owners and saved scopes are not type edges. Following those
/// links would make finite generic bodies appear recursive.
fn cycle_reaching_nodes(nodes: &[Node]) -> BTreeSet<usize> {
    let edges = nodes
        .iter()
        .map(|node| node.kind.children())
        .collect::<Vec<_>>();
    reachability::can_reach_cycle(&edges)
}

fn factor_group_count(nodes: &[Node], groups: &[usize]) -> usize {
    nodes
        .iter()
        .enumerate()
        .filter(|(_, node)| {
            node.kind.is_constructor()
                || matches!(node.kind, Type::Bound { .. } | Type::Arbitrary { .. })
        })
        .map(|(id, _)| groups[id])
        .collect::<BTreeSet<_>>()
        .len()
}

pub fn normalize(original: &[Node], original_root: usize, memo: &mut Keys) -> Definition {
    normalize_with_binders(
        original,
        original_root,
        ParameterMode::NormalizeParameters,
        memo,
    )
}

pub fn normalize_scoped(original: &[Node], original_root: usize, memo: &mut Keys) -> Definition {
    normalize_with_binders(original, original_root, ParameterMode::PreserveScope, memo)
}

fn normalize_with_binders(
    original: &[Node],
    original_root: usize,
    mode: ParameterMode,
    memo: &mut Keys,
) -> Definition {
    let (mut nodes, mut root) = prune(original, original_root, mode);
    loop {
        (nodes, root) = lattice(&nodes, root, None, mode);
        if mode == ParameterMode::PreserveScope || !remove_unused_parameters(&mut nodes) {
            break;
        }
    }
    loop {
        let groups = ranks(&nodes, memo);
        let factor_count = factor_group_count(&nodes, &groups);
        let (mut next, next_root) = lattice(&nodes, root, Some(&groups), mode);
        let parameters_changed =
            mode == ParameterMode::NormalizeParameters && remove_unused_parameters(&mut next);
        let next_groups = ranks(&next, memo);
        let next_count = factor_group_count(&next, &next_groups);
        nodes = next;
        root = next_root;
        if !parameters_changed && next_count == factor_count {
            break;
        }
    }
    let cyclic_reach = cycle_reaching_nodes(&nodes);
    let groups = ranks(&nodes, memo);
    let finite = finite_keys(&nodes, &cyclic_reach, memo);
    // Members of a final group have equal descriptions and free owners.
    // Reusing the key keeps each node's own parameter records.
    let mut recursive = BTreeMap::new();
    let keys = (0..nodes.len())
        .map(|id| {
            if cyclic_reach.contains(&id) {
                recursive
                    .entry(groups[id])
                    .or_insert_with(|| Key::Recursive(recursive_key(&nodes, id)))
                    .clone()
            } else {
                Key::Finite(finite[&id].clone())
            }
        })
        .collect::<Vec<_>>();
    for node in &mut nodes {
        if let Type::Union(children) | Type::Intersection(children) = &mut node.kind {
            children.sort_by(|left, right| keys[*left].cmp(&keys[*right]));
        }
    }
    let free_bindings = free_bindings(&nodes);
    Definition {
        nodes,
        root,
        keys,
        free_bindings,
    }
}
