//! Keep the existing finite order while sharing complete child keys.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::hash::{DefaultHasher, Hash, Hasher};
use std::mem;
use std::rc::Rc;

use crate::frontend::problem::{BoundRef, Callable, ClassId};

use super::super::super::search::identities::RigidId;
use super::super::{Node, Type};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Head {
    Value,
    Arm,
    Bound(BoundRef),
    Class(ClassId),
    Arbitrary(RigidId),
    Tuple,
    Callable,
    Generic(u32),
    Parameters,
}

#[derive(Debug)]
struct KeyNode {
    head: Head,
    children: Vec<FiniteKey>,
    hash: u64,
}

// A last root can own a long chain of keys. Release that chain with a stack
// so dropping a finite value does not recurse through its child types.
impl Drop for KeyNode {
    fn drop(&mut self) {
        let mut pending = mem::take(&mut self.children);
        while let Some(key) = pending.pop() {
            if let Ok(mut node) = Rc::try_unwrap(key.0) {
                pending.extend(mem::take(&mut node.children));
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct FiniteKey(Rc<KeyNode>);

/// Children come from this cache and never change. Their addresses identify
/// them while the cache owns their keys. Structural order uses their contents.
#[derive(Debug, Default)]
pub struct Keys {
    interned: BTreeMap<(Head, Vec<usize>), FiniteKey>,
}

impl Keys {
    pub fn new() -> Self {
        Self::default()
    }

    fn intern(&mut self, head: Head, children: Vec<FiniteKey>) -> FiniteKey {
        let key = (
            head.clone(),
            children
                .iter()
                .map(|child| Rc::as_ptr(&child.0) as usize)
                .collect(),
        );
        self.interned
            .entry(key)
            .or_insert_with(|| FiniteKey::new(head, children))
            .clone()
    }
}

impl FiniteKey {
    fn new(head: Head, children: Vec<Self>) -> Self {
        let mut hasher = DefaultHasher::new();
        head.hash(&mut hasher);
        children.len().hash(&mut hasher);
        for child in &children {
            child.0.hash.hash(&mut hasher);
        }
        Self(Rc::new(KeyNode {
            head,
            children,
            hash: hasher.finish(),
        }))
    }

    /// The full key must still confirm equality when hashes match.
    pub fn hash(&self) -> u64 {
        self.0.hash
    }
}

enum Compare {
    Keys(FiniteKey, FiniteKey),
    Order(Ordering),
}

impl Ord for FiniteKey {
    fn cmp(&self, other: &Self) -> Ordering {
        let mut seen = BTreeSet::new();
        let mut pending = vec![Compare::Keys(self.clone(), other.clone())];
        while let Some(task) = pending.pop() {
            let (left, right) = match task {
                Compare::Order(order) if order != Ordering::Equal => return order,
                Compare::Order(_) => continue,
                Compare::Keys(left, right) => (left, right),
            };
            if Rc::ptr_eq(&left.0, &right.0)
                || !seen.insert((Rc::as_ptr(&left.0), Rc::as_ptr(&right.0)))
            {
                continue;
            }
            let order = left.0.head.cmp(&right.0.head);
            if order != Ordering::Equal {
                return order;
            }
            pending.push(Compare::Order(
                left.0.children.len().cmp(&right.0.children.len()),
            ));
            pending.extend(
                left.0
                    .children
                    .iter()
                    .zip(&right.0.children)
                    .rev()
                    .map(|(left, right)| Compare::Keys(left.clone(), right.clone())),
            );
        }
        Ordering::Equal
    }
}

impl PartialOrd for FiniteKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for FiniteKey {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for FiniteKey {}

fn bound(node: &Node, owner: usize, position: u32) -> BoundRef {
    let Some(depth) = node.scope.iter().rev().position(|id| *id == owner) else {
        panic!("finite key reached a parameter without its owner");
    };
    let Ok(depth) = u32::try_from(depth) else {
        panic!("finite binding depth exceeds u32");
    };
    BoundRef::new(depth, position)
}

fn callable(
    head: Head,
    body: &Callable<usize>,
    keys: &BTreeMap<usize, FiniteKey>,
    memo: &mut Keys,
) -> FiniteKey {
    let parameters = memo.intern(
        Head::Parameters,
        body.params.iter().map(|id| keys[id].clone()).collect(),
    );
    memo.intern(head, vec![parameters, keys[&body.ret].clone()])
}

fn factor(
    nodes: &[Node],
    id: usize,
    keys: &BTreeMap<usize, FiniteKey>,
    memo: &mut Keys,
) -> FiniteKey {
    let node = &nodes[id];
    match &node.kind {
        Type::Arbitrary { identity, .. } => memo.intern(Head::Arbitrary(*identity), Vec::new()),
        Type::Bound { owner, position } => {
            memo.intern(Head::Bound(bound(node, *owner, *position)), Vec::new())
        }
        Type::Class(class) => memo.intern(
            Head::Class(class.class),
            class.arguments.iter().map(|id| keys[id].clone()).collect(),
        ),
        Type::Tuple(children) => memo.intern(
            Head::Tuple,
            children.iter().map(|id| keys[id].clone()).collect(),
        ),
        Type::Callable(body) => callable(Head::Callable, body, keys, memo),
        Type::Generic {
            parameters, body, ..
        } => callable(Head::Generic(*parameters), body, keys, memo),
        _ => panic!("finite factor key reached a lattice wrapper"),
    }
}

fn arm(nodes: &[Node], id: usize, keys: &BTreeMap<usize, FiniteKey>, memo: &mut Keys) -> FiniteKey {
    let mut factors = match &nodes[id].kind {
        Type::Intersection(children) => children
            .iter()
            .map(|id| factor(nodes, *id, keys, memo))
            .collect(),
        _ => vec![factor(nodes, id, keys, memo)],
    };
    factors.sort();
    memo.intern(Head::Arm, factors)
}

pub fn finite_keys(
    nodes: &[Node],
    cyclic: &BTreeSet<usize>,
    memo: &mut Keys,
) -> BTreeMap<usize, FiniteKey> {
    let mut keys = BTreeMap::new();
    for seed in 0..nodes.len() {
        if cyclic.contains(&seed) {
            continue;
        }
        let mut pending = vec![(seed, false)];
        while let Some((id, finished)) = pending.pop() {
            if keys.contains_key(&id) {
                continue;
            }
            if !finished {
                pending.push((id, true));
                pending.extend(
                    nodes[id]
                        .kind
                        .children()
                        .into_iter()
                        .rev()
                        .map(|child| (child, false)),
                );
                continue;
            }
            let mut arms = match &nodes[id].kind {
                Type::Never => Vec::new(),
                Type::Union(children) => children
                    .iter()
                    .map(|child| arm(nodes, *child, &keys, memo))
                    .collect(),
                _ => vec![arm(nodes, id, &keys, memo)],
            };
            arms.sort();
            keys.insert(id, memo.intern(Head::Value, arms));
        }
    }
    keys
}
