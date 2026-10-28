//! Semantic type normalization and generic binder rewriting.
//!
//! Normalization preserves constructor arguments and canonical bound positions.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroU32;

use crate::indices::parameter_positions;

use super::{
    BoundRef, Callable, ClassId, ClassType, Generic, TypeBuilder, TypeId, TypeNode, TypeStore,
    checked_u32,
};

/// Union and intersection use opposite absorbing and neutral classes.
#[derive(Debug, Clone, Copy)]
pub enum Junction {
    Union,
    Intersection,
}

impl Junction {
    /// A child of this class determines the whole expression.
    pub fn absorbing(self) -> ClassId {
        match self {
            Self::Union => ClassId::OBJECT,
            Self::Intersection => ClassId::NEVER,
        }
    }

    /// A child of this class has no effect on the expression.
    pub fn neutral(self) -> ClassId {
        match self {
            Self::Union => ClassId::NEVER,
            Self::Intersection => ClassId::OBJECT,
        }
    }
}

/// One binder operation with the data required for that operation.
#[derive(Debug, Clone, Copy)]
enum BinderMapping<'a> {
    Remove,
    Renumber(&'a BTreeMap<u32, u32>),
    Replace(&'a [BinderReplacement]),
}

/// One parameter's operation in a complete restriction selection.
#[derive(Debug, Clone, Copy)]
pub enum BinderReplacement {
    /// Keep the original bound reference.
    Keep,
    /// Intersect the reference with a closed restriction type.
    Upper(TypeId),
    /// Replace the reference with a closed exact member.
    Exact(TypeId),
}

/// Live parameters of the nearest binder after structural normalization.
#[must_use]
pub fn live_bound_positions(
    types: &TypeStore,
    body: &Callable<TypeId>,
    parameters: u32,
) -> BTreeSet<u32> {
    let mut live = BTreeSet::new();
    for child in body.children() {
        collect_bound_positions(types, *child, 0, parameters, &mut live);
    }
    live
}

fn collect_bound_positions(
    types: &TypeStore,
    type_id: TypeId,
    depth: u32,
    parameters: u32,
    positions: &mut BTreeSet<u32>,
) {
    match types.type_node(type_id) {
        TypeNode::Bound(reference) if reference.binder == depth => {
            assert!(
                reference.position < parameters,
                "bound reference position exceeds its binder: {reference:?}"
            );
            positions.insert(reference.position);
        }
        TypeNode::Class(application) => {
            for argument in &application.arguments {
                collect_bound_positions(types, *argument, depth, parameters, positions);
            }
        }
        TypeNode::Bound(_) | TypeNode::Flexible(_) => {}
        TypeNode::Tuple(children)
        | TypeNode::Union(children)
        | TypeNode::Intersection(children) => {
            for child in children {
                collect_bound_positions(types, *child, depth, parameters, positions);
            }
        }
        TypeNode::Callable(body) => {
            for child in body.children() {
                collect_bound_positions(types, *child, depth, parameters, positions);
            }
        }
        TypeNode::Generic(Generic { body, .. }) => {
            for child in body.children() {
                collect_bound_positions(types, *child, depth + 1, parameters, positions);
            }
        }
    }
}

fn compare_callables(
    types: &TypeStore,
    left: &Callable<TypeId>,
    right: &Callable<TypeId>,
) -> Ordering {
    for (left, right) in left.params.iter().zip(&right.params) {
        let order = compare_types(types, *left, *right);
        if order != Ordering::Equal {
            return order;
        }
    }
    left.params
        .len()
        .cmp(&right.params.len())
        .then_with(|| compare_types(types, left.ret, right.ret))
}

/// Stable structural order for canonical compound children.
#[must_use]
pub fn compare_types(types: &TypeStore, left: TypeId, right: TypeId) -> Ordering {
    let left_node = types.type_node(left);
    let right_node = types.type_node(right);
    match (left_node, right_node) {
        (TypeNode::Bound(left), TypeNode::Bound(right)) => left.cmp(right),
        (TypeNode::Class(left), TypeNode::Class(right)) => {
            let root_order = left.class.cmp(&right.class);
            if root_order != Ordering::Equal {
                return root_order;
            }
            for (left, right) in left.arguments.iter().zip(&right.arguments) {
                let order = compare_types(types, *left, *right);
                if order != Ordering::Equal {
                    return order;
                }
            }
            left.arguments.len().cmp(&right.arguments.len())
        }
        (TypeNode::Flexible(left), TypeNode::Flexible(right)) => left.cmp(right),
        (TypeNode::Tuple(left), TypeNode::Tuple(right))
        | (TypeNode::Union(left), TypeNode::Union(right))
        | (TypeNode::Intersection(left), TypeNode::Intersection(right)) => {
            for (left, right) in left.iter().zip(right) {
                let order = compare_types(types, *left, *right);
                if order != Ordering::Equal {
                    return order;
                }
            }
            left.len().cmp(&right.len())
        }
        (TypeNode::Callable(left), TypeNode::Callable(right)) => {
            compare_callables(types, left, right)
        }
        (TypeNode::Generic(left), TypeNode::Generic(right)) => left
            .parameters
            .cmp(&right.parameters)
            .then_with(|| compare_callables(types, &left.body, &right.body)),
        _ => type_rank(left_node).cmp(&type_rank(right_node)),
    }
}

impl TypeBuilder {
    /// Construct one canonical generic callable.
    ///
    /// Unused parameters are removed. Live parameters keep declaration order
    /// and receive consecutive positions. A body with no live parameter becomes
    /// a monomorphic callable with references to outer binders shifted inward.
    ///
    /// # Panics
    ///
    /// Panics if the binder is empty or its body names an out-of-range parameter.
    pub fn intern_generic(&mut self, parameters: u32, body: &Callable<TypeId>) -> TypeId {
        assert!(
            parameters != 0,
            "generic callable has no declared parameter"
        );
        let live = live_bound_positions(&self.store, body, parameters);
        let mut memo = BTreeMap::new();
        let Some(parameters) =
            NonZeroU32::new(checked_u32(live.len(), "live generic parameter count"))
        else {
            let body =
                body.map(|child| self.remap_binder(*child, 0, BinderMapping::Remove, &mut memo));
            return self.intern_callable(body.params, body.ret);
        };

        let positions = parameter_positions(&live);
        let body = body.map(|child| {
            self.remap_binder(*child, 0, BinderMapping::Renumber(&positions), &mut memo)
        });
        self.intern_node(TypeNode::Generic(Generic { parameters, body }))
    }

    /// Apply one complete restriction selection to the original callable body.
    ///
    /// The list has one entry per original parameter position. Replacement
    /// types contain no bound reference, metavariable, or generic callable.
    /// Inserted types are not rewritten. Within a nested generic, the rewrite
    /// applies outer replacements before normalizing the nested binder.
    ///
    /// # Panics
    ///
    /// Panics if a reference to the owning binder has no replacement entry.
    pub fn rewrite_binder(
        &mut self,
        body: &Callable<TypeId>,
        replacements: &[BinderReplacement],
    ) -> Callable<TypeId> {
        let mut memo = BTreeMap::new();
        body.map(|child| {
            self.remap_binder(*child, 0, BinderMapping::Replace(replacements), &mut memo)
        })
    }

    /// One memo belongs to one complete mapping. A shared type can occur at
    /// different binder depths, so depth is part of the memo key.
    fn remap_binder(
        &mut self,
        type_id: TypeId,
        depth: u32,
        mapping: BinderMapping<'_>,
        memo: &mut BTreeMap<(TypeId, u32), TypeId>,
    ) -> TypeId {
        if let Some(rewritten) = memo.get(&(type_id, depth)) {
            return *rewritten;
        }
        let node = self.store.type_node(type_id).clone();
        let rewritten = match node {
            TypeNode::Bound(reference) => match mapping {
                BinderMapping::Remove if reference.binder == depth => {
                    panic!("removed generic binder still has a live reference: {reference:?}");
                }
                BinderMapping::Remove if reference.binder > depth => {
                    self.intern_bound(BoundRef::new(reference.binder - 1, reference.position))
                }
                BinderMapping::Renumber(positions) if reference.binder == depth => {
                    let Some(position) = positions.get(&reference.position) else {
                        panic!("generic canonicalization lost a live parameter: {reference:?}");
                    };
                    self.intern_bound(BoundRef::new(reference.binder, *position))
                }
                BinderMapping::Replace(replacements) if reference.binder == depth => {
                    let Some(replacement) = replacements.get(reference.position as usize) else {
                        panic!("binder rewrite has no replacement for reference: {reference:?}");
                    };
                    match replacement {
                        BinderReplacement::Keep => type_id,
                        BinderReplacement::Upper(bound) => {
                            self.intern_intersection(vec![type_id, *bound])
                        }
                        BinderReplacement::Exact(member) => *member,
                    }
                }
                BinderMapping::Remove | BinderMapping::Renumber(_) | BinderMapping::Replace(_) => {
                    type_id
                }
            },
            TypeNode::Class(application) => {
                let application =
                    application.map(|argument| self.remap_binder(*argument, depth, mapping, memo));
                self.intern_class(application.class, application.arguments)
            }
            TypeNode::Flexible(_) => type_id,
            TypeNode::Tuple(children) => {
                let children = children
                    .into_iter()
                    .map(|child| self.remap_binder(child, depth, mapping, memo))
                    .collect();
                self.intern_tuple(children)
            }
            TypeNode::Callable(body) => {
                let body = body.map(|child| self.remap_binder(*child, depth, mapping, memo));
                self.intern_callable(body.params, body.ret)
            }
            TypeNode::Generic(Generic { parameters, body }) => {
                let body = body.map(|child| self.remap_binder(*child, depth + 1, mapping, memo));
                self.intern_generic(parameters.get(), &body)
            }
            TypeNode::Union(children) => {
                let children = children
                    .into_iter()
                    .map(|child| self.remap_binder(child, depth, mapping, memo))
                    .collect();
                self.intern_union(children)
            }
            TypeNode::Intersection(children) => {
                let children = children
                    .into_iter()
                    .map(|child| self.remap_binder(child, depth, mapping, memo))
                    .collect();
                self.intern_intersection(children)
            }
        };
        memo.insert((type_id, depth), rewritten);
        rewritten
    }

    /// Construct one canonical union from already interned children.
    pub fn intern_union(&mut self, children: Vec<TypeId>) -> TypeId {
        self.intern_junction(Junction::Union, children)
    }

    /// Construct one canonical intersection from already interned children.
    pub fn intern_intersection(&mut self, children: Vec<TypeId>) -> TypeId {
        self.intern_junction(Junction::Intersection, children)
    }

    fn intern_junction(&mut self, junction: Junction, children: Vec<TypeId>) -> TypeId {
        let mut flattened = Vec::new();
        for child in children {
            match (junction, self.store.type_node(child)) {
                (Junction::Union, TypeNode::Union(nested))
                | (Junction::Intersection, TypeNode::Intersection(nested)) => {
                    flattened.extend_from_slice(nested);
                }
                (
                    _,
                    TypeNode::Bound(_)
                    | TypeNode::Class(_)
                    | TypeNode::Flexible(_)
                    | TypeNode::Tuple(_)
                    | TypeNode::Callable(_)
                    | TypeNode::Generic(_)
                    | TypeNode::Union(_)
                    | TypeNode::Intersection(_),
                ) => flattened.push(child),
            }
        }
        let absorbing = self.intern_node(TypeNode::Class(ClassType::plain(junction.absorbing())));
        if flattened.contains(&absorbing) {
            return absorbing;
        }
        let neutral = self.intern_node(TypeNode::Class(ClassType::plain(junction.neutral())));
        flattened.retain(|child| *child != neutral);
        flattened.sort_by(|left, right| compare_types(&self.store, *left, *right));
        flattened.dedup();
        match flattened.as_slice() {
            [] => neutral,
            [only] => *only,
            _ => self.intern_node(match junction {
                Junction::Union => TypeNode::Union(flattened),
                Junction::Intersection => TypeNode::Intersection(flattened),
            }),
        }
    }
}

fn type_rank(node: &TypeNode) -> u8 {
    match node {
        TypeNode::Bound(_) => 0,
        TypeNode::Class(_) => 1,
        TypeNode::Flexible(_) => 2,
        TypeNode::Tuple(_) => 3,
        TypeNode::Callable(..) => 4,
        TypeNode::Generic(..) => 5,
        TypeNode::Union(_) => 6,
        TypeNode::Intersection(_) => 7,
    }
}
