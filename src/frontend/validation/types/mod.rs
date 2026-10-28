//! Canonical semantic type data and its resolution builder.
//!
//! `TypeStore` is immutable after resolution. `TypeBuilder` owns the interning
//! index while constructing it. Children and identifiers belong to one store.

mod normalize;
#[cfg(test)]
mod tests;

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::iter;
use std::num::NonZeroU32;

use super::declarations::{ClassId, Declarations, MetaVarId};
pub use normalize::{BinderReplacement, Junction, live_bound_positions};

use crate::indices::checked_u32;

/// Identifier of one interned semantic type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeId(u32);

/// Canonical reference to one generic callable parameter.
///
/// `binder == 0` names the nearest generic callable. Larger values walk to
/// enclosing generic callables. `position` is the parameter's canonical
/// position within that binder. Structural order puts outer binders first, then
/// uses canonical parameter position.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BoundRef {
    binder: u32,
    position: u32,
}

impl PartialOrd for BoundRef {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BoundRef {
    fn cmp(&self, other: &Self) -> Ordering {
        other
            .binder
            .cmp(&self.binder)
            .then_with(|| self.position.cmp(&other.position))
    }
}

impl BoundRef {
    /// Construct one canonical bound reference.
    #[must_use]
    pub fn new(binder: u32, position: u32) -> Self {
        Self { binder, position }
    }

    /// Relative index of the binder that owns this reference.
    #[must_use]
    pub fn binder(self) -> u32 {
        self.binder
    }

    /// Canonical parameter position within the owning binder.
    #[must_use]
    pub fn position(self) -> u32 {
        self.position
    }
}

/// Class identity and its ordered argument values.
///
/// Stored applications in checked type and hierarchy data have the declared
/// argument count. Source resolution and type construction check that condition.
/// Standalone values are data; mapping preserves their argument count and order.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ClassType<T> {
    pub class: ClassId,
    pub arguments: Vec<T>,
}

impl<T> ClassType<T> {
    /// The built-in top class has no arguments.
    pub const OBJECT: Self = Self::plain(ClassId::OBJECT);

    /// The built-in bottom class has no arguments.
    pub const NEVER: Self = Self::plain(ClassId::NEVER);

    /// Construct a class application without arguments.
    ///
    /// The class must have no declared parameters. Source resolution or
    /// semantic construction checks this requirement.
    #[must_use]
    pub const fn plain(class: ClassId) -> Self {
        Self {
            class,
            arguments: Vec::new(),
        }
    }

    /// Preserve declared arity while changing the argument representation.
    pub fn map<U>(&self, map: impl FnMut(&T) -> U) -> ClassType<U> {
        ClassType {
            class: self.class,
            arguments: self.arguments.iter().map(map).collect(),
        }
    }
}

/// Fixed positional parameters and one return type.
///
/// Mapping children preserves callable arity and their order.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Callable<T> {
    pub params: Vec<T>,
    pub ret: T,
}

impl<T> Callable<T> {
    /// Visit parameters from left to right, then the return value.
    pub fn children(&self) -> impl Iterator<Item = &T> {
        self.params.iter().chain(iter::once(&self.ret))
    }

    /// Preserve arity and child order while changing the child representation.
    ///
    /// Parameters are mapped from left to right, then the return value. This
    /// order keeps source resolution and search reconstruction deterministic.
    pub fn map<U>(&self, mut map: impl FnMut(&T) -> U) -> Callable<U> {
        let params = self.params.iter().map(&mut map).collect();
        let ret = map(&self.ret);
        Callable { params, ret }
    }
}

/// Retained generic binder with one complete callable body.
///
/// The parameter count is nonzero. Normalization removes the binder when no
/// parameter remains live.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Generic<T> {
    pub parameters: NonZeroU32,
    pub body: Callable<T>,
}

/// One interned semantic type.
///
/// Children are canonical `TypeId` values. Union and intersection members
/// follow stable structural order. Class arguments keep declaration order.
/// Class parameter references belong only to templates, never to these nodes.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeNode {
    Bound(BoundRef),
    Class(ClassType<TypeId>),
    Flexible(MetaVarId),
    Tuple(Vec<TypeId>),
    Callable(Callable<TypeId>),
    Generic(Generic<TypeId>),
    Union(Vec<TypeId>),
    Intersection(Vec<TypeId>),
}

impl TypeId {
    /// Array index for the interned type table.
    fn index(self) -> usize {
        self.0 as usize
    }
}

/// Canonical type nodes for one resolved problem.
#[derive(Debug, Clone)]
pub struct TypeStore {
    nodes: Vec<TypeNode>,
    metavars: Vec<TypeId>,
}

impl TypeStore {
    /// Read a canonical node from this store.
    #[must_use]
    pub fn type_node(&self, id: TypeId) -> &TypeNode {
        &self.nodes[id.index()]
    }

    /// Find an already canonical node without changing this store.
    #[cfg(test)]
    #[must_use]
    pub fn find_type(&self, node: &TypeNode) -> Option<TypeId> {
        self.nodes
            .iter()
            .position(|candidate| candidate == node)
            .map(|index| TypeId(checked_u32(index, "type count")))
    }

    /// Read the canonical flexible type of a declared metavariable.
    #[must_use]
    pub fn metavar_type(&self, id: MetaVarId) -> TypeId {
        self.metavars[id.index()]
    }

    /// Add every metavariable reachable from one canonical type node.
    /// Shared descendants are read once per call.
    pub fn collect_metavars(&self, type_id: TypeId, metavars: &mut BTreeSet<MetaVarId>) {
        let mut pending = vec![type_id];
        let mut seen = BTreeSet::new();
        while let Some(id) = pending.pop() {
            if !seen.insert(id) {
                continue;
            }
            match self.type_node(id) {
                TypeNode::Bound(_) => {}
                TypeNode::Flexible(id) => {
                    metavars.insert(*id);
                }
                TypeNode::Class(application) => pending.extend(&application.arguments),
                TypeNode::Tuple(children)
                | TypeNode::Union(children)
                | TypeNode::Intersection(children) => pending.extend(children),
                TypeNode::Callable(body) | TypeNode::Generic(Generic { body, .. }) => {
                    pending.extend(body.children());
                }
            }
        }
    }
}

/// Local type construction during reference resolution.
#[derive(Debug)]
pub struct TypeBuilder {
    store: TypeStore,
    ids: BTreeMap<TypeNode, TypeId>,
    // Collection completes the class schema before this builder exists.
    // Metavariable additions in raw fixtures do not change class arities.
    class_arities: Box<[usize]>,
}

impl TypeBuilder {
    /// Construct the initial types after declaration collection completes.
    #[must_use]
    pub fn new(declarations: &Declarations) -> Self {
        let mut builder = Self {
            store: TypeStore {
                nodes: Vec::new(),
                metavars: Vec::new(),
            },
            ids: BTreeMap::new(),
            class_arities: declarations
                .classes()
                .map(|(id, _)| declarations.class_arity(id))
                .collect(),
        };
        for (id, _) in declarations.classes() {
            if declarations.class_arity(id) == 0 {
                builder.intern_class(id, Vec::new());
            }
        }
        for (id, _) in declarations.metavars() {
            let ty = builder.intern_node(TypeNode::Flexible(id));
            builder.store.metavars.push(ty);
        }
        builder
    }

    /// Read the types already constructed.
    #[must_use]
    pub fn types(&self) -> &TypeStore {
        &self.store
    }

    /// Complete resolution and discard the construction index.
    #[must_use]
    pub fn finish(self) -> TypeStore {
        self.store
    }

    #[cfg(test)]
    #[must_use]
    pub fn from_store(store: TypeStore, declarations: &Declarations) -> Self {
        let ids = store
            .nodes
            .iter()
            .enumerate()
            .map(|(index, node)| (node.clone(), TypeId(checked_u32(index, "type count"))))
            .collect();
        let class_arities = declarations
            .classes()
            .map(|(id, _)| declarations.class_arity(id))
            .collect();
        Self {
            store,
            ids,
            class_arities,
        }
    }

    /// Extend a raw fixture's flexible-type table in declaration order.
    ///
    /// # Panics
    ///
    /// Panics if the fixture's declaration and type tables disagree.
    #[cfg(test)]
    pub fn add_metavar(&mut self, id: MetaVarId) {
        assert_eq!(
            id.index(),
            self.store.metavars.len(),
            "fixture metavariable tables disagree"
        );
        let ty = self.intern_node(TypeNode::Flexible(id));
        self.store.metavars.push(ty);
    }

    /// Intern one semantic type node.
    #[cfg(test)]
    pub fn intern_type(&mut self, node: TypeNode) -> TypeId {
        match node {
            TypeNode::Class(application) => {
                self.intern_class(application.class, application.arguments)
            }
            TypeNode::Tuple(elements) => self.intern_tuple(elements),
            TypeNode::Callable(Callable { params, ret }) => self.intern_callable(params, ret),
            TypeNode::Generic(Generic { parameters, body }) => {
                self.intern_generic(parameters.get(), &body)
            }
            TypeNode::Union(children) => self.intern_union(children),
            TypeNode::Intersection(children) => self.intern_intersection(children),
            leaf @ (TypeNode::Bound(_) | TypeNode::Flexible(_)) => self.intern_node(leaf),
        }
    }

    /// Intern one class application with its declared number of arguments.
    ///
    /// Source resolution reports arity errors before this call. Rewrites keep
    /// complete argument values and their order.
    ///
    /// # Panics
    ///
    /// Panics when a caller supplies the wrong number of arguments.
    pub fn intern_class(&mut self, class: ClassId, arguments: Vec<TypeId>) -> TypeId {
        let expected = self.class_arities[class.index()];
        assert_eq!(
            arguments.len(),
            expected,
            "invalid class application arity for {class:?}: expected {expected}, got {}",
            arguments.len()
        );
        self.intern_node(TypeNode::Class(ClassType { class, arguments }))
    }

    /// Intern one tuple without changing its element types or order.
    pub fn intern_tuple(&mut self, elements: Vec<TypeId>) -> TypeId {
        self.intern_node(TypeNode::Tuple(elements))
    }

    /// Intern one callable without changing its parameter or return types.
    pub fn intern_callable(&mut self, params: Vec<TypeId>, ret: TypeId) -> TypeId {
        self.intern_node(TypeNode::Callable(Callable { params, ret }))
    }

    /// Intern one canonical bound reference.
    pub fn intern_bound(&mut self, reference: BoundRef) -> TypeId {
        self.intern_node(TypeNode::Bound(reference))
    }

    /// Intern one already canonical semantic node.
    fn intern_node(&mut self, node: TypeNode) -> TypeId {
        if let Some(id) = self.ids.get(&node) {
            return *id;
        }
        let id = TypeId(checked_u32(self.store.nodes.len(), "type count"));
        self.ids.insert(node.clone(), id);
        self.store.nodes.push(node);
        id
    }
}
