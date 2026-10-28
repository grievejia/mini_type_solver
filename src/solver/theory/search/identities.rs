//! Persistent search identities and scope ancestry.
//!
//! Each site has one identity. Reusing a site preserves its scope and variable kind.

use std::collections::BTreeMap;

use crate::frontend::problem::{AtomId, Callable, Generic, MetaVarId, TypeId, TypeNode, TypeStore};
use crate::indices::checked_u32;

use super::graph::{ChoiceCopy, FactorNode, Graph, SFactor, SValue};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ScopeId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct VarId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RigidId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct SiteId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ChoiceId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct RequirementId(u32);

pub const ROOT_SCOPE: ScopeId = ScopeId(0);

/// Required relation between a converted value and its source.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Direction {
    /// The source is below the converted value.
    Widen,
    /// The converted value is below the source.
    Narrow,
    /// Both subtype relations must hold.
    Exact,
}

impl Direction {
    pub fn reverse(self) -> Self {
        match self {
            Self::Widen => Self::Narrow,
            Self::Narrow => Self::Widen,
            Self::Exact => Self::Exact,
        }
    }
}

/// One step from a subtype obligation into a nested type comparison.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum PathStep {
    UpperArm(usize),
    LowerArm(usize),
    LowerFactor(usize),
    UpperFactor(usize),
    Tuple(usize),
    Parameter(usize),
    Return,
    ClassArgument(usize),
    ClassDirection(ClassDirection),
    GenericBody,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ClassDirection {
    Forward,
    Reverse,
}

/// Ordered comparison steps, independent of source locations and scope ancestry.
pub type TypePath = Vec<PathStep>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum GenericSide {
    Lower,
    Upper,
    Adaptation,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct GenericSite {
    /// Derived comparisons keep the source atom, their type position, and scope.
    pub check: AtomId,
    pub path: TypePath,
    pub side: GenericSide,
    pub scope: ScopeId,
    pub generic: Generic<SValue>,
}

/// Identity of one deferred generic use.
///
/// The owner, comparison, and path distinguish uses with equal generic sources.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ChoiceSite {
    pub owner: VarId,
    pub check: AtomId,
    pub path: TypePath,
    pub source: Generic<SValue>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct RequirementSite {
    pub route: ChoiceCopy,
    pub check: AtomId,
    pub path: TypePath,
    pub upper: SFactor,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum VarSite {
    Declared(MetaVarId),
    StoredInstance {
        copy: ChoiceCopy,
        requirement: RequirementId,
    },
    Selection {
        site: SiteId,
        position: u32,
    },
    Instance {
        choice: ChoiceId,
        requirement: RequirementId,
        position: u32,
    },
    /// A proxy keeps the destination scope, kind, and direction. Reusing it
    /// must retain the source relation for the requesting comparison.
    Proxy {
        source: VarId,
        scope: ScopeId,
        direction: Direction,
        kind: ValueKind,
    },
}

#[derive(Debug, Clone)]
struct Scope {
    parent: Option<ScopeId>,
    depth: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ValueKind {
    General,
    GenericFree,
}

#[derive(Debug, Clone)]
struct Variable {
    scope: ScopeId,
    kind: ValueKind,
}

#[derive(Debug, Clone)]
struct Rigid {
    scope: ScopeId,
    position: u32,
}

/// Stable scope and use identities, shared by every branch of one theory call.
#[derive(Debug)]
pub struct Identities {
    source_values: BTreeMap<TypeId, SValue>,
    scopes: Vec<Scope>,
    scope_ids: BTreeMap<SiteId, ScopeId>,
    variables: Vec<Variable>,
    variable_ids: BTreeMap<VarSite, VarId>,
    rigids: Vec<Rigid>,
    rigid_ids: BTreeMap<(SiteId, u32), RigidId>,
    generic_sites: Vec<GenericSite>,
    generic_site_ids: BTreeMap<GenericSite, SiteId>,
    choice_site_ids: BTreeMap<ChoiceSite, ChoiceId>,
    requirement_site_ids: BTreeMap<RequirementSite, RequirementId>,
}

impl Identities {
    /// Create persistent identity tables for one theory call.
    ///
    /// Identity entries survive branch rollback, so deferred identity map lengths
    /// remain valid for allocating new identifiers throughout the theory call.
    /// Each use also checks its branch record in [`State`](super::range::State).
    /// A deferred route's branch record owns both its instances and its readers.
    /// Reapplying an update reuses identifiers and recreates all branch data.
    pub fn new() -> Self {
        Self {
            source_values: BTreeMap::new(),
            scopes: vec![Scope {
                parent: None,
                depth: 0,
            }],
            scope_ids: BTreeMap::new(),
            variables: Vec::new(),
            variable_ids: BTreeMap::new(),
            rigids: Vec::new(),
            rigid_ids: BTreeMap::new(),
            generic_sites: Vec::new(),
            generic_site_ids: BTreeMap::new(),
            choice_site_ids: BTreeMap::new(),
            requirement_site_ids: BTreeMap::new(),
        }
    }

    pub fn generic_site(&mut self, site: GenericSite) -> SiteId {
        if let Some(id) = self.generic_site_ids.get(&site) {
            return *id;
        }
        let id = SiteId(checked_u32(self.generic_sites.len(), "generic site count"));
        self.generic_site_ids.insert(site.clone(), id);
        self.generic_sites.push(site);
        id
    }

    pub fn generic(&self, id: SiteId) -> &GenericSite {
        &self.generic_sites[id.0 as usize]
    }

    pub fn choice(&mut self, site: ChoiceSite) -> ChoiceId {
        if let Some(id) = self.choice_site_ids.get(&site) {
            return *id;
        }
        let id = ChoiceId(checked_u32(
            self.choice_site_ids.len(),
            "deferred choice count",
        ));
        self.choice_site_ids.insert(site, id);
        id
    }

    pub fn requirement(&mut self, site: RequirementSite) -> RequirementId {
        if let Some(id) = self.requirement_site_ids.get(&site) {
            return *id;
        }
        let id = RequirementId(checked_u32(
            self.requirement_site_ids.len(),
            "upper requirement count",
        ));
        self.requirement_site_ids.insert(site, id);
        id
    }

    /// Reuse a generic site's child scope, preserving its parent.
    ///
    /// Generic sites include their side, so conversion and comparison sites differ.
    pub fn child_scope(&mut self, site: SiteId, parent: ScopeId) -> ScopeId {
        if let Some(id) = self.scope_ids.get(&site) {
            let scope = &self.scopes[id.0 as usize];
            assert_eq!(
                scope.parent,
                Some(parent),
                "stable scope site changed its parent"
            );
            return *id;
        }
        let depth = self.scopes[parent.0 as usize].depth + 1;
        let id = ScopeId(checked_u32(self.scopes.len(), "scope count"));
        self.scope_ids.insert(site, id);
        self.scopes.push(Scope {
            parent: Some(parent),
            depth,
        });
        id
    }

    /// Reuse a variable identity or register it with the site's value kind.
    ///
    /// The site fixes value kind. Reusing an identity must preserve its scope.
    pub fn variable(&mut self, site: VarSite, scope: ScopeId) -> VarId {
        if let Some(id) = self.variable_ids.get(&site) {
            let variable = &self.variables[id.0 as usize];
            assert_eq!(variable.scope, scope, "stable variable site changed scope");
            return *id;
        }
        let kind = match &site {
            VarSite::Declared(_) => ValueKind::General,
            VarSite::Selection { .. }
            | VarSite::Instance { .. }
            | VarSite::StoredInstance { .. } => ValueKind::GenericFree,
            VarSite::Proxy { kind, .. } => *kind,
        };
        let id = VarId(checked_u32(self.variables.len(), "scoped variable count"));
        self.variable_ids.insert(site, id);
        self.variables.push(Variable { scope, kind });
        id
    }

    pub fn declared(&mut self, id: MetaVarId) -> VarId {
        self.variable(VarSite::Declared(id), ROOT_SCOPE)
    }

    pub fn rigid(&mut self, site: SiteId, position: u32, scope: ScopeId) -> RigidId {
        if let Some(id) = self.rigid_ids.get(&(site, position)) {
            assert_eq!(
                self.rigid_scope(*id),
                scope,
                "stable rigid site changed scope"
            );
            return *id;
        }
        let id = RigidId(checked_u32(self.rigids.len(), "rigid type count"));
        self.rigids.push(Rigid { scope, position });
        self.rigid_ids.insert((site, position), id);
        id
    }

    /// Read the depth fixed when the scope was allocated.
    pub fn scope_depth(&self, scope: ScopeId) -> u32 {
        self.scopes[scope.0 as usize].depth
    }

    /// Return the scopes from the root to this scope, without the root itself.
    pub fn scope_chain(&self, mut scope: ScopeId) -> Vec<ScopeId> {
        let mut chain = Vec::new();
        while let Some(parent) = self.scopes[scope.0 as usize].parent {
            chain.push(scope);
            scope = parent;
        }
        chain.reverse();
        chain
    }

    pub fn rigid_position(&self, id: RigidId) -> u32 {
        self.rigids[id.0 as usize].position
    }

    pub fn variable_scope(&self, id: VarId) -> ScopeId {
        self.variables[id.0 as usize].scope
    }

    pub fn variable_kind(&self, id: VarId) -> ValueKind {
        self.variables[id.0 as usize].kind
    }

    pub fn rigid_scope(&self, id: RigidId) -> ScopeId {
        self.rigids[id.0 as usize].scope
    }

    pub fn is_ancestor(&self, ancestor: ScopeId, mut scope: ScopeId) -> bool {
        loop {
            if ancestor == scope {
                return true;
            }
            let Some(parent) = self.scopes[scope.0 as usize].parent else {
                return false;
            };
            scope = parent;
        }
    }

    pub fn youngest(&self, left: ScopeId, right: ScopeId) -> ScopeId {
        if self.is_ancestor(left, right) {
            right
        } else if self.is_ancestor(right, left) {
            left
        } else {
            panic!("comparison endpoints are in incomparable scopes: {left:?}, {right:?}");
        }
    }

    pub fn lowest_common_ancestor(&self, mut left: ScopeId, mut right: ScopeId) -> ScopeId {
        while self.scopes[left.0 as usize].depth > self.scopes[right.0 as usize].depth {
            let Some(parent) = self.scopes[left.0 as usize].parent else {
                panic!("non-root scope has no parent");
            };
            left = parent;
        }
        while self.scopes[right.0 as usize].depth > self.scopes[left.0 as usize].depth {
            let Some(parent) = self.scopes[right.0 as usize].parent else {
                panic!("non-root scope has no parent");
            };
            right = parent;
        }
        while left != right {
            let (Some(left_parent), Some(right_parent)) = (
                self.scopes[left.0 as usize].parent,
                self.scopes[right.0 as usize].parent,
            ) else {
                panic!("scope tree has two roots");
            };
            left = left_parent;
            right = right_parent;
        }
        left
    }
}

/// Convert a frontend node once. Use the graph and identities from the same
/// theory call, and the source types from that call's input.
pub fn source_value(
    graph: &Graph,
    type_id: TypeId,
    types: &TypeStore,
    identities: &mut Identities,
) -> SValue {
    if let Some(value) = identities.source_values.get(&type_id).cloned() {
        return value;
    }
    let value = match types.type_node(type_id) {
        TypeNode::Bound(reference) => graph.factor(FactorNode::Bound(*reference)),
        TypeNode::Class(application) => graph.factor(FactorNode::Class(
            application.map(|argument| source_value(graph, *argument, types, identities)),
        )),
        TypeNode::Flexible(id) => graph.factor(FactorNode::Ref(identities.declared(*id))),
        TypeNode::Tuple(elements) => graph.factor(FactorNode::Tuple(
            elements
                .iter()
                .map(|element| source_value(graph, *element, types, identities))
                .collect(),
        )),
        TypeNode::Callable(Callable { params, ret }) => {
            graph.factor(FactorNode::Callable(Callable {
                params: params
                    .iter()
                    .map(|param| source_value(graph, *param, types, identities))
                    .collect(),
                ret: source_value(graph, *ret, types, identities),
            }))
        }
        TypeNode::Generic(generic) => graph.factor(FactorNode::Generic(Generic {
            parameters: generic.parameters,
            body: generic
                .body
                .map(|child| source_value(graph, *child, types, identities)),
        })),
        TypeNode::Union(children) => graph.union(
            children
                .iter()
                .map(|child| source_value(graph, *child, types, identities)),
        ),
        TypeNode::Intersection(children) => graph.intersection(
            children
                .iter()
                .map(|child| source_value(graph, *child, types, identities)),
        ),
    };
    identities.source_values.insert(type_id, value.clone());
    value
}
