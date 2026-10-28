//! Own closed type definitions and the bindings saved with each occurrence.
//!
//! A reference returns to its definition's saved bindings. It does not add a
//! binder frame. Only checked definitions can leave this module.

mod compare;
mod normalize;
#[cfg(test)]
mod tests;

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

#[cfg(test)]
use crate::frontend::problem::BoundRef;
use crate::frontend::problem::{Callable, ClassId, ClassType, Declarations, TemplateType};
use crate::indices::checked_u32;
use crate::solver::reachability;

use super::search::graph::{FactorNode, SArm, SFactor, SValue};
use super::search::identities::{Identities, RigidId, ScopeId, VarId};
pub use compare::is_subtype;
pub use normalize::subtype::{Normalization, normalize as normalize_finite};
use normalize::{Key, Keys, normalize, normalize_scoped};

#[derive(Debug, Clone)]
enum Type {
    Never,
    Arbitrary {
        owner: usize,
        position: u32,
        identity: RigidId,
    },
    Class(ClassType<usize>),
    Tuple(Vec<usize>),
    Callable(Callable<usize>),
    Generic {
        // Copies retain this owner while parameter positions stay fixed.
        // It is not a type child or a
        // part of the structural key for a closed type.
        binding: Rc<()>,
        parameters: u32,
        body: Callable<usize>,
    },
    Bound {
        owner: usize,
        position: u32,
    },
    Reference(usize),
    Union(Vec<usize>),
    Intersection(Vec<usize>),
}

impl Type {
    fn children(&self) -> Vec<usize> {
        match self {
            Self::Never | Self::Arbitrary { .. } | Self::Bound { .. } => Vec::new(),
            Self::Class(class) => class.arguments.clone(),
            Self::Tuple(children) | Self::Union(children) | Self::Intersection(children) => {
                children.clone()
            }
            Self::Callable(body) | Self::Generic { body, .. } => body.children().copied().collect(),
            Self::Reference(target) => vec![*target],
        }
    }

    fn is_constructor(&self) -> bool {
        matches!(
            self,
            Self::Class(_) | Self::Tuple(_) | Self::Callable(_) | Self::Generic { .. }
        )
    }

    fn map_children(&self, mut map: impl FnMut(usize) -> usize) -> Self {
        match self {
            Self::Never => Self::Never,
            Self::Arbitrary {
                owner,
                position,
                identity,
            } => Self::Arbitrary {
                owner: *owner,
                position: *position,
                identity: *identity,
            },
            Self::Class(class) => Self::Class(class.map(|child| map(*child))),
            Self::Tuple(children) => Self::Tuple(children.iter().copied().map(map).collect()),
            Self::Callable(body) => Self::Callable(body.map(|child| map(*child))),
            Self::Generic {
                binding,
                parameters,
                body,
            } => Self::Generic {
                binding: Rc::clone(binding),
                parameters: *parameters,
                body: body.map(|child| map(*child)),
            },
            Self::Bound { owner, position } => Self::Bound {
                owner: *owner,
                position: *position,
            },
            Self::Reference(target) => Self::Reference(map(*target)),
            Self::Union(children) => Self::Union(children.iter().copied().map(map).collect()),
            Self::Intersection(children) => {
                Self::Intersection(children.iter().copied().map(map).collect())
            }
        }
    }
}

#[derive(Debug, Clone)]
struct Node {
    kind: Type,
    scope: Vec<usize>,
}

#[derive(Debug, Clone)]
struct Definition {
    nodes: Vec<Node>,
    root: usize,
    keys: Vec<Key>,
    // These identities distinguish open values from different binders.
    // Closed values have an empty set and use only their structural key.
    free_bindings: Vec<BTreeSet<usize>>,
}

/// One immutable owner for checked type definitions in a result.
#[derive(Debug)]
pub struct ClosedGraph {
    definitions: Vec<Definition>,
    canonical: BTreeMap<(usize, usize), (usize, usize)>,
    names: BTreeMap<ClassId, String>,
}

/// A checked value. Child queries keep the same graph owner.
#[derive(Debug, Clone)]
pub struct Value {
    graph: Rc<ClosedGraph>,
    definition: usize,
    node: usize,
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Value {}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Value {
    fn cmp(&self, other: &Self) -> Ordering {
        self.key().cmp(other.key()).then_with(|| {
            self.definition().free_bindings[self.node]
                .cmp(&other.definition().free_bindings[other.node])
        })
    }
}

/// A type query copies child handles, never the type definitions they refer to.
#[derive(Debug)]
pub enum ValueNode {
    Never,
    Arbitrary,
    Class {
        name: String,
        class: ClassId,
        arguments: Vec<Value>,
    },
    Tuple(Vec<Value>),
    Callable(Callable<Value>),
    /// A Bound descendant owned by this binder names this generic value itself
    /// as its owner. References to other binders retain their own owners.
    Generic {
        parameters: u32,
        body: Callable<Value>,
    },
    Bound {
        owner: Value,
        position: u32,
        #[cfg(test)]
        coordinate: BoundRef,
    },
    Union(Vec<Value>),
    Intersection(Vec<Value>),
}

impl Value {
    pub fn is_generic_free(&self) -> bool {
        reachable(&self.definition().nodes, self.node)
            .iter()
            .all(|id| !matches!(self.definition().nodes[*id].kind, Type::Generic { .. }))
    }

    /// Class names reachable from this value, including constructor arguments.
    pub fn classes(&self) -> impl Iterator<Item = ClassId> + '_ {
        reachable(&self.definition().nodes, self.node)
            .into_iter()
            .filter_map(|id| match &self.definition().nodes[id].kind {
                Type::Class(class) => Some(class.class),
                _ => None,
            })
    }

    /// Identify the shared node that child queries return for this occurrence.
    pub fn occurrence(&self) -> Self {
        self.child(self.node)
    }

    /// Node identity includes its graph owner and the shared canonical location.
    pub fn same_occurrence(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.graph, &other.graph)
            && self.location(self.node) == other.location(other.node)
    }

    /// Hash the same graph owner and shared location as [`Self::same_occurrence`].
    pub fn hash_occurrence<H: Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.graph).hash(state);
        self.location(self.node).hash(state);
    }

    /// An open value keeps every saved outer owner, including unused owners.
    /// A closed value has no required outer scope. A generic excludes its own owner.
    pub fn binding_scope(&self) -> Vec<Self> {
        let definition = self.definition();
        if definition.free_bindings[self.node].is_empty() {
            return Vec::new();
        }
        definition.nodes[self.node]
            .scope
            .iter()
            .map(|owner| Self {
                graph: Rc::clone(&self.graph),
                definition: self.definition,
                node: *owner,
            })
            .collect()
    }
    /// Copies of one binder keep the same owner. Parameter names do not
    /// establish ownership, and closed type equality does not establish it.
    pub fn same_binding(&self, other: &Self) -> bool {
        match (
            &self.definition().nodes[self.node].kind,
            &other.definition().nodes[other.node].kind,
        ) {
            (Type::Generic { binding: lower, .. }, Type::Generic { binding: upper, .. }) => {
                Rc::ptr_eq(lower, upper)
            }
            _ => false,
        }
    }

    fn definition(&self) -> &Definition {
        &self.graph.definitions[self.definition]
    }

    fn key(&self) -> &Key {
        &self.definition().keys[self.node]
    }

    fn location(&self, node: usize) -> (usize, usize) {
        self.graph
            .canonical
            .get(&(self.definition, node))
            .copied()
            .unwrap_or((self.definition, node))
    }

    fn child(&self, node: usize) -> Self {
        let (definition, node) = self.location(node);
        Self {
            graph: Rc::clone(&self.graph),
            definition,
            node,
        }
    }

    /// Whether child queries return to this same checked value.
    #[cfg(test)]
    pub fn is_recursive(&self) -> bool {
        self.is_recursive_without([])
    }

    pub fn contains_recursion(&self) -> bool {
        matches!(self.key(), Key::Recursive(_))
    }

    /// A new name is needed when a path returns here without reaching a value
    /// that already has a name. Named values stop that path as references.
    pub fn is_recursive_without<'a>(&self, named: impl IntoIterator<Item = &'a Self>) -> bool {
        let named = named.into_iter().cloned().collect::<BTreeSet<_>>();
        let definition = self.definition();
        if named.contains(self) {
            return false;
        }
        let mut pending = definition.nodes[self.node].kind.children();
        let mut seen = BTreeSet::new();
        while let Some(node) = pending.pop() {
            let value = self.child(node);
            if named.contains(&value) {
                continue;
            }
            if value == *self {
                return true;
            }
            if seen.insert(node) {
                pending.extend(definition.nodes[node].kind.children());
            }
        }
        false
    }

    /// Read the complete type at this value position.
    pub fn node(&self) -> ValueNode {
        let node = &self.definition().nodes[self.node];
        match &node.kind {
            Type::Never => ValueNode::Never,
            Type::Arbitrary { .. } => ValueNode::Arbitrary,
            Type::Class(class) => ValueNode::Class {
                name: self.graph.names[&class.class].clone(),
                class: class.class,
                arguments: class
                    .arguments
                    .iter()
                    .map(|child| self.child(*child))
                    .collect(),
            },
            Type::Tuple(children) => {
                ValueNode::Tuple(children.iter().map(|child| self.child(*child)).collect())
            }
            Type::Callable(body) => ValueNode::Callable(body.map(|child| self.child(*child))),
            Type::Generic {
                parameters, body, ..
            } => ValueNode::Generic {
                parameters: *parameters,
                body: body.map(|child| self.child(*child)),
            },
            Type::Bound { owner, position } => ValueNode::Bound {
                owner: Self {
                    graph: Rc::clone(&self.graph),
                    definition: self.definition,
                    node: *owner,
                },
                position: *position,
                #[cfg(test)]
                coordinate: {
                    let depth = node
                        .scope
                        .iter()
                        .rev()
                        .position(|binder| binder == owner)
                        .expect("a checked parameter has a binder");
                    BoundRef::new(checked_u32(depth, "binding depth"), *position)
                },
            },
            Type::Union(children) => {
                ValueNode::Union(children.iter().map(|child| self.child(*child)).collect())
            }
            Type::Intersection(children) => {
                ValueNode::Intersection(children.iter().map(|child| self.child(*child)).collect())
            }
            Type::Reference(_) => panic!("reference wrapper survived closed graph normalization"),
        }
    }

    /// Class names also reserve names used for printed binders.
    pub fn has_class_name(&self, name: &str) -> bool {
        self.graph.names.values().any(|class| class == name)
    }
}

/// Construction stays local until references, bindings, and cycles are checked.
#[derive(Debug)]
pub struct Builder {
    nodes: Vec<Node>,
    names: BTreeMap<ClassId, String>,
    variables: BTreeMap<VarId, usize>,
    scope_owners: BTreeMap<ScopeId, usize>,
    variable_scopes: BTreeMap<VarId, Vec<usize>>,
    rigids: BTreeMap<RigidId, (usize, u32)>,
    values: BTreeMap<(SValue, Vec<usize>), usize>,
    factors: BTreeMap<(SFactor, Vec<usize>), usize>,
    included: BTreeMap<(usize, usize), usize>,
    pending: Vec<Import>,
}

#[derive(Debug)]
enum Import {
    Value(usize, SValue, Vec<usize>),
    Factor(usize, SFactor, Vec<usize>),
}

impl Builder {
    pub fn new(declarations: &Declarations) -> Self {
        let names = declarations
            .classes()
            .map(|(id, class)| (id, class.name().to_owned()))
            .collect();
        Self {
            nodes: Vec::new(),
            names,
            variables: BTreeMap::new(),
            scope_owners: BTreeMap::new(),
            variable_scopes: BTreeMap::new(),
            rigids: BTreeMap::new(),
            values: BTreeMap::new(),
            factors: BTreeMap::new(),
            included: BTreeMap::new(),
            pending: Vec::new(),
        }
    }

    fn add(&mut self, kind: Type, scope: Vec<usize>) -> usize {
        let id = self.nodes.len();
        self.nodes.push(Node { kind, scope });
        id
    }

    /// Register all equation targets before reading their constructor children.
    pub fn equations(&mut self, equations: &BTreeMap<VarId, SValue>) {
        for variable in equations.keys() {
            let scope = self
                .variable_scopes
                .get(variable)
                .cloned()
                .unwrap_or_default();
            let id = self.add(Type::Never, scope);
            assert!(
                self.variables.insert(*variable, id).is_none(),
                "equation registered twice"
            );
        }
        for (variable, value) in equations {
            let scope = self
                .variable_scopes
                .get(variable)
                .cloned()
                .unwrap_or_default();
            let target = self.import_value(value, &scope);
            self.nodes[self.variables[variable]].kind = Type::Reference(target);
        }
    }

    pub fn assigned_equations(&mut self, assignments: &BTreeMap<VarId, Value>) {
        for (variable, value) in assignments {
            let root = self.include(value);
            assert!(
                self.variables.insert(*variable, root).is_none(),
                "an assignment target is registered once"
            );
        }
    }

    /// Keep arbitrary parameter owners separate from the generics in source
    /// types. Internal checks can read these scopes; public roots remain closed.
    /// The list contains all parent introductions. The root has no introduction.
    /// Parents are installed before their children, regardless of the input order.
    pub fn scopes(
        &mut self,
        introductions: &[(ScopeId, Vec<RigidId>)],
        variables: impl Iterator<Item = VarId>,
        identities: &Identities,
    ) {
        let mut introductions = introductions.iter().collect::<Vec<_>>();
        introductions.sort_by_key(|(scope, _)| identities.scope_depth(*scope));
        for (scope, rigids) in introductions {
            if self.scope_owners.contains_key(scope) {
                continue;
            }
            let chain = identities.scope_chain(*scope);
            let outer = chain[..chain.len() - 1]
                .iter()
                .map(|scope| self.scope_owners[scope])
                .collect::<Vec<_>>();
            let never = self.add(Type::Never, outer.clone());
            let owner = self.add(
                Type::Generic {
                    binding: Rc::new(()),
                    parameters: checked_u32(rigids.len(), "arbitrary parameter count"),
                    body: Callable {
                        params: Vec::new(),
                        ret: never,
                    },
                },
                outer,
            );
            self.scope_owners.insert(*scope, owner);
            for rigid in rigids {
                self.rigids
                    .insert(*rigid, (owner, identities.rigid_position(*rigid)));
            }
        }
        for variable in variables {
            let scope = identities
                .scope_chain(identities.variable_scope(variable))
                .iter()
                .map(|scope| self.scope_owners[scope])
                .collect();
            self.variable_scopes.insert(variable, scope);
        }
    }

    pub fn scoped_root(
        &mut self,
        value: &SValue,
        scope: ScopeId,
        identities: &Identities,
    ) -> usize {
        let scope = identities
            .scope_chain(scope)
            .iter()
            .map(|scope| self.scope_owners[scope])
            .collect::<Vec<_>>();
        self.import_value(value, &scope)
    }

    fn import_value(&mut self, value: &SValue, scope: &[usize]) -> usize {
        let key = (value.clone(), scope.to_vec());
        if let Some(id) = self.values.get(&key) {
            return *id;
        }
        let id = self.add(Type::Never, scope.to_vec());
        self.values.insert(key, id);
        self.pending
            .push(Import::Value(id, value.clone(), scope.to_vec()));
        id
    }

    fn import_factor(&mut self, factor: &SFactor, scope: &[usize]) -> usize {
        let key = (factor.clone(), scope.to_vec());
        if let Some(id) = self.factors.get(&key) {
            return *id;
        }
        let id = self.add(Type::Never, scope.to_vec());
        self.factors.insert(key, id);
        self.pending
            .push(Import::Factor(id, factor.clone(), scope.to_vec()));
        id
    }

    /// Copy one definition table once. Recursive children remain table indices.
    pub fn include(&mut self, value: &Value) -> usize {
        assert_eq!(
            self.names, value.graph.names,
            "a value must use the same class declarations"
        );
        let key = (Rc::as_ptr(&value.graph) as usize, value.definition);
        let offset = if let Some(offset) = self.included.get(&key) {
            *offset
        } else {
            let offset = self.nodes.len();
            let source = &value.definition().nodes;
            let mut owners = BTreeMap::new();
            for node in source {
                if let Type::Arbitrary {
                    owner, identity, ..
                } = node.kind
                    && let Some((target, _)) = self.rigids.get(&identity)
                {
                    owners.insert(owner, *target);
                    for (old, new) in source[owner].scope.iter().zip(&self.nodes[*target].scope) {
                        owners.insert(*old, *new);
                    }
                }
            }
            let owner = |id: usize| owners.get(&id).copied().unwrap_or(id + offset);
            self.nodes.extend(source.iter().map(|node| {
                let mut kind = node.kind.map_children(|child| child + offset);
                if let Type::Bound { owner: id, .. } | Type::Arbitrary { owner: id, .. } = &mut kind
                {
                    *id = owner(*id);
                }
                Node {
                    kind,
                    scope: node.scope.iter().map(|id| owner(*id)).collect(),
                }
            }));
            self.included.insert(key, offset);
            offset
        };
        offset + value.node
    }

    /// Substitute a checked superclass template in the source class's saved scope.
    ///
    /// Include the complete source class occurrence and use that node's saved
    /// scope for new template nodes. An argument's scope is not enough: a closed
    /// first argument can have an empty scope while a later argument refers to
    /// a binder.
    /// Reuse actual argument nodes so their parameter owners stay unchanged.
    ///
    /// # Panics
    ///
    /// Panics if `source` is not a class, or a template parameter belongs to
    /// another class or has no actual argument.
    pub fn ancestor(&mut self, source: &Value, template: &ClassType<TemplateType>) -> usize {
        let source = self.include(source);
        let Type::Class(class) = &self.nodes[source].kind else {
            panic!("superclass substitution requires a source class occurrence");
        };
        let source_class = class.class;
        let arguments = class.arguments.clone();
        let scope = self.nodes[source].scope.clone();
        let mut results = Vec::new();
        for template in &template.arguments {
            let mut stack = vec![(template, false)];
            let mut values = Vec::new();
            while let Some((template, finished)) = stack.pop() {
                let children = match template {
                    TemplateType::Parameter { reference } => {
                        assert_eq!(
                            reference.owner, source_class,
                            "a superclass template parameter must belong to the source class"
                        );
                        let Some(argument) = arguments.get(reference.position as usize) else {
                            panic!("a superclass template parameter has no actual argument");
                        };
                        values.push(*argument);
                        continue;
                    }
                    TemplateType::Class(class) => class.arguments.iter().collect::<Vec<_>>(),
                    TemplateType::Tuple(children)
                    | TemplateType::Union(children)
                    | TemplateType::Intersection(children) => children.iter().collect(),
                    TemplateType::Callable { params, ret } => {
                        params.iter().chain([ret.as_ref()]).collect()
                    }
                };
                if !finished {
                    stack.push((template, true));
                    stack.extend(children.into_iter().rev().map(|child| (child, false)));
                    continue;
                }
                let children = values.split_off(values.len() - children.len());
                let kind = match template {
                    TemplateType::Class(class) => Type::Class(ClassType {
                        class: class.class,
                        arguments: children,
                    }),
                    TemplateType::Tuple(_) => Type::Tuple(children),
                    TemplateType::Union(_) => Type::Union(children),
                    TemplateType::Intersection(_) => Type::Intersection(children),
                    TemplateType::Callable { .. } => {
                        let mut children = children;
                        let Some(ret) = children.pop() else {
                            panic!("a function template has a return type");
                        };
                        Type::Callable(Callable {
                            params: children,
                            ret,
                        })
                    }
                    TemplateType::Parameter { .. } => {
                        panic!("a parameter template was already substituted")
                    }
                };
                values.push(self.add(kind, scope.clone()));
            }
            results.extend(values);
        }
        self.add(
            Type::Class(ClassType {
                class: template.class,
                arguments: results,
            }),
            scope,
        )
    }

    fn import_arm(&mut self, arm: &SArm, scope: &[usize]) -> usize {
        let children = arm
            .factors()
            .iter()
            .map(|factor| self.import_factor(factor, scope))
            .collect();
        self.add(Type::Intersection(children), scope.to_vec())
    }

    fn fill_factor(&mut self, id: usize, factor: &SFactor, scope: &[usize]) -> Type {
        match factor.node() {
            FactorNode::Class(class) => {
                Type::Class(class.map(|child| self.import_value(child, scope)))
            }
            FactorNode::Tuple(children) => Type::Tuple(
                children
                    .iter()
                    .map(|child| self.import_value(child, scope))
                    .collect(),
            ),
            FactorNode::Callable(body) => {
                Type::Callable(body.map(|child| self.import_value(child, scope)))
            }
            FactorNode::Generic(generic) => {
                let mut inner = scope.to_vec();
                inner.push(id);
                Type::Generic {
                    binding: Rc::new(()),
                    parameters: generic.parameters.get(),
                    body: generic.body.map(|child| self.import_value(child, &inner)),
                }
            }
            FactorNode::Bound(reference) => {
                let Some(owner) = scope.iter().rev().nth(reference.binder() as usize) else {
                    panic!("closed parameter has no enclosing binder");
                };
                Type::Bound {
                    owner: *owner,
                    position: reference.position(),
                }
            }
            FactorNode::Ref(variable) => Type::Reference(self.variables[variable]),
            FactorNode::Rigid(rigid) => {
                let (owner, position) = self.rigids[rigid];
                Type::Arbitrary {
                    owner,
                    position,
                    identity: *rigid,
                }
            }
            FactorNode::Choice(_) => {
                panic!("open search factor reached closed graph construction");
            }
        }
    }

    fn fill(&mut self) {
        while let Some(task) = self.pending.pop() {
            match task {
                Import::Value(id, value, scope) => {
                    let children = value
                        .arms()
                        .iter()
                        .map(|arm| self.import_arm(arm, &scope))
                        .collect();
                    self.nodes[id].kind = Type::Union(children);
                }
                Import::Factor(id, factor, scope) => {
                    self.nodes[id].kind = self.fill_factor(id, &factor, &scope);
                }
            }
        }
    }

    /// Validate each root in its saved scope, then normalize its reachable graph.
    /// Public roots have an empty scope. Open internal roots retain their owners.
    /// Imported class arguments have already been checked by their construction.
    ///
    /// # Panics
    ///
    /// Panics on missing nodes, invalid bindings or scopes, and unguarded cycles.
    pub fn finish(mut self, roots: &[usize]) -> Vec<Value> {
        self.fill();
        validate(&self.nodes, roots);
        let (definitions, locations) = self.normalize_roots(roots);
        let mut canonical = BTreeMap::new();
        let mut keys = BTreeMap::new();
        for (index, definition) in definitions.iter().enumerate() {
            let free = free_parameters(&definition.nodes);
            for (node, key) in definition.keys.iter().enumerate() {
                if free[node].is_empty() {
                    let location = *keys.entry(key.clone()).or_insert((index, node));
                    canonical.insert((index, node), location);
                }
            }
        }
        let graph = Rc::new(ClosedGraph {
            definitions,
            canonical,
            names: self.names,
        });
        locations
            .into_iter()
            .map(|(definition, root)| {
                let (definition, node) = graph
                    .canonical
                    .get(&(definition, root))
                    .copied()
                    .unwrap_or((definition, root));
                Value {
                    node,
                    graph: Rc::clone(&graph),
                    definition,
                }
            })
            .collect()
    }

    fn normalize_roots(&mut self, roots: &[usize]) -> (Vec<Definition>, Vec<(usize, usize)>) {
        if roots.is_empty() {
            return (Vec::new(), Vec::new());
        }
        let mut memo = Keys::new();
        if self.nodes.iter().all(|node| {
            node.scope.is_empty()
                && !matches!(
                    node.kind,
                    Type::Generic { .. } | Type::Bound { .. } | Type::Arbitrary { .. }
                )
        }) {
            // Use the wrapper only when every node has an empty saved scope and
            // none is a generic, bound reference, or arbitrary parameter. The
            // wrapper refers only to checked roots. No old node refers back to
            // it. Otherwise, normalize each root separately. A scoped root then
            // keeps its saved scope. Closed generic roots also use this path.
            let wrapper = self.add(Type::Tuple(roots.to_vec()), Vec::new());
            let definition = normalize(&self.nodes, wrapper, &mut memo);
            let Type::Tuple(children) = &definition.nodes[definition.root].kind else {
                panic!("structural normalization changed the wrapper's constructor");
            };
            let locations = children.iter().map(|node| (0, *node)).collect();
            return (vec![definition], locations);
        }
        let free = free_parameters(&self.nodes);
        let mut definitions = Vec::new();
        let mut interned = BTreeMap::new();
        let mut normalized = BTreeMap::new();
        let mut locations = Vec::new();
        for root in roots {
            if let Some(location) = normalized.get(root) {
                locations.push(*location);
                continue;
            }
            let definition = if free[*root].is_empty() {
                normalize(&self.nodes, *root, &mut memo)
            } else {
                normalize_scoped(&self.nodes, *root, &mut memo)
            };
            let key = (
                definition.keys[definition.root].clone(),
                definition.free_bindings[definition.root].clone(),
            );
            let index = *interned.entry(key).or_insert_with(|| {
                let index = definitions.len();
                definitions.push(definition);
                index
            });
            let location = (index, definitions[index].root);
            normalized.insert(*root, location);
            locations.push(location);
        }
        (definitions, locations)
    }
}

/// Test descriptions contain indices, not handles from unchecked storage.
#[cfg(test)]
#[derive(Debug, Clone)]
pub enum Description {
    Never,
    Class(ClassType<usize>),
    Tuple(Vec<usize>),
    Callable(Callable<usize>),
    Generic {
        parameters: u32,
        body: Callable<usize>,
    },
    Bound {
        owner: usize,
        position: u32,
    },
    Reference(usize),
    Union(Vec<usize>),
    Intersection(Vec<usize>),
}

/// Check a complete description before any value can be queried.
/// Test descriptions must use the declared class argument counts.
#[cfg(test)]
pub fn construct(
    declarations: &Declarations,
    description: &[(Description, Vec<usize>)],
    roots: &[usize],
) -> Vec<Value> {
    let mut builder = Builder::new(declarations);
    builder.nodes = description
        .iter()
        .map(|(kind, scope)| {
            let kind = match kind {
                Description::Never => Type::Never,
                Description::Class(class) => Type::Class(class.clone()),
                Description::Tuple(children) => Type::Tuple(children.clone()),
                Description::Callable(body) => Type::Callable(body.clone()),
                Description::Generic { parameters, body } => Type::Generic {
                    binding: Rc::new(()),
                    parameters: *parameters,
                    body: body.clone(),
                },
                Description::Bound { owner, position } => Type::Bound {
                    owner: *owner,
                    position: *position,
                },
                Description::Reference(target) => Type::Reference(*target),
                Description::Union(children) => Type::Union(children.clone()),
                Description::Intersection(children) => Type::Intersection(children.clone()),
            };
            Node {
                kind,
                scope: scope.clone(),
            }
        })
        .collect();
    builder.finish(roots)
}

fn reachable(nodes: &[Node], root: usize) -> BTreeSet<usize> {
    let mut seen = BTreeSet::new();
    let mut pending = vec![root];
    while let Some(id) = pending.pop() {
        if seen.insert(id) {
            pending.extend(nodes[id].kind.children());
        }
    }
    seen
}

fn free_parameters(nodes: &[Node]) -> Vec<BTreeSet<usize>> {
    let mut free = vec![BTreeSet::new(); nodes.len()];
    loop {
        let mut changed = false;
        for (id, node) in nodes.iter().enumerate() {
            let mut parameters = match node.kind {
                Type::Bound { owner, .. } | Type::Arbitrary { owner, .. } => {
                    BTreeSet::from([owner])
                }
                _ => node
                    .kind
                    .children()
                    .iter()
                    .flat_map(|child| free[*child].iter().copied())
                    .collect(),
            };
            if matches!(node.kind, Type::Generic { .. }) {
                parameters.remove(&id);
            }
            if free[id] != parameters {
                free[id] = parameters;
                changed = true;
            }
        }
        if !changed {
            return free;
        }
    }
}

// Arbitrary parameters already have a checked identity in their type key.
// Bound parameters need their binder owner when an expression is still open.
fn free_bindings(nodes: &[Node]) -> Vec<BTreeSet<usize>> {
    let mut free = vec![BTreeSet::new(); nodes.len()];
    loop {
        let mut changed = false;
        for (id, node) in nodes.iter().enumerate() {
            let mut bindings = if let Type::Bound { owner, .. } = node.kind {
                let Type::Generic { binding, .. } = &nodes[owner].kind else {
                    panic!("a checked parameter owner must be a binder");
                };
                BTreeSet::from([Rc::as_ptr(binding) as usize])
            } else {
                node.kind
                    .children()
                    .iter()
                    .flat_map(|child| free[*child].iter().copied())
                    .collect()
            };
            if let Type::Generic { binding, .. } = &node.kind {
                bindings.remove(&(Rc::as_ptr(binding) as usize));
            }
            if free[id] != bindings {
                free[id] = bindings;
                changed = true;
            }
        }
        if !changed {
            return free;
        }
    }
}

fn validate(nodes: &[Node], roots: &[usize]) {
    if roots.iter().any(|root| *root >= nodes.len())
        || nodes
            .iter()
            .any(|node| node.kind.children().iter().any(|id| *id >= nodes.len()))
    {
        panic!("closed graph references a missing node");
    }
    for node in nodes {
        if let Type::Bound { owner, position }
        | Type::Arbitrary {
            owner, position, ..
        } = node.kind
            && (!node.scope.contains(&owner)
                || !matches!(nodes.get(owner).map(|node| &node.kind), Some(Type::Generic { parameters, .. }) if position < *parameters))
        {
            panic!("closed graph parameter has no visible binder or exceeds its parameter count");
        }
        if node.scope.iter().any(|owner| {
            !matches!(
                nodes.get(*owner).map(|node| &node.kind),
                Some(Type::Generic { .. })
            )
        }) {
            panic!("closed graph saved scope contains a non-binder");
        }
        if node
            .scope
            .iter()
            .enumerate()
            .any(|(position, owner)| nodes[*owner].scope != node.scope[..position])
        {
            panic!("closed graph saved scopes do not follow their binder order");
        }
    }
    let free = free_parameters(nodes);
    if roots.iter().any(|root| {
        free[*root]
            .iter()
            .any(|owner| !nodes[*root].scope.contains(owner))
    }) {
        panic!("closed graph root has a parameter outside its saved scope");
    }
    for (id, node) in nodes.iter().enumerate() {
        let mut scope = node.scope.clone();
        if matches!(node.kind, Type::Generic { .. }) {
            scope.push(id);
        }
        for child in node.kind.children() {
            let saved = &nodes[child].scope;
            // Normalization can remove a reference to an outer value. The
            // child's explicit parameter owners remain valid in that ancestor
            // scope. Reusing it here does not change its bindings.
            let valid = free[child].is_empty() || scope.starts_with(saved);
            assert!(
                valid,
                "closed graph child is not visible in its parent scope"
            );
        }
    }
    let edges = nodes
        .iter()
        .map(|node| {
            if node.kind.is_constructor() {
                Vec::new()
            } else {
                node.kind.children()
            }
        })
        .collect::<Vec<_>>();
    assert!(
        reachability::can_reach_cycle(&edges).is_empty(),
        "closed graph contains an unguarded cycle"
    );
}
