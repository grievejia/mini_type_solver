//! Interned immutable types for one theory call.
//!
//! Handles belong to this graph. Constructor edges point to existing handles;
//! variable references point to persistent identities, not their changing values.
//! Each search owns one graph. Handles are used only with that graph.
//! The graph survives rollback. Branch state owns assignments and instances.
//! After output construction, accepted comparison records are released. The
//! returned solution keeps closed output values and bounds. Test builds also
//! keep original and normalized assignment maps. The graph's interning tables
//! are dropped when the theory call ends. Each handle keeps its node data alive.
//!
//! Interning is canonical: equal structures have the same node identifier. `Eq`
//! compares identifiers; `Ord` compares structure and returns `Equal` exactly
//! when `Eq` holds. Map keys, sorting, deduplication, and binary searches require
//! this agreement. Subtype equivalence can hold between different structures.
//! Constructor edges are acyclic and point to nodes already interned, so child
//! identity keys preserve canonicality from leaves through complete values.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;

use crate::frontend::problem::{
    BoundRef, Callable, ClassId, ClassType, Declarations, Generic, TemplateType,
};
use crate::indices::checked_u32;

mod order;
#[cfg(test)]
mod tests;

use super::super::Shape;
use super::identities::{ChoiceId, RigidId, ScopeId, VarId};

/// Stable node identity within one graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct NodeId(u32);

/// An immutable node handle. Identity comparison never follows graph edges.
///
/// `contains_generic` describes the stored constructor structure. It does not
/// follow variable values or deferred instances.
#[derive(Debug)]
struct Node<T> {
    id: NodeId,
    data: Rc<T>,
    contains_generic: bool,
}

impl<T> Clone for Node<T> {
    fn clone(&self) -> Self {
        Self {
            id: self.id,
            data: Rc::clone(&self.data),
            contains_generic: self.contains_generic,
        }
    }
}

impl<T> PartialEq for Node<T> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<T> Eq for Node<T> {}

/// One deferred choice with its complete outward route.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ChoiceCopy {
    pub choice: ChoiceId,
    pub route: Vec<ScopeId>,
}

impl ChoiceCopy {
    pub fn home(choice: ChoiceId) -> Self {
        Self {
            choice,
            route: Vec::new(),
        }
    }
}

/// Constructor or reference. Children retain graph identities and lexical coordinates.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum FactorNode {
    Bound(BoundRef),
    Class(ClassType<SValue>),
    Rigid(RigidId),
    Ref(VarId),
    Tuple(Vec<SValue>),
    Callable(Callable<SValue>),
    Generic(Generic<SValue>),
    Choice(ChoiceCopy),
}

impl FactorNode {
    /// Constructor children in source order. References and choices are leaves.
    pub fn children(&self) -> impl Iterator<Item = &SValue> {
        let (children, returned) = match self {
            Self::Class(class) => (class.arguments.as_slice(), None),
            Self::Tuple(elements) => (elements.as_slice(), None),
            Self::Callable(body) | Self::Generic(Generic { body, .. }) => {
                (body.params.as_slice(), Some(&body.ret))
            }
            Self::Bound(_) | Self::Rigid(_) | Self::Ref(_) | Self::Choice(_) => (&[][..], None),
        };
        children.iter().chain(returned)
    }

    fn shape(&self) -> Shape {
        match self {
            Self::Bound(_) | Self::Rigid(_) | Self::Ref(_) | Self::Choice(_) => Shape::Unknown,
            Self::Class(application) if application.class == ClassId::OBJECT => Shape::Unknown,
            Self::Class(_) => Shape::Class,
            Self::Tuple(elements) => Shape::Tuple(elements.len()),
            Self::Callable(body) | Self::Generic(Generic { body, .. }) => {
                Shape::Callable(body.params.len())
            }
        }
    }
}

/// Interned constructor or reference with immutable children.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SFactor(Node<FactorNode>);

impl SFactor {
    pub fn node(&self) -> &FactorNode {
        &self.0.data
    }
}

/// Interned intersection with sorted, unique, compatible factors.
///
/// An arm contains at least one factor. An intersection with no factors is
/// represented by an arm containing only `object`.
///
/// During propagation, a deferred choice ([`FactorNode::Choice`]) has unknown
/// shape. Propagation cannot use the choice's current instances to discard
/// an arm.
///
/// After search succeeds, witness materialization replaces each deferred choice
/// with the intersection of the choice's instances. If the expanded arm contains
/// incompatible factors, materialization removes the arm from the union.
/// If no arms remain, the value is `never`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SArm(Node<Vec<SFactor>>);

impl SArm {
    pub fn factors(&self) -> &[SFactor] {
        &self.0.data
    }
}

/// Interned union of complete intersection arms. An empty union is never.
///
/// Arms are sorted and unique. Raw values can retain subtype-redundant arms
/// because nested variable assignments can change. Closure removes them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SValue(Node<Vec<SArm>>);

impl SValue {
    pub fn arms(&self) -> &[SArm] {
        &self.0.data
    }

    /// Exactly one factor with no surrounding union or intersection.
    pub fn single_factor(&self) -> Option<&SFactor> {
        let [arm] = self.arms() else {
            return None;
        };
        let [factor] = arm.factors() else {
            return None;
        };
        Some(factor)
    }

    /// True when the immutable type structure contains a generic callable.
    /// Variable references and deferred choices are leaves for this query.
    pub fn contains_generic(&self) -> bool {
        self.0.contains_generic
    }

    /// Copy arm handles without copying their constructor nodes.
    pub fn into_arms(self) -> Vec<SArm> {
        self.0.data.as_ref().clone()
    }
}

#[derive(Debug, Default)]
struct Nodes {
    next: usize,
    factors: BTreeMap<FactorKey, SFactor>,
    arms: BTreeMap<Vec<NodeId>, SArm>,
    values: BTreeMap<Vec<NodeId>, SValue>,
    templates: BTreeMap<(ClassId, ClassId, Vec<NodeId>), Vec<SValue>>,
}

/// Interning uses child identities. Structural sorting has a separate operation.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
enum FactorKey {
    Bound(BoundRef),
    Class(ClassType<NodeId>),
    Rigid(RigidId),
    Ref(VarId),
    Tuple(Vec<NodeId>),
    Callable(Callable<NodeId>),
    Generic(Generic<NodeId>),
    Choice(ChoiceCopy),
}

impl FactorNode {
    fn key(&self) -> FactorKey {
        match self {
            Self::Bound(reference) => FactorKey::Bound(*reference),
            Self::Class(application) => FactorKey::Class(application.map(|value| value.0.id)),
            Self::Rigid(id) => FactorKey::Rigid(*id),
            Self::Ref(id) => FactorKey::Ref(*id),
            Self::Tuple(elements) => {
                FactorKey::Tuple(elements.iter().map(|value| value.0.id).collect())
            }
            Self::Callable(body) => FactorKey::Callable(body.map(|value| value.0.id)),
            Self::Generic(generic) => FactorKey::Generic(Generic {
                parameters: generic.parameters,
                body: generic.body.map(|value| value.0.id),
            }),
            Self::Choice(copy) => FactorKey::Choice(copy.clone()),
        }
    }
}

impl Nodes {
    fn node<T>(&mut self, data: T, contains_generic: bool) -> Node<T> {
        let id = NodeId(checked_u32(self.next, "solver type node count"));
        self.next += 1;
        Node {
            id,
            data: Rc::new(data),
            contains_generic,
        }
    }
}

/// Type interning owned by one search. Shared borrows can intern immutable nodes.
/// Each operation releases the mutable table borrow before following child edges.
#[derive(Debug)]
pub struct Graph {
    nodes: RefCell<Nodes>,
    class_arities: BTreeMap<ClassId, usize>,
}

impl Graph {
    /// Fix class arities from the immutable input declarations.
    pub fn new(declarations: &Declarations) -> Self {
        let class_arities = declarations
            .classes()
            .map(|(id, _)| (id, declarations.class_arity(id)))
            .collect();
        Self {
            nodes: RefCell::new(Nodes::default()),
            class_arities,
        }
    }

    /// Check class arity before publishing a constructor node. Children belong
    /// to this graph. Bound coordinates and reference identities come from
    /// validated types or search operations. Substitution preserves them.
    pub fn intern_factor(&self, factor: FactorNode) -> SFactor {
        if let FactorNode::Class(application) = &factor {
            assert_eq!(
                self.class_arities.get(&application.class),
                Some(&application.arguments.len()),
                "solver class constructor must have its declared arity"
            );
        }
        let key = factor.key();
        let mut nodes = self.nodes.borrow_mut();
        if let Some(existing) = nodes.factors.get(&key) {
            return existing.clone();
        }
        let contains_generic = matches!(factor, FactorNode::Generic(_))
            || factor.children().any(SValue::contains_generic);
        let result = SFactor(nodes.node(factor, contains_generic));
        nodes.factors.insert(key, result.clone());
        result
    }

    /// Normalize only stable identities and outer-shape conflicts.
    /// Nested references can change, so no subtype subsumption applies here.
    pub fn arm(&self, mut factors: Vec<SFactor>) -> Option<SArm> {
        if factors
            .iter()
            .any(|factor| factor.node() == &FactorNode::Class(ClassType::NEVER))
        {
            return None;
        }
        if factors.len() > 1 {
            factors.retain(|factor| factor.node() != &FactorNode::Class(ClassType::OBJECT));
        }
        if factors.is_empty() {
            factors.push(self.intern_factor(FactorNode::Class(ClassType::OBJECT)));
        }
        factors.sort();
        factors.dedup();
        if Shape::conflict(factors.iter().map(|factor| factor.node().shape())) {
            return None;
        }
        Some(self.intern_arm(factors))
    }

    /// The caller has checked that these factors form one normalized non-bottom arm.
    fn intern_arm(&self, factors: Vec<SFactor>) -> SArm {
        let key: Vec<_> = factors.iter().map(|factor| factor.0.id).collect();
        let mut nodes = self.nodes.borrow_mut();
        if let Some(existing) = nodes.arms.get(&key) {
            return existing.clone();
        }
        let contains_generic = factors.iter().any(|factor| factor.0.contains_generic);
        let result = SArm(nodes.node(factors, contains_generic));
        nodes.arms.insert(key, result.clone());
        result
    }

    fn intern_union(&self, mut arms: Vec<SArm>) -> SValue {
        arms.sort();
        arms.dedup();
        let key: Vec<_> = arms.iter().map(|arm| arm.0.id).collect();
        let mut nodes = self.nodes.borrow_mut();
        if let Some(existing) = nodes.values.get(&key) {
            return existing.clone();
        }
        let contains_generic = arms.iter().any(|arm| arm.0.contains_generic);
        let result = SValue(nodes.node(arms, contains_generic));
        nodes.values.insert(key, result.clone());
        result
    }

    /// Construct a union from one normalized arm.
    pub fn arm_value(&self, arm: SArm) -> SValue {
        self.intern_union(vec![arm])
    }

    /// Construct the empty union.
    pub fn never(&self) -> SValue {
        self.intern_union(Vec::new())
    }

    /// Construct the unrestricted type.
    pub fn object(&self) -> SValue {
        self.factor(FactorNode::Class(ClassType::OBJECT))
    }

    /// Intern a constructor and normalize its one-factor value.
    pub fn factor(&self, factor: FactorNode) -> SValue {
        self.value(self.intern_factor(factor))
    }

    /// Normalize one interned factor as a complete value.
    pub fn value(&self, factor: SFactor) -> SValue {
        match self.arm(vec![factor]) {
            Some(arm) => self.arm_value(arm),
            None => self.never(),
        }
    }

    /// Combine complete arms. Object absorbs every other arm.
    pub fn union(&self, values: impl IntoIterator<Item = SValue>) -> SValue {
        let mut arms = Vec::new();
        for value in values {
            arms.extend(value.into_arms());
        }
        if arms.iter().any(|arm| {
            let [factor] = arm.factors() else {
                return false;
            };
            factor.node() == &FactorNode::Class(ClassType::OBJECT)
        }) {
            return self.object();
        }
        self.intern_union(arms)
    }

    /// Distribute outer lattice operators. Constructor children remain graph edges.
    pub fn intersection(&self, values: impl IntoIterator<Item = SValue>) -> SValue {
        let mut value = self.object();
        for child in values {
            let mut arms = Vec::new();
            for left in value.arms() {
                for right in child.arms() {
                    if let Some(arm) = self.arm(
                        left.factors()
                            .iter()
                            .chain(right.factors())
                            .cloned()
                            .collect(),
                    ) {
                        arms.push(arm);
                    }
                }
            }
            value = self.intern_union(arms);
        }
        value
    }

    /// Substitute one checked ancestor template. Each owner and ancestor pair
    /// identifies one template in this graph's immutable hierarchy. Actual
    /// arguments are reused directly, including their binders and references.
    pub fn ancestor_arguments(
        &self,
        owner: ClassId,
        template: &ClassType<TemplateType>,
        arguments: &[SValue],
    ) -> Vec<SValue> {
        assert_eq!(
            self.class_arities.get(&owner),
            Some(&arguments.len()),
            "ancestor substitution must supply all owner arguments"
        );
        let key = (
            owner,
            template.class,
            arguments.iter().map(|value| value.0.id).collect(),
        );
        if let Some(result) = self.nodes.borrow().templates.get(&key) {
            return result.clone();
        }
        let result: Vec<_> = template
            .arguments
            .iter()
            .map(|argument| instantiate_template(self, argument, owner, arguments))
            .collect();
        assert_eq!(
            self.class_arities.get(&template.class),
            Some(&result.len()),
            "ancestor template must have its declared arity"
        );
        self.nodes
            .borrow_mut()
            .templates
            .insert(key, result.clone());
        result
    }
}

/// Substitute superclass templates with complete live argument values.
/// Parameter references belong to `owner`. A replacement is not recursively
/// substituted, so its callable binders and selections keep their identity.
fn instantiate_template(
    graph: &Graph,
    template: &TemplateType,
    owner: ClassId,
    arguments: &[SValue],
) -> SValue {
    match template {
        TemplateType::Parameter { reference } => {
            assert_eq!(
                reference.owner, owner,
                "ancestor parameter has another owner"
            );
            let Some(argument) = arguments.get(reference.position as usize) else {
                panic!("ancestor parameter position exceeds declared arity");
            };
            argument.clone()
        }
        TemplateType::Class(application) => {
            graph.factor(FactorNode::Class(application.map(|argument| {
                instantiate_template(graph, argument, owner, arguments)
            })))
        }
        TemplateType::Tuple(elements) => graph.factor(FactorNode::Tuple(
            elements
                .iter()
                .map(|element| instantiate_template(graph, element, owner, arguments))
                .collect(),
        )),
        TemplateType::Callable { params, ret } => graph.factor(FactorNode::Callable(Callable {
            params: params
                .iter()
                .map(|param| instantiate_template(graph, param, owner, arguments))
                .collect(),
            ret: instantiate_template(graph, ret, owner, arguments),
        })),
        TemplateType::Union(children) => graph.union(
            children
                .iter()
                .map(|child| instantiate_template(graph, child, owner, arguments)),
        ),
        TemplateType::Intersection(children) => graph.intersection(
            children
                .iter()
                .map(|child| instantiate_template(graph, child, owner, arguments)),
        ),
    }
}
