//! Public values borrow immutable type definitions from the accepted solution.
//!
//! Child queries copy handles. They keep parameter owners and recursive references.

mod render;
#[cfg(test)]
mod tests;

use std::hash::{Hash, Hasher};
use std::rc::Rc;

use crate::frontend::problem::{Callable, Declarations};

use super::theory::TheorySolution;
use super::theory::closed::{Value, ValueNode};

/// Transfer the checked assignment into declaration-ordered public entries.
///
/// The solution contains every variable in the selected comparisons. A missing
/// declared variable is unconstrained. Assigned values retain their checked
/// graph and owners; construction does not change their types.
pub fn build_model(declarations: &Declarations, solution: TheorySolution) -> Model {
    let mut assignments = solution.into_assignments();
    let names = Rc::new(DisplayNames {
        reserved: declarations
            .metavars()
            .map(|(_, name)| name.to_owned())
            .collect(),
    });
    let entries = declarations
        .metavars()
        .map(|(id, name)| ModelEntry {
            metavar: name.to_owned(),
            value: match assignments.remove(&id) {
                Some(value) => ModelValue::Assigned(AssignedValue {
                    value,
                    names: Rc::clone(&names),
                }),
                None => ModelValue::Unconstrained,
            },
        })
        .collect();
    Model { entries }
}

/// One accepted value for each declared metavar.
#[derive(Debug, PartialEq, Eq)]
pub struct Model {
    entries: Vec<ModelEntry>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct ModelEntry {
    metavar: String,
    value: ModelValue,
}

impl ModelEntry {
    #[must_use]
    pub fn metavar(&self) -> &str {
        &self.metavar
    }
    #[must_use]
    pub fn value(&self) -> &ModelValue {
        &self.value
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ModelValue {
    Unconstrained,
    Assigned(AssignedValue),
}

/// A checked graph handle and immutable names used only for rendering.
#[derive(Debug, Clone)]
pub struct AssignedValue {
    value: Value,
    names: Rc<DisplayNames>,
}

/// Identity of one shared node in its owning graph. Copies keep the identity.
/// Equal type structures in different graphs have different identities.
#[derive(Debug, Clone)]
pub struct AssignedNodeId {
    value: Value,
}

impl PartialEq for AssignedNodeId {
    fn eq(&self, other: &Self) -> bool {
        self.value.same_occurrence(&other.value)
    }
}
impl Eq for AssignedNodeId {}

impl Hash for AssignedNodeId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash_occurrence(state);
    }
}

#[derive(Debug)]
struct DisplayNames {
    reserved: Vec<String>,
}

/// Read one level of a value. Children still refer to the same graph.
#[derive(Debug)]
pub enum AssignedNode {
    Never,
    Bound {
        owner: AssignedValue,
        position: u32,
    },
    Class {
        name: String,
        arguments: Vec<AssignedValue>,
    },
    Tuple(Vec<AssignedValue>),
    Callable(Callable<AssignedValue>),
    /// A Bound descendant owned by this binder names this generic value itself
    /// as its owner. References to other binders retain their own owners.
    Generic {
        parameters: u32,
        body: Callable<AssignedValue>,
    },
    Union(Vec<AssignedValue>),
    Intersection(Vec<AssignedValue>),
}

impl PartialEq for AssignedValue {
    fn eq(&self, other: &Self) -> bool {
        // Printed names are public data. Graph addresses and class identifiers
        // from separate solve calls cannot determine model equality.
        self.render() == other.render()
    }
}
impl Eq for AssignedValue {}

impl Model {
    #[must_use]
    pub fn entries(&self) -> &[ModelEntry] {
        &self.entries
    }
    #[must_use]
    pub fn render(&self) -> String {
        let mut out = String::from("satisfiable\nmodel:\n");
        for entry in &self.entries {
            out.push_str("  ?");
            out.push_str(&entry.metavar);
            out.push_str(" = ");
            out.push_str(&entry.value.render());
            out.push('\n');
        }
        out
    }
}

impl ModelValue {
    #[must_use]
    pub fn render(&self) -> String {
        match self {
            Self::Unconstrained => String::from("unconstrained"),
            Self::Assigned(value) => value.render(),
        }
    }
}

impl AssignedValue {
    fn child(&self, value: Value) -> Self {
        Self {
            value,
            names: Rc::clone(&self.names),
        }
    }

    /// Identify the shared node occurrence. The identifier retains its graph.
    #[must_use]
    pub fn id(&self) -> AssignedNodeId {
        AssignedNodeId {
            value: self.value.occurrence(),
        }
    }

    /// Copies of one binder have the same owner, even when names differ.
    #[must_use]
    pub fn same_binding(&self, other: &Self) -> bool {
        self.value.same_binding(&other.value)
    }

    /// Saved outer owners of an open value, from outermost to innermost.
    /// Unused saved owners remain in the list. Closed values return no owners.
    /// A generic's own owner is excluded.
    #[must_use]
    pub fn binding_scope(&self) -> Vec<Self> {
        self.value
            .binding_scope()
            .into_iter()
            .map(|owner| self.child(owner))
            .collect()
    }

    /// Read one level without choosing names or unfolding recursive paths.
    /// Children can return to a node already read. Owner links are not type edges.
    ///
    /// # Panics
    ///
    /// Panics if an internal arbitrary parameter escapes into a public value.
    #[must_use]
    pub fn node(&self) -> AssignedNode {
        match self.value.node() {
            ValueNode::Arbitrary => {
                panic!("an arbitrary parameter cannot escape into a public value")
            }
            ValueNode::Never => AssignedNode::Never,
            ValueNode::Bound {
                owner, position, ..
            } => AssignedNode::Bound {
                owner: self.child(owner),
                position,
            },
            ValueNode::Class {
                name, arguments, ..
            } => AssignedNode::Class {
                name,
                arguments: arguments
                    .into_iter()
                    .map(|value| self.child(value))
                    .collect(),
            },
            ValueNode::Tuple(children) => AssignedNode::Tuple(
                children
                    .into_iter()
                    .map(|value| self.child(value))
                    .collect(),
            ),
            ValueNode::Callable(body) => {
                AssignedNode::Callable(body.map(|value| self.child(value.clone())))
            }
            ValueNode::Generic { parameters, body } => AssignedNode::Generic {
                parameters,
                body: body.map(|value| self.child(value.clone())),
            },
            ValueNode::Union(children) => AssignedNode::Union(
                children
                    .into_iter()
                    .map(|value| self.child(value))
                    .collect(),
            ),
            ValueNode::Intersection(children) => AssignedNode::Intersection(
                children
                    .into_iter()
                    .map(|value| self.child(value))
                    .collect(),
            ),
        }
    }

    /// Render with names assigned from this value's saved outer scope.
    ///
    /// # Panics
    ///
    /// Panics if a checked parameter has no display name.
    #[must_use]
    pub fn render(&self) -> String {
        render::value(self)
    }
}
