//! Declaration records and source name lookup.
//!
//! Declaration identifiers follow source order. Name lookup is used during
//! collection and resolution. Semantic type construction has a separate owner.

use std::collections::BTreeMap;

use super::super::ast::{ClassParameterExpr, VarianceExpr};
use super::super::diagnostic::Span;
use crate::indices::checked_u32;

pub const BUILTIN_COUNT: usize = 2;
const BUILTIN_NAMES: [&str; BUILTIN_COUNT] = ["object", "never"];

/// Identifier of a declared class.
///
/// `ClassId(0)` is `object` and `ClassId(1)` is `never`. Further identifiers
/// follow declaration order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ClassId(u32);

/// Identifier of a declared metavariable, in declaration order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct MetaVarId(u32);

impl ClassId {
    /// Identifier of the built-in `object`, pre-registered first.
    pub const OBJECT: ClassId = ClassId(0);

    /// Identifier of the built-in `never`, pre-registered second.
    pub const NEVER: ClassId = ClassId(1);

    /// Array index for dense per-class tables.
    #[must_use]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Declared variance, independent of source syntax.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Variance {
    Invariant,
    Covariant,
    Contravariant,
}

/// One semantic class parameter in declaration order.
///
/// The span covers the declared name, which collection diagnostics report.
#[derive(Debug, Clone)]
pub struct ClassParameter {
    name: String,
    variance: Variance,
    span: Span,
}

impl From<ClassParameterExpr> for ClassParameter {
    fn from(parameter: ClassParameterExpr) -> Self {
        let variance = match parameter.variance {
            VarianceExpr::Invariant => Variance::Invariant,
            VarianceExpr::Covariant(_) => Variance::Covariant,
            VarianceExpr::Contravariant(_) => Variance::Contravariant,
        };
        Self {
            name: parameter.name.name,
            variance,
            span: parameter.name.span,
        }
    }
}

impl ClassParameter {
    /// Read the declared parameter name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Read the declared variance.
    #[must_use]
    pub fn variance(&self) -> Variance {
        self.variance
    }

    /// Read the parameter's source location.
    #[must_use]
    pub fn span(&self) -> Span {
        self.span
    }
}

/// One class name and its parameter declaration.
#[derive(Debug, Clone)]
pub struct ClassDefinition {
    name: String,
    parameters: Vec<ClassParameter>,
}

impl ClassDefinition {
    /// Read the declared class name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }
}

/// Complete declaration metadata, without type or hierarchy state.
#[derive(Debug, Clone)]
pub struct Declarations {
    classes: Vec<ClassDefinition>,
    metavars: Vec<String>,
}

impl Declarations {
    /// Read whether a name denotes a built-in class.
    #[must_use]
    pub fn is_builtin(name: &str) -> bool {
        BUILTIN_NAMES.contains(&name)
    }

    /// Read whether a name denotes the bottom class.
    #[must_use]
    pub fn is_never(name: &str) -> bool {
        name == "never"
    }

    /// Read the number of user classes.
    #[must_use]
    pub fn user_class_count(&self) -> usize {
        self.classes.len() - BUILTIN_COUNT
    }

    /// Read the number of classes, including built-ins.
    #[must_use]
    pub fn class_count(&self) -> usize {
        self.classes.len()
    }

    /// Read the number of declared metavariables.
    #[must_use]
    pub fn metavar_count(&self) -> usize {
        self.metavars.len()
    }

    /// Read the name belonging to a class identifier.
    #[must_use]
    pub fn class_name(&self, id: ClassId) -> &str {
        &self.classes[id.index()].name
    }

    /// Read class parameters in declaration order.
    pub fn class_parameters(&self, id: ClassId) -> impl Iterator<Item = &ClassParameter> {
        self.classes[id.index()].parameters.iter()
    }

    /// Read the argument count fixed by collection.
    #[must_use]
    pub fn class_arity(&self, id: ClassId) -> usize {
        self.classes[id.index()].parameters.len()
    }

    /// Read classes in declaration order.
    pub fn classes(&self) -> impl Iterator<Item = (ClassId, &ClassDefinition)> {
        self.classes
            .iter()
            .enumerate()
            .map(|(index, definition)| (ClassId(checked_u32(index, "class count")), definition))
    }

    /// Read metavariables in declaration order.
    pub fn metavars(&self) -> impl Iterator<Item = (MetaVarId, &str)> {
        self.metavars.iter().enumerate().map(|(index, name)| {
            (
                MetaVarId(checked_u32(index, "metavariable count")),
                name.as_str(),
            )
        })
    }

    /// Find a class in immutable declaration records.
    ///
    /// Resolution uses `NameLookup`. This scan supports inspection and model names
    /// after the lookup index has been discarded.
    #[must_use]
    pub fn lookup_class(&self, name: &str) -> Option<ClassId> {
        self.classes()
            .find_map(|(id, class)| (class.name == name).then_some(id))
    }

    /// Find a metavariable in immutable declaration records.
    #[cfg(test)]
    #[must_use]
    pub fn lookup_metavar(&self, name: &str) -> Option<MetaVarId> {
        self.metavars()
            .find_map(|(id, found)| (found == name).then_some(id))
    }

    /// Extend a raw fixture without changing its class schema.
    ///
    /// # Panics
    ///
    /// Panics if the fixture already declares this metavariable.
    #[cfg(test)]
    pub fn add_metavar(&mut self, name: &str) -> MetaVarId {
        assert!(
            !self.metavars.iter().any(|existing| existing == name),
            "test metavariable must be fresh: {name}"
        );
        let id = MetaVarId(checked_u32(self.metavars.len(), "metavariable count"));
        self.metavars.push(name.to_owned());
        id
    }
}

/// Immutable source name lookup after collection completes.
#[derive(Debug)]
pub struct NameLookup {
    classes: BTreeMap<String, ClassId>,
    metavars: BTreeMap<String, MetaVarId>,
}

impl NameLookup {
    /// Resolve a class source name.
    #[must_use]
    pub fn lookup_class(&self, name: &str) -> Option<ClassId> {
        self.classes.get(name).copied()
    }

    /// Resolve a metavariable source name.
    #[must_use]
    pub fn lookup_metavar(&self, name: &str) -> Option<MetaVarId> {
        self.metavars.get(name).copied()
    }
}

/// Collection owns each name index together with the records it indexes.
#[derive(Debug)]
pub struct DeclarationBuilder {
    declarations: Declarations,
    names: NameLookup,
}

impl DeclarationBuilder {
    /// Start collection with the built-in classes registered.
    #[must_use]
    pub fn new() -> Self {
        let declarations = Declarations {
            classes: BUILTIN_NAMES
                .iter()
                .map(|name| ClassDefinition {
                    name: (*name).to_owned(),
                    parameters: Vec::new(),
                })
                .collect(),
            metavars: Vec::new(),
        };
        let names = NameLookup {
            classes: declarations
                .classes()
                .map(|(id, class)| (class.name.clone(), id))
                .collect(),
            metavars: BTreeMap::new(),
        };
        Self {
            declarations,
            names,
        }
    }

    /// Read the declarations collected so far.
    #[must_use]
    pub fn declarations(&self) -> &Declarations {
        &self.declarations
    }

    /// Complete collection and publish both records and their name index.
    #[must_use]
    pub fn finish(self) -> (Declarations, NameLookup) {
        (self.declarations, self.names)
    }

    /// Register ordered class parameters without constructing a semantic type.
    pub fn insert_class(&mut self, name: &str, parameters: Vec<ClassParameter>) -> Option<ClassId> {
        if self.names.classes.contains_key(name) {
            return None;
        }
        let id = ClassId(checked_u32(self.declarations.classes.len(), "class count"));
        self.names.classes.insert(name.to_owned(), id);
        self.declarations.classes.push(ClassDefinition {
            name: name.to_owned(),
            parameters,
        });
        Some(id)
    }

    /// Register a metavariable without constructing a semantic type.
    pub fn insert_metavar(&mut self, name: &str) -> Option<MetaVarId> {
        if self.names.metavars.contains_key(name) {
            return None;
        }
        let id = MetaVarId(checked_u32(
            self.declarations.metavars.len(),
            "metavariable count",
        ));
        self.names.metavars.insert(name.to_owned(), id);
        self.declarations.metavars.push(name.to_owned());
        Some(id)
    }
}

impl MetaVarId {
    /// Read the position in its declaration table.
    #[must_use]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}
