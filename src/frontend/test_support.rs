//! Raw semantic builders for trusted programmatic test problems.
//!
//! Fixtures copy checked declaration and hierarchy metadata. They can add raw
//! types and atoms for theory tests, but cannot construct a `ValidatedFile`.
//! Fixtures use the solver's comparison and value rules. Metadata, binding, scope,
//! arity, input ownership, and permitted type kinds must remain valid.

use super::problem::{
    AtomBuilder, BoundRef, Callable, ClassId, Declarations, Hierarchy, MetaVarId, TypeBuilder,
    TypeId,
};
use super::{parse, validate};

#[doc(inline)]
pub use super::ast::{
    CallableTypeExpr, ClassArguments, ClassParameters, Declaration, Formula,
    GenericCallableTypeExpr, GenericParameterExpr, TypeExpr, VarianceExpr,
};

#[derive(Debug)]
pub struct RawProblem {
    pub declarations: Declarations,
    pub types: TypeBuilder,
    pub atoms: AtomBuilder,
    pub hierarchy: Hierarchy,
}

impl RawProblem {
    /// Construct raw builders from a source-validated metadata fixture.
    ///
    /// # Panics
    ///
    /// Panics if the fixture source fails parsing or validation.
    pub fn new(source: &str) -> Self {
        let file = match parse(source).and_then(validate) {
            Ok(file) => file,
            Err(error) => panic!(
                "invalid raw fixture metadata: {}",
                error.render("fixture", source)
            ),
        };
        let declarations = file.declarations().clone();
        let types = TypeBuilder::from_store(file.types().clone(), &declarations);
        Self {
            declarations,
            types,
            atoms: AtomBuilder::from_store(file.atoms().clone()),
            hierarchy: file.hierarchy().clone(),
        }
    }

    /// Extend the raw fixture's declaration and flexible-type tables together.
    ///
    /// # Panics
    ///
    /// Panics if the fixture already declares this metavariable.
    pub fn declare_metavar(&mut self, name: &str) -> MetaVarId {
        let id = self.declarations.add_metavar(name);
        self.types.add_metavar(id);
        id
    }
}

/// Read a required fixture class from checked declarations.
///
/// # Panics
///
/// Panics if the fixture does not declare the class.
#[must_use]
pub fn lookup_class(declarations: &Declarations, name: &str) -> ClassId {
    let Some(id) = declarations.lookup_class(name) else {
        panic!("fixture must declare class {name}");
    };
    id
}

/// Read a required fixture metavariable from checked declarations.
///
/// # Panics
///
/// Panics if the fixture does not declare the metavariable.
#[must_use]
pub fn lookup_metavar(declarations: &Declarations, name: &str) -> MetaVarId {
    let Some(id) = declarations.lookup_metavar(name) else {
        panic!("fixture must declare metavariable {name}");
    };
    id
}

/// Construct the generic identity callable with one shared parameter.
#[must_use]
pub fn generic_identity(problem: &mut RawProblem) -> TypeId {
    let parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let body = Callable {
        params: vec![parameter],
        ret: parameter,
    };
    problem.types.intern_generic(1, &body)
}
