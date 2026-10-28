//! Read-only data from reference resolution and hierarchy validation.
//!
//! Identifiers belong to their accompanying stores. `ValidatedFile` exposes
//! immutable borrows of these owners; its construction remains in validation.
//!
//! Start from assertion core units to inspect canonical atoms and their types.
//! Class and metavariable identifiers refer to the same file's declarations.
//! Hierarchy queries return the checked ancestor order and argument templates.
//! Builders and intermediate validation records are private implementation data.
//!
//! # Examples
//!
//! ```
//! use mini_type_solver::frontend::{self, problem::{AtomFormula, TypeNode}};
//!
//! let source = "class Animal; class Dog extends Animal; metavar ?T; assert Dog <: ?T;";
//! let file = frontend::parse(source).and_then(frontend::validate)?;
//! for assertion in file.assertions() {
//!     for unit in &assertion.units {
//!         if let AtomFormula::Atom(atom) = &unit.formula
//!             && let TypeNode::Class(class) = file.types().type_node(
//!                 file.atoms().atom(*atom).lower,
//!             )
//!         {
//!             println!("{}", file.declarations().class_name(class.class));
//!         }
//!     }
//! }
//! # Ok::<(), frontend::Diagnostic>(())
//! ```

#[doc(inline)]
pub use super::validation::{
    Assertion, Atom, AtomFormula, AtomId, AtomStore, BoundRef, Callable, ClassDefinition, ClassId,
    ClassParamRef, ClassParameter, ClassType, ClassVariance, CoreUnit, Declarations, Generic,
    Hierarchy, MetaVarId, TemplateType, TypeId, TypeNode, TypeStore,
};

#[cfg(test)]
pub use super::validation::{AtomBuilder, TypeBuilder};
