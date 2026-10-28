//! Declaration collection and validation stage records.
//!
//! The frontend calls each stage in order. Each stage consumes its checked input.

mod atoms;
mod classes;
mod declarations;
mod file;
mod hierarchy;
mod resolve;
#[cfg(test)]
mod tests;
mod type_resolver;
mod types;

use std::collections::BTreeSet;

use crate::indices::checked_u32;

use super::ast::{
    AssertDecl, ClassDecl, ClassParameters, Declaration, ParsedFile, SuperclassExpr,
    into_declarations,
};
use super::diagnostic::{Diagnostic, DiagnosticKind, NameKind, Span, diagnostic};
use classes::ParameterUse;

pub use atoms::{Atom, AtomBuilder, AtomId, AtomStore};
pub use classes::{ClassParamRef, TemplateType};
pub use declarations::{
    BUILTIN_COUNT, ClassDefinition, ClassId, ClassParameter, DeclarationBuilder, Declarations,
    MetaVarId, NameLookup, Variance as ClassVariance,
};
#[doc(inline)]
pub use file::{Assertion, AtomFormula, CoreUnit};
pub use hierarchy::{Hierarchy, order};
pub use resolve::resolve;
pub use types::{
    BinderReplacement, BoundRef, Callable, ClassType, Generic, TypeBuilder, TypeId, TypeNode,
    TypeStore, live_bound_positions,
};

/// Declarations with names collected into tables.
///
/// Identifier tables hold every declared class and metavariable, class
/// records hold each declaration with its spans in source order, and
/// assertions are stored unmodified with their labels.
#[derive(Debug)]
pub struct CollectedFile {
    declarations: Declarations,
    names: NameLookup,
    classes: Vec<CollectedClass>,
    assertions: Vec<AssertDecl>,
}

/// One collected class declaration, in source order.
///
/// Keeps the identifier, declaration span, and unresolved superclass expressions
/// with their source spans. The declaration table owns the class name.
#[derive(Debug)]
pub struct CollectedClass {
    id: ClassId,
    span: Span,
    superclasses: Vec<SuperclassExpr>,
}

/// Declarations with every reference mapped to identifiers.
///
/// Superclass names resolve against declared classes plus the built-ins;
/// plain term names resolve against classes and `?`-prefixed names
/// against declared metavariables. Class records keep their spans;
/// assertions stay in source order.
#[derive(Debug)]
pub struct ResolvedFile {
    declarations: Declarations,
    types: TypeStore,
    atoms: AtomStore,
    classes: Vec<ResolvedClass>,
    assertions: Vec<Assertion>,
}

/// Validated source declarations and formulas over interned atoms.
///
/// Names, restrictions, class arguments, and inheritance are checked.
/// Every occurrence of one endpoint pair shares its `AtomId`.
/// Hierarchy validation publishes the file after all checks pass.
#[derive(Debug)]
pub struct ValidatedFile {
    declarations: Declarations,
    types: TypeStore,
    atoms: AtomStore,
    hierarchy: Hierarchy,
    assertions: Vec<Assertion>,
}

/// One resolved class declaration, in source order.
#[derive(Debug)]
pub struct ResolvedClass {
    id: ClassId,
    span: Span,
    superclasses: Vec<ResolvedSuperclass>,
}

/// One checked superclass template with separate diagnostic source data.
///
/// The root-name span locates self-edge errors. The complete expression span
/// locates ancestor-argument conflicts. Surviving parameter uses retain their
/// polarity and source span for variance checks.
#[derive(Debug)]
pub struct ResolvedSuperclass {
    name_span: Span,
    template: ClassType<TemplateType>,
    span: Span,
    parameter_uses: Vec<ParameterUse>,
}

/// Move parsed declarations into tables, records, and assertion storage.
///
/// Declarations are processed in source order, so the first duplicate
/// or built-in redeclaration wins.
///
/// # Errors
///
/// Returns the first collection [`Diagnostic`] when a name is declared
/// twice, a superclass repeats within one declaration, a declaration
/// reuses a built-in class name, or a superclass list uses `never`.
pub fn collect(parsed: ParsedFile) -> Result<CollectedFile, Diagnostic> {
    let mut declarations = DeclarationBuilder::new();
    let mut classes = Vec::new();
    let mut assertions: Vec<AssertDecl> = Vec::new();
    let mut labels = BTreeSet::new();
    for decl in into_declarations(parsed) {
        match decl {
            Declaration::Class(decl) => {
                classes.push(collect_class(decl, &mut declarations)?);
            }
            Declaration::Metavar(decl) => {
                if declarations.insert_metavar(&decl.name.name).is_none() {
                    return Err(diagnostic(
                        decl.name.span,
                        DiagnosticKind::DuplicateName {
                            kind: NameKind::Metavar,
                            name: decl.name.name,
                        },
                    ));
                }
            }
            Declaration::Assert(decl) => {
                if let Some(label) = &decl.label
                    && !labels.insert(label.name.clone())
                {
                    return Err(diagnostic(
                        label.span,
                        DiagnosticKind::DuplicateName {
                            kind: NameKind::AssertionName,
                            name: label.name.clone(),
                        },
                    ));
                }
                assertions.push(decl);
            }
        }
    }
    let (declarations, names) = declarations.finish();
    Ok(CollectedFile {
        declarations,
        names,
        classes,
        assertions,
    })
}

/// Register one class declaration and check the names that it declares.
///
/// The class and its parameters enter the declarations before its superclass list is
/// checked. This step does not resolve superclass names.
fn collect_class(
    decl: ClassDecl,
    declarations: &mut DeclarationBuilder,
) -> Result<CollectedClass, Diagnostic> {
    let ClassDecl {
        span,
        name,
        parameters,
        superclasses: declared,
    } = decl;
    if Declarations::is_builtin(&name.name) {
        return Err(diagnostic(
            name.span,
            DiagnosticKind::BuiltinRedeclared { name: name.name },
        ));
    }
    let parameters = parameters
        .into_iter()
        .flat_map(ClassParameters::into_operands)
        .map(ClassParameter::from)
        .collect();
    let inserted = declarations.insert_class(&name.name, parameters);
    let Some(id) = inserted else {
        return Err(diagnostic(
            name.span,
            DiagnosticKind::DuplicateName {
                kind: NameKind::Class,
                name: name.name,
            },
        ));
    };
    let mut parameter_names = BTreeSet::new();
    for parameter in declarations.declarations().class_parameters(id) {
        if !parameter_names.insert(parameter.name()) {
            return Err(diagnostic(
                parameter.span(),
                DiagnosticKind::DuplicateName {
                    kind: NameKind::TypeParameter,
                    name: parameter.name().to_owned(),
                },
            ));
        }
        if Declarations::is_builtin(parameter.name()) {
            return Err(diagnostic(
                parameter.span(),
                DiagnosticKind::BuiltinTypeParameter {
                    name: parameter.name().to_owned(),
                },
            ));
        }
    }
    let mut superclasses = Vec::with_capacity(declared.len());
    for superclass in declared {
        if Declarations::is_never(&superclass.name.name) {
            return Err(diagnostic(
                superclass.name.span,
                DiagnosticKind::NeverAsSuperclass,
            ));
        }
        if superclasses
            .iter()
            .any(|seen: &SuperclassExpr| seen.name.name == superclass.name.name)
        {
            return Err(diagnostic(
                superclass.name.span,
                DiagnosticKind::DuplicateSuperclass {
                    name: superclass.name.name,
                },
            ));
        }
        superclasses.push(superclass);
    }
    Ok(CollectedClass {
        id,
        span,
        superclasses,
    })
}
