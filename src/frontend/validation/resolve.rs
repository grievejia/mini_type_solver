//! Assertion and type reference resolution.
//!
//! Complete declaration tables permit forward references. Binder lookup is local.

use super::super::ast::{AssertDecl, Formula};
use super::super::diagnostic::Diagnostic;
use super::type_resolver::TypeResolver;
use super::{
    Assertion, AtomBuilder, AtomFormula, CollectedFile, CoreUnit, ResolvedFile, TypeBuilder,
    classes,
};

/// Map every reference to its identifier, failing on the first error.
///
/// Classes resolve before assertions, each in source order. A class error
/// precedes an assertion error wherever either declaration appears.
///
/// # Errors
///
/// Returns the first diagnostic for names, applications, or type parameters.
pub fn resolve(collected: CollectedFile) -> Result<ResolvedFile, Diagnostic> {
    let CollectedFile {
        declarations,
        names,
        classes,
        assertions,
    } = collected;
    let mut resolved_classes = Vec::with_capacity(classes.len());
    for record in classes {
        resolved_classes.push(classes::resolve_class(record, &declarations, &names)?);
    }
    let mut types = TypeBuilder::new(&declarations);
    let mut atoms = AtomBuilder::new();
    let mut resolver = TypeResolver::new(&declarations, &names, &mut types);
    let mut resolved_assertions = Vec::with_capacity(assertions.len());
    for declaration in assertions {
        resolved_assertions.push(resolve_assertion(declaration, &mut atoms, &mut resolver)?);
    }
    Ok(ResolvedFile {
        declarations,
        types: types.finish(),
        atoms: atoms.finish(),
        classes: resolved_classes,
        assertions: resolved_assertions,
    })
}

/// Core-unit boundaries use source formulas before type normalization.
fn resolve_assertion(
    declaration: AssertDecl,
    atoms: &mut AtomBuilder,
    resolver: &mut TypeResolver<'_>,
) -> Result<Assertion, Diagnostic> {
    let AssertDecl { label, formula, .. } = declaration;
    let label = label.map(|label| label.name);
    let units = match unparenthesized(&formula) {
        Formula::And(node) => node
            .operands()
            .map(|operand| resolve_unit(operand, atoms, resolver))
            .collect::<Result<_, _>>()?,
        single => vec![resolve_unit(single, atoms, resolver)?],
    };
    Ok(Assertion { label, units })
}

fn resolve_unit(
    formula: &Formula,
    atoms: &mut AtomBuilder,
    resolver: &mut TypeResolver<'_>,
) -> Result<CoreUnit, Diagnostic> {
    let formula = unparenthesized(formula);
    Ok(CoreUnit {
        span: formula.span(),
        formula: resolve_formula(formula, atoms, resolver)?,
    })
}

/// Parentheses do not create core-unit boundaries.
fn unparenthesized(formula: &Formula) -> &Formula {
    match formula {
        Formula::Paren(group) => unparenthesized(&group.inner),
        single => single,
    }
}

fn resolve_formula(
    formula: &Formula,
    atoms: &mut AtomBuilder,
    resolver: &mut TypeResolver<'_>,
) -> Result<AtomFormula, Diagnostic> {
    match formula {
        Formula::And(node) => Ok(AtomFormula::Conjunction(resolve_operands(
            node.operands(),
            atoms,
            resolver,
        )?)),
        Formula::Or(node) => Ok(AtomFormula::Disjunction(resolve_operands(
            node.operands(),
            atoms,
            resolver,
        )?)),
        Formula::Subtype(atom) => {
            let (lower, upper) = resolver.pair(&atom.left, &atom.right)?;
            Ok(AtomFormula::Atom(atoms.intern_atom(lower, upper)))
        }
        Formula::Paren(group) => resolve_formula(&group.inner, atoms, resolver),
    }
}

fn resolve_operands<'a>(
    operands: impl Iterator<Item = &'a Formula>,
    atoms: &mut AtomBuilder,
    resolver: &mut TypeResolver<'_>,
) -> Result<Vec<AtomFormula>, Diagnostic> {
    operands
        .map(|operand| resolve_formula(operand, atoms, resolver))
        .collect()
}
