//! Shared fixtures for validation checks.

mod assertions;
mod hierarchy;
mod resolution;

use super::super::parse;
use super::atoms::Atom;
use super::{
    Assertion, AtomFormula, Diagnostic, ResolvedFile, TypeId, ValidatedFile, collect, order,
    resolve,
};

fn collect_err(source: &str) -> Diagnostic {
    let Ok(parsed) = parse(source) else {
        panic!("expected source to parse");
    };
    let Err(diagnostic) = collect(parsed) else {
        panic!("expected source to fail collection");
    };
    diagnostic
}

fn resolve_err(source: &str) -> Diagnostic {
    let Ok(parsed) = parse(source) else {
        panic!("expected source to parse");
    };
    let Ok(collected) = collect(parsed) else {
        panic!("expected source to collect");
    };
    let Err(diagnostic) = resolve(collected) else {
        panic!("expected source to fail resolution");
    };
    diagnostic
}

fn resolve_ok(source: &str) -> ResolvedFile {
    let Ok(parsed) = parse(source) else {
        panic!("expected source to parse");
    };
    let Ok(collected) = collect(parsed) else {
        panic!("expected source to collect");
    };
    match resolve(collected) {
        Ok(resolved) => resolved,
        Err(diagnostic) => panic!(
            "expected source to resolve: {}",
            diagnostic.render("test", source)
        ),
    }
}

fn order_ok(source: &str) -> ValidatedFile {
    let resolved = resolve_ok(source);
    match order(resolved) {
        Ok(ordered) => ordered,
        Err(diagnostic) => panic!(
            "expected source to order: {}",
            diagnostic.render("test", source)
        ),
    }
}

fn order_err(source: &str) -> Diagnostic {
    let resolved = resolve_ok(source);
    let Err(diagnostic) = order(resolved) else {
        panic!("expected source to fail ordering");
    };
    diagnostic
}

fn last_start(source: &str, spelling: &str) -> usize {
    let Some(start) = source.rfind(spelling) else {
        panic!("expected {spelling:?} in test source");
    };
    start
}

fn resolved_atom(resolved: &ResolvedFile, assertion: &Assertion) -> Atom {
    let [unit] = assertion.units.as_slice() else {
        panic!("expected one resolved core unit");
    };
    let AtomFormula::Atom(atom) = &unit.formula else {
        panic!("expected one resolved atom");
    };
    *resolved.atoms.atom(*atom)
}

fn resolved_lowers(resolved: &ResolvedFile) -> Vec<TypeId> {
    resolved
        .assertions
        .iter()
        .map(|assertion| resolved_atom(resolved, assertion).lower)
        .collect()
}
