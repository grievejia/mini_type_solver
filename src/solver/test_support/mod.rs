//! Shared engine fixtures and independent result checks.
//!
//! Source checks use raw declarations. Core checks retain the full environment.

mod evaluator;

use crate::frontend::Span;
use crate::frontend::problem::{AtomId, ClassId, MetaVarId, TypeId, TypeNode};
use crate::frontend::test_support::{RawProblem, lookup_class};
use crate::frontend::{parse, validate};
use crate::solver::input::Input;

use super::{AtomFormula, Core, SolveOutcome, ValidatedFile, WorkUnit};

pub use evaluator::{Type, direct_query, model_holds};

pub fn validate_ok(source: &str) -> ValidatedFile {
    let Ok(parsed) = parse(source) else {
        panic!("expected source to parse");
    };
    let Ok(validated) = validate(parsed) else {
        panic!("expected source to validate");
    };
    validated
}

/// Input mode for the independent model evaluator.
#[derive(Clone, Copy)]
pub enum ModelInput<'a> {
    /// Reparse source and evaluate its original syntax trees.
    Source(&'a str),
    /// Evaluate canonical formulas with the declarations used to build `RawProblem`.
    Canonical {
        declarations: &'a str,
        input: &'a Input<'a>,
        formulas: &'a [&'a AtomFormula],
    },
}

/// Assert `core` is subset-minimal over `units`: every entry maps
/// to one unit in order, the reported core list alone is
/// unsatisfiable, and dropping any single survivor from that
/// core list flips its remainder to satisfiable under `rerun`.
/// Every check runs on the reported core's units, never the
/// complete list: discarded units may hold another conflict
/// that must not poison the verdict. The cross-engine contract
/// pins this validity per engine, never core identity.
pub fn assert_core_minimal<'a>(
    units: &[WorkUnit<'a>],
    core: &Core,
    rerun: &mut dyn FnMut(&[WorkUnit<'a>]) -> SolveOutcome,
) {
    let mut kept = Vec::with_capacity(core.units().len());
    let mut cursor = 0;
    for entry in core.units() {
        let offset = units[cursor..]
            .iter()
            .position(|unit| unit.label == entry.label() && unit.span == entry.span())
            .unwrap_or_else(|| panic!("core entry matches no unit: {entry:?}"));
        kept.push(cursor + offset);
        cursor += offset + 1;
    }
    let core_units: Vec<WorkUnit<'a>> = kept.iter().map(|index| units[*index]).collect();
    assert!(
        matches!(rerun(&core_units), SolveOutcome::Unsatisfiable(_)),
        "reported core is satisfiable"
    );
    for (position, drop) in kept.iter().enumerate() {
        let rest: Vec<WorkUnit<'a>> = core_units
            .iter()
            .enumerate()
            .filter(|(index, _)| *index != position)
            .map(|(_, unit)| *unit)
            .collect();
        assert!(
            matches!(rerun(&rest), SolveOutcome::Satisfiable(_)),
            "core stays unsatisfiable without unit {drop}"
        );
    }
}

pub const FIXTURE_DECLARATIONS: &str = "class a; class b;";

pub fn fixture_problem() -> (RawProblem, ClassId, ClassId, MetaVarId) {
    let mut problem = RawProblem::new(FIXTURE_DECLARATIONS);
    let t = problem.declare_metavar("T");
    let a = lookup_class(&problem.declarations, "a");
    let b = lookup_class(&problem.declarations, "b");
    (problem, a, b, t)
}

/// Build an atom formula with the raw fixture's canonical endpoint types.
pub fn atom(problem: &mut RawProblem, lower: TypeNode, upper: TypeNode) -> AtomFormula {
    AtomFormula::Atom(atom_id(problem, lower, upper))
}

/// Intern a comparison of endpoint types that satisfy the raw fixture rules.
pub fn atom_id(problem: &mut RawProblem, lower: TypeNode, upper: TypeNode) -> AtomId {
    let lower = problem.types.intern_type(lower);
    let upper = problem.types.intern_type(upper);
    problem.atoms.intern_atom(lower, upper)
}

/// Build an atom formula from endpoint IDs in this fixture's type store.
pub fn atom_from_ids(problem: &mut RawProblem, lower: TypeId, upper: TypeId) -> AtomFormula {
    AtomFormula::Atom(problem.atoms.intern_atom(lower, upper))
}

pub fn unit(formula: &AtomFormula) -> WorkUnit<'_> {
    WorkUnit {
        formula,
        label: None,
        span: Span::new(0, 0),
    }
}
