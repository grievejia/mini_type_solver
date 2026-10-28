//! Shared checks for engine verdicts, valid models, and subset-minimal cores.
//!
//! Every engine must match the hand-derived verdict for each input. Each returned
//! model is checked by the independent evaluator. Each core must fail as a whole
//! and succeed after any one unit is removed, in the original environment.
//! Models and cores may differ between engines; general engine checks require
//! the same verdict. Individual output fixtures also check their expected text.

mod classes;
mod constructors;
mod generics;
mod interactions;
mod outcomes;
mod ranges;
mod recursive;
mod scopes;

use crate::frontend::Span;
use crate::frontend::problem::TypeId;
use crate::frontend::test_support::RawProblem;
use crate::solver::input::Input;

use super::direct::run_direct;
use super::dnf::run_dnf;
use super::sat::run_varisat;
use super::test_support::{ModelInput, assert_core_minimal, model_holds, validate_ok};
use super::theory::TheoryResult;
use super::{
    AtomFormula, DirectStats, DnfStats, SatStats, SharedStats, SolveOutcome, WorkUnit,
    solve_conjunction, work_units,
};

/// One engine tag: run it over a unit list with fresh statistics.
#[derive(Debug, Clone, Copy)]
pub enum Engine {
    Dnf,
    Direct,
    Varisat,
}

pub fn run_engine(engine: Engine, units: &[WorkUnit<'_>], input: &Input<'_>) -> SolveOutcome {
    match engine {
        Engine::Dnf => run_dnf(
            units,
            input,
            &mut DnfStats::default(),
            &mut SharedStats::default(),
        ),
        Engine::Direct => run_direct(
            units,
            input,
            &mut DirectStats::default(),
            &mut SharedStats::default(),
        ),
        Engine::Varisat => run_varisat(
            units,
            input,
            &mut SatStats::default(),
            &mut SharedStats::default(),
        ),
    }
}

fn callable_type(problem: &mut RawProblem, params: &[TypeId], ret: TypeId) -> TypeId {
    problem.types.intern_callable(params.to_vec(), ret)
}

/// Check one unit list under every engine. Satisfiable models use the
/// selected independent evaluator input. Unsatisfiable cores must be
/// subset-minimal.
fn check_units(
    units: &[WorkUnit<'_>],
    input: &Input<'_>,
    model_input: ModelInput<'_>,
    expected: bool,
    case: &str,
) -> Vec<SolveOutcome> {
    let engines = [Engine::Dnf, Engine::Direct, Engine::Varisat];
    let outcomes = engines
        .iter()
        .map(|engine| run_engine(*engine, units, input))
        .collect::<Vec<_>>();
    for (engine, outcome) in engines.iter().zip(&outcomes) {
        assert_eq!(
            matches!(outcome, SolveOutcome::Satisfiable(_)),
            expected,
            "{engine:?} has the wrong verdict for:\n{case}"
        );
        match outcome {
            SolveOutcome::Satisfiable(model) => assert!(
                model_holds(model_input, model),
                "{engine:?} model does not hold for:\n{case}"
            ),
            SolveOutcome::Unsatisfiable(core) => {
                let mut rerun = |rest: &[WorkUnit<'_>]| run_engine(*engine, rest, input);
                assert_core_minimal(units, core, &mut rerun);
            }
        }
    }
    outcomes
}

/// Check hand-built canonical formulas under every engine. Each returned
/// model is also checked by the independent evaluator.
pub fn check_canonical(
    declarations: &str,
    input: &Input<'_>,
    formulas: &[AtomFormula],
    expected: bool,
) -> Vec<SolveOutcome> {
    let units = formulas
        .iter()
        .enumerate()
        .map(|(index, formula)| WorkUnit {
            formula,
            label: None,
            span: Span::new(index, index),
        })
        .collect::<Vec<_>>();
    let formula_refs = formulas.iter().collect::<Vec<_>>();
    check_units(
        &units,
        input,
        ModelInput::Canonical {
            declarations,
            input,
            formulas: &formula_refs,
        },
        expected,
        "hand-built canonical formulas",
    )
}

fn check_atom_conjunction(source: &str, expected: bool) {
    let file = validate_ok(source);
    let atoms = work_units(&file)
        .iter()
        .map(|unit| {
            let AtomFormula::Atom(atom) = unit.formula else {
                panic!("theory comparison requires atom-only units");
            };
            *atom
        })
        .collect::<Vec<_>>();
    assert_eq!(
        matches!(
            solve_conjunction(&atoms, &Input::new(&file)),
            TheoryResult::Satisfiable(_)
        ),
        expected,
        "shared theory has the wrong verdict for:\n{source}"
    );
    check_source(source, expected);
}

/// Check one source under all three engines against a hand-derived verdict.
/// Satisfiable results must hold, and unsatisfiable cores must be minimal.
fn check_source(source: &str, expected: bool) {
    let file = validate_ok(source);
    let units = work_units(&file);
    check_units(
        &units,
        &Input::new(&file),
        ModelInput::Source(source),
        expected,
        source,
    );
}

/// Bit 0 is the first source unit. Each rejection mask identifies one smallest
/// failing set of source units.
/// Every subset uses the original solver input. The independent evaluator
/// reparses source with omitted units replaced by a comparison that always holds.
fn check_source_subsets(source: &str, rejections: &[usize]) {
    let file = validate_ok(source);
    let input = Input::new(&file);
    let units = work_units(&file);
    for mask in 0..1 << units.len() {
        let selected = units
            .iter()
            .enumerate()
            .filter(|(index, _)| mask & (1 << index) != 0)
            .map(|(_, unit)| *unit)
            .collect::<Vec<_>>();
        let mut subset = source.to_owned();
        // Later replacements must not change the offsets of earlier units.
        for (index, unit) in units.iter().enumerate().rev() {
            if mask & (1 << index) == 0 {
                subset.replace_range(unit.span.start()..unit.span.end(), "object <: object");
            }
        }
        let expected = !rejections
            .iter()
            .any(|rejection| mask & rejection == *rejection);
        check_units(
            &selected,
            &input,
            ModelInput::Source(&subset),
            expected,
            &format!("source units {mask:b}: {source}"),
        );
    }
}

/// Check one deterministic source model under every engine.
fn check_source_model(source: &str, expected: &str) {
    let file = validate_ok(source);
    let units = work_units(&file);
    for engine in [Engine::Dnf, Engine::Direct, Engine::Varisat] {
        let outcome = run_engine(engine, &units, &Input::new(&file));
        let SolveOutcome::Satisfiable(model) = &outcome else {
            panic!("{engine:?} rejected a satisfiable model fixture");
        };
        assert!(
            model_holds(ModelInput::Source(source), model),
            "{engine:?} model does not hold for: {source}\n{}",
            model.render()
        );
        assert_eq!(outcome.render(source), expected, "{engine:?} model text");
    }
}

fn model_text(outcome: &SolveOutcome) -> String {
    let SolveOutcome::Satisfiable(model) = outcome else {
        panic!("expected a witness");
    };
    model.render()
}
