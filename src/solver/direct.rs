//! Direct search over validated core units.
//!
//! [`run_direct`] expands conjunctions and tries disjunction children in source
//! order. It restores the selected comparisons between attempts and asks the
//! type solver whenever that list changes.
//!
//! Core reduction uses the same search and complete input declarations.
//! Each shorter list starts a new search.

use crate::frontend::problem::{AtomFormula, AtomId};
use crate::solver::input::Input;

use super::theory::{TheoryResult, TheorySolution};
use super::{DirectStats, SharedStats, SolveOutcome, WorkUnit, build_model, check_atoms, minimize};

/// Selected comparisons plus the verdict cached for exactly that list:
/// `proven` holds the accepting witness when the current set already
/// proved satisfiable, and is empty otherwise. Any change to the set
/// clears it; only an unchanged set keeps it.
#[derive(Debug, Default)]
struct SearchState {
    active: Vec<AtomId>,
    proven: Option<TheorySolution>,
}

/// Run the direct engine over all units using the class declarations in the input. Search
/// the unit formulas left to right, build the first accepting
/// branch's model, and minimize a core over units when no branch
/// succeeds. Counts entered branches, backtracks, and every theory
/// call into the statistics, including minimization work. Logs one
/// INFO summary of the initial search; minimization work appears
/// only in the statistics totals.
pub fn run_direct(
    units: &[WorkUnit<'_>],
    input: &Input,
    engine: &mut DirectStats,
    shared: &mut SharedStats,
) -> SolveOutcome {
    let formulas: Vec<&AtomFormula> = units.iter().map(|unit| unit.formula).collect();
    let mut state = SearchState::default();
    let found = search(&formulas, &[], &mut state, input, engine, shared);
    tracing::info!(
        branch_attempts = engine.branch_attempts,
        backtracks = engine.backtracks,
        "direct search complete"
    );
    if let Some(solution) = found {
        tracing::debug!("direct search found a model");
        SolveOutcome::Satisfiable(build_model(input.declarations(), solution))
    } else {
        tracing::debug!("direct search found no model; minimizing a core");
        let mut check = |formulas: &[&AtomFormula]| {
            let mut state = SearchState::default();
            search(formulas, &[], &mut state, input, engine, shared).is_some()
        };
        SolveOutcome::Unsatisfiable(minimize(units, &mut check))
    }
}

/// Search pending formulas against the active set, returning the
/// accepting witness. Each call owns its pending slice: conjunctions
/// expand in place, atoms process immediately, and the first queued
/// disjunction branches against the rest. Newly queued branches
/// precede the outer `queued` ones, preserving source order because
/// the pending child precedes the remaining outer work.
fn search<'a>(
    pending: &[&'a AtomFormula],
    queued: &[&'a [AtomFormula]],
    state: &mut SearchState,
    input: &Input,
    engine: &mut DirectStats,
    shared: &mut SharedStats,
) -> Option<TheorySolution> {
    let mut found: Vec<&'a [AtomFormula]> = Vec::new();
    for formula in pending {
        expand_one(formula, &mut found, state, input, shared)?;
    }
    let mut all: Vec<&'a [AtomFormula]> = Vec::with_capacity(found.len() + queued.len());
    all.extend(found);
    all.extend(queued.iter().copied());
    let [first, rest @ ..] = all.as_slice() else {
        return finish(state, input, shared);
    };
    for child in *first {
        engine.branch_attempts += 1;
        let saved = state.active.len();
        if let Some(solution) = search(&[child], rest, state, input, engine, shared) {
            return Some(solution);
        }
        engine.backtracks += 1;
        if state.active.len() > saved {
            state.active.truncate(saved);
            state.proven = None;
        }
        tracing::debug!("branch failed; rolled back");
    }
    None
}

/// Expand one pending formula: atoms process immediately,
/// conjunctions expand in place, disjunctions queue in source order.
/// Returns `None` when an added atom refutes the branch.
fn expand_one<'a>(
    formula: &'a AtomFormula,
    branches: &mut Vec<&'a [AtomFormula]>,
    state: &mut SearchState,
    input: &Input,
    shared: &mut SharedStats,
) -> Option<()> {
    match formula {
        AtomFormula::Atom(atom) => {
            add_atom(state, *atom, input, shared)?;
        }
        AtomFormula::Conjunction(children) => {
            for child in children {
                expand_one(child, branches, state, input, shared)?;
            }
        }
        AtomFormula::Disjunction(children) => {
            branches.push(children);
        }
    }
    Some(())
}

/// Add one atom to the active set, asking the theory when the set
/// changed. A duplicate leaves the set and the cache untouched.
/// Returns `None` when the grown set is unsatisfiable.
fn add_atom(
    state: &mut SearchState,
    atom: AtomId,
    input: &Input,
    shared: &mut SharedStats,
) -> Option<()> {
    if state.active.contains(&atom) {
        return Some(());
    }
    state.active.push(atom);
    state.proven = None;
    match check_atoms(&state.active, input, shared) {
        TheoryResult::Satisfiable(solution) => {
            state.proven = Some(solution);
            Some(())
        }
        TheoryResult::Unsatisfiable => None,
    }
}

/// Decide the current branch: reuse the cached witness when the active
/// set already proved satisfiable, else ask the theory once. The
/// single call also covers the atom-free formula.
fn finish(
    state: &mut SearchState,
    input: &Input,
    shared: &mut SharedStats,
) -> Option<TheorySolution> {
    if let Some(solution) = state.proven.take() {
        return Some(solution);
    }
    match check_atoms(&state.active, input, shared) {
        TheoryResult::Satisfiable(solution) => Some(solution),
        TheoryResult::Unsatisfiable => None,
    }
}

#[cfg(test)]
mod tests {
    use super::super::dnf::run_dnf;
    use super::super::{
        DirectStats, DnfStats, ModelInput, SharedStats, SolveOutcome, WorkUnit,
        assert_core_minimal, model_holds, validate_ok, work_units,
    };
    use super::run_direct;
    use crate::frontend::problem::{AtomFormula, ClassType, TypeNode};
    use crate::solver::input::Input;
    use crate::solver::test_support::{atom, atom_id, fixture_problem, unit};

    /// Run the direct driver over units, returning the outcome with
    /// its statistics for exact counter assertions.
    fn run_with_stats(
        units: &[WorkUnit<'_>],
        input: &Input<'_>,
    ) -> (SolveOutcome, DirectStats, SharedStats) {
        let mut engine = DirectStats::default();
        let mut shared = SharedStats::default();
        let outcome = run_direct(units, input, &mut engine, &mut shared);
        (outcome, engine, shared)
    }

    #[test]
    fn first_branch_wins_with_its_own_model() {
        let (mut problem, a, b, t) = fixture_problem();
        let first = atom(
            &mut problem,
            TypeNode::Class(ClassType::plain(a)),
            TypeNode::Flexible(t),
        );
        let second = atom(
            &mut problem,
            TypeNode::Class(ClassType::plain(b)),
            TypeNode::Flexible(t),
        );
        let formula = AtomFormula::Disjunction(vec![first, second]);
        let units = [unit(&formula)];
        let (outcome, engine, shared) = run_with_stats(&units, &Input::fixture(&problem));
        let SolveOutcome::Satisfiable(model) = &outcome else {
            panic!("expected the first branch to satisfy");
        };
        let [entry] = model.entries() else {
            panic!("expected one entry");
        };
        assert_eq!(entry.metavar(), "T");
        assert_eq!(entry.value().render(), "a");
        assert_eq!(engine.branch_attempts(), 1);
        assert_eq!(engine.backtracks(), 0);
        assert_eq!(shared.theory_calls(), 1);
        let dnf = run_dnf(
            &units,
            &Input::fixture(&problem),
            &mut DnfStats::default(),
            &mut SharedStats::default(),
        );
        assert_eq!(outcome, dnf);
    }

    #[test]
    fn rollback_retries_a_different_set_at_the_same_length() {
        let (mut problem, a, b, t) = fixture_problem();
        let failing = atom(
            &mut problem,
            TypeNode::Class(ClassType::plain(a)),
            TypeNode::Class(ClassType::plain(b)),
        );
        let later = atom(
            &mut problem,
            TypeNode::Class(ClassType::plain(b)),
            TypeNode::Flexible(t),
        );
        let formula = AtomFormula::Disjunction(vec![failing, later]);
        let units = [unit(&formula)];
        let (outcome, engine, shared) = run_with_stats(&units, &Input::fixture(&problem));
        let SolveOutcome::Satisfiable(model) = &outcome else {
            panic!("expected the later branch to satisfy");
        };
        let [entry] = model.entries() else {
            panic!("expected one entry");
        };
        assert_eq!(entry.value().render(), "b");
        assert_eq!(engine.branch_attempts(), 2);
        assert_eq!(engine.backtracks(), 1);
        // A length-keyed cache would answer the second length-1 set
        // from the first branch's refutation without asking the
        // theory; the second call proves the set was rechecked.
        assert_eq!(shared.theory_calls(), 2);
    }

    #[test]
    fn nested_disjunctions_follow_cartesian_order() {
        // DNF terms in order: A/C (unsat), A/D (sat, T=dog),
        // B/C (sat, T=never), B/D. The search must stop at the
        // second term; the third term's different model proves a
        // wrong order cannot pass by coincidence.
        let source = "class animal;\nclass dog extends animal;\nclass cat extends animal;\nclass bird;\nmetavar ?T;\nmetavar ?U;\nassert (dog <: ?T or bird <: ?U) and ((?T <: cat) or (?T <: animal));";
        let file = validate_ok(source);
        let units = work_units(&file);
        let (outcome, engine, shared) = run_with_stats(&units, &Input::new(&file));
        let SolveOutcome::Satisfiable(model) = &outcome else {
            panic!("expected the second DNF term to satisfy");
        };
        let [first, second] = model.entries() else {
            panic!("expected two entries");
        };
        assert_eq!(first.value().render(), "dog");
        assert_eq!(second.value().render(), "unconstrained");
        assert_eq!(engine.branch_attempts(), 3);
        assert_eq!(engine.backtracks(), 1);
        assert_eq!(shared.theory_calls(), 3);
        assert!(model_holds(ModelInput::Source(source), model));
    }

    #[test]
    fn duplicate_only_alternative_reuses_the_cache() {
        let (mut problem, a, b, t) = fixture_problem();
        let shared_id = atom_id(
            &mut problem,
            TypeNode::Class(ClassType::plain(a)),
            TypeNode::Flexible(t),
        );
        let leaf = || AtomFormula::Atom(shared_id);
        let atom_b = atom(
            &mut problem,
            TypeNode::Class(ClassType::plain(b)),
            TypeNode::Flexible(t),
        );
        let formula =
            AtomFormula::Conjunction(vec![leaf(), AtomFormula::Disjunction(vec![leaf(), atom_b])]);
        let units = [unit(&formula)];
        let (outcome, engine, shared) = run_with_stats(&units, &Input::fixture(&problem));
        assert!(
            matches!(outcome, SolveOutcome::Satisfiable(_)),
            "expected the duplicate branch to satisfy"
        );
        assert_eq!(engine.branch_attempts(), 1);
        assert_eq!(engine.backtracks(), 0);
        assert_eq!(shared.theory_calls(), 1);
    }

    #[test]
    fn unsat_core_is_minimal() {
        let file = validate_ok(
            "class animal;\nclass dog extends animal;\nclass cat extends animal;\nmetavar ?T;\nassert dog <: ?T;\nassert ?T <: cat;",
        );
        let units = work_units(&file);
        let (outcome, _, _) = run_with_stats(&units, &Input::new(&file));
        let dnf = run_dnf(
            &units,
            &Input::new(&file),
            &mut DnfStats::default(),
            &mut SharedStats::default(),
        );
        assert!(
            matches!(dnf, SolveOutcome::Unsatisfiable(_)),
            "dnf verdict differs"
        );
        let SolveOutcome::Unsatisfiable(core) = &outcome else {
            panic!("expected an unsatisfiable core");
        };
        assert_eq!(core.units().len(), 2);
        let mut rerun = |rest: &[WorkUnit<'_>]| {
            run_direct(
                rest,
                &Input::new(&file),
                &mut DirectStats::default(),
                &mut SharedStats::default(),
            )
        };
        assert_core_minimal(&units, core, &mut rerun);
    }

    #[test]
    fn empty_connectives_follow_their_equations() {
        let (problem, _, _, _) = fixture_problem();
        let empty_conjunction = AtomFormula::Conjunction(vec![]);
        let units = [unit(&empty_conjunction)];
        let (outcome, _, _) = run_with_stats(&units, &Input::fixture(&problem));
        assert!(
            matches!(outcome, SolveOutcome::Satisfiable(_)),
            "expected the empty conjunction to satisfy"
        );
        let empty_disjunction = AtomFormula::Disjunction(vec![]);
        let units = [unit(&empty_disjunction)];
        let (outcome, _, _) = run_with_stats(&units, &Input::fixture(&problem));
        assert!(
            matches!(outcome, SolveOutcome::Unsatisfiable(_)),
            "expected the empty disjunction to fail"
        );
        let nested = AtomFormula::Conjunction(vec![AtomFormula::Disjunction(vec![])]);
        let units = [unit(&nested)];
        let (outcome, _, _) = run_with_stats(&units, &Input::fixture(&problem));
        assert!(
            matches!(outcome, SolveOutcome::Unsatisfiable(_)),
            "expected the nested empty disjunction to fail"
        );
        let sat_nested = AtomFormula::Disjunction(vec![
            AtomFormula::Conjunction(vec![]),
            AtomFormula::Disjunction(vec![]),
        ]);
        let units = [unit(&sat_nested)];
        let (outcome, _, _) = run_with_stats(&units, &Input::fixture(&problem));
        assert!(
            matches!(outcome, SolveOutcome::Satisfiable(_)),
            "expected the empty-conjunction alternative to satisfy"
        );
        // No assertions: one empty-set theory call on the model path.
        let (outcome, _, shared) = run_with_stats(&[], &Input::fixture(&problem));
        assert!(
            matches!(outcome, SolveOutcome::Satisfiable(_)),
            "expected no assertions to satisfy"
        );
        assert_eq!(shared.theory_calls(), 1);
        assert_eq!(shared.peak_activated_atoms(), 0);
    }

    #[test]
    fn reported_model_satisfies_its_source_formula() {
        let source = "class animal;\nclass dog extends animal;\nclass cat extends animal;\nmetavar ?T;\nassert (dog <: ?T) and ((?T <: cat) or (?T <: animal));";
        let file = validate_ok(source);
        let units = work_units(&file);
        let (outcome, _, _) = run_with_stats(&units, &Input::new(&file));
        let SolveOutcome::Satisfiable(model) = &outcome else {
            panic!("expected the second branch to satisfy");
        };
        let [entry] = model.entries() else {
            panic!("expected one entry");
        };
        assert_eq!(entry.value().render(), "dog");
        assert!(model_holds(ModelInput::Source(source), model));
    }
}
