//! Eager-DNF Boolean engine over flattened core units plus the driver.
//!
//! [`expand`] materializes one formula into disjunct terms. [`expand_all`]
//! expands conjunction children and flattened core units with the same
//! Cartesian product order. [`run_dnf`] checks each canonicalized term in order
//! with the conjunctive theory and returns the first model, minimizing a core
//! over units when every term fails.
//! Model construction, core minimization, and statistics helpers live
//! in the solver seam.

use crate::frontend::problem::{AtomFormula, AtomId};
use crate::solver::input::Input;

use super::theory::{TheoryResult, TheorySolution};
use super::{DnfStats, SharedStats, SolveOutcome, WorkUnit, build_model, check_atoms, minimize};

/// Expand one formula into materialized DNF terms, each a list of atom
/// identifiers. Conjunctions multiply out with the first child's
/// alternatives varying slowest; disjunctions concatenate. An empty
/// conjunction is one empty term and an empty disjunction is none.
pub fn expand(formula: &AtomFormula) -> Vec<Vec<AtomId>> {
    match formula {
        AtomFormula::Atom(atom) => vec![vec![*atom]],
        AtomFormula::Conjunction(children) => expand_all(children.iter()),
        AtomFormula::Disjunction(children) => {
            let mut terms = Vec::new();
            for child in children {
                terms.extend(expand(child));
            }
            terms
        }
    }
}

/// Expand the conjunction of children into a Cartesian product of terms.
///
/// Earlier children's alternatives vary slowest. An empty child list gives one
/// empty term, so an empty core remains satisfiable. The capacity hint uses
/// checked arithmetic. If it overflows, vector growth supplies the capacity.
fn expand_all<'a, I>(children: I) -> Vec<Vec<AtomId>>
where
    I: IntoIterator<Item = &'a AtomFormula>,
{
    let mut terms = vec![Vec::new()];
    for child in children {
        let child_terms = expand(child);
        let capacity = terms.len().checked_mul(child_terms.len()).unwrap_or(0);
        let mut next = Vec::with_capacity(capacity);
        for term in &terms {
            for child_term in &child_terms {
                let mut joined = term.clone();
                joined.extend_from_slice(child_term);
                next.push(joined);
            }
        }
        terms = next;
    }
    terms
}

/// Deduplicate one term's atoms in first-occurrence order. The result
/// is also the activated set the accepting term reports.
fn canonicalize(mut term: Vec<AtomId>) -> Vec<AtomId> {
    let mut seen = Vec::with_capacity(term.len());
    term.retain(|atom| {
        if seen.contains(atom) {
            false
        } else {
            seen.push(*atom);
            true
        }
    });
    term
}

/// Run the eager-DNF engine over all units with the class declarations in the input:
/// expand every unit, check each canonicalized term in order, and
/// return the first satisfiable term's model or a minimized core.
/// Counts every complete expansion and every theory call into the
/// statistics, including minimization work.
pub fn run_dnf(
    units: &[WorkUnit<'_>],
    input: &Input,
    engine: &mut DnfStats,
    shared: &mut SharedStats,
) -> SolveOutcome {
    let terms = expand_all(units.iter().map(|unit| unit.formula));
    engine.materialized_terms += terms.len();
    tracing::info!(terms = terms.len(), "materialized DNF terms");
    if let Some(solution) = first_solution(terms, input, shared) {
        return SolveOutcome::Satisfiable(build_model(input.declarations(), solution));
    }
    tracing::debug!("every term unsatisfiable; minimizing a core");
    let mut check = |formulas: &[&AtomFormula]| {
        let _span = tracing::debug_span!("core_check", units = formulas.len()).entered();
        let terms = expand_all(formulas.iter().copied());
        engine.materialized_terms += terms.len();
        first_solution(terms, input, shared).is_some()
    };
    SolveOutcome::Unsatisfiable(minimize(units, &mut check))
}

/// Initial search and core checks visit canonical terms in the same order.
fn first_solution(
    terms: Vec<Vec<AtomId>>,
    input: &Input<'_>,
    shared: &mut SharedStats,
) -> Option<TheorySolution> {
    for (index, term) in terms.into_iter().enumerate() {
        let atoms = canonicalize(term);
        if let TheoryResult::Satisfiable(solution) = check_atoms(&atoms, input, shared) {
            tracing::debug!(term = index, "term satisfiable");
            return Some(solution);
        }
        tracing::debug!(term = index, "term unsatisfiable");
    }
    None
}

#[cfg(test)]
mod tests {
    use super::super::theory::TheoryResult;
    use super::super::{
        DnfStats, ModelInput, SharedStats, SolveOutcome, check_atoms, model_holds, validate_ok,
        work_units,
    };
    use super::{WorkUnit, canonicalize, expand, expand_all, run_dnf};
    use crate::frontend::Span;
    use crate::frontend::problem::{AtomFormula, AtomId, ClassType, TypeNode};
    use crate::frontend::test_support::lookup_class;
    use crate::solver::input::Input;
    use crate::solver::test_support::{atom, atom_id, fixture_problem, unit};

    /// Run the DNF driver over units, discarding statistics. Tests
    /// that pin counter values use the public reports instead.
    fn run_units(units: &[WorkUnit<'_>], input: &Input<'_>) -> SolveOutcome {
        run_dnf(
            units,
            input,
            &mut DnfStats::default(),
            &mut SharedStats::default(),
        )
    }

    fn pair_terms(input: &Input<'_>, terms: &[Vec<AtomId>]) -> Vec<Vec<(TypeNode, TypeNode)>> {
        terms
            .iter()
            .map(|term| {
                term.iter()
                    .map(|id| {
                        let atom = input.atoms().atom(*id);
                        (
                            input.types().type_node(atom.lower).clone(),
                            input.types().type_node(atom.upper).clone(),
                        )
                    })
                    .collect()
            })
            .collect()
    }

    #[test]
    fn nested_disjunctions_expand_first_child_slowest() {
        let file = validate_ok(
            "class a;\nclass b;\nclass c;\nclass d;\nclass e;\nclass f;\nclass g;\nclass h;\nassert (a <: b or c <: d) and (e <: f or g <: h);",
        );
        let [assertion] = file.assertions() else {
            panic!("expected one assertion");
        };
        let formulas: Vec<&AtomFormula> =
            assertion.units.iter().map(|unit| &unit.formula).collect();
        assert_eq!(formulas.len(), 2);
        let terms = expand_all(formulas);
        assert_eq!(terms.len(), 4);
        let problem = &Input::new(&file);
        let pair = |first: &str, second: &str| {
            let first = lookup_class(problem.declarations(), first);
            let second = lookup_class(problem.declarations(), second);
            (
                TypeNode::Class(ClassType::plain(first)),
                TypeNode::Class(ClassType::plain(second)),
            )
        };
        assert_eq!(
            pair_terms(problem, &terms),
            [
                [pair("a", "b"), pair("e", "f")],
                [pair("a", "b"), pair("g", "h")],
                [pair("c", "d"), pair("e", "f")],
                [pair("c", "d"), pair("g", "h")],
            ]
        );
    }

    #[test]
    fn empty_connectives_follow_their_equations() {
        assert_eq!(expand(&AtomFormula::Conjunction(vec![])), [Vec::new()]);
        assert_eq!(
            expand(&AtomFormula::Disjunction(vec![])),
            Vec::<Vec<AtomId>>::new()
        );
    }

    #[test]
    fn canonicalization_dedups_repeats_in_order() {
        let (mut problem, a, b, t) = fixture_problem();
        let first = atom_id(
            &mut problem,
            TypeNode::Class(ClassType::plain(a)),
            TypeNode::Flexible(t),
        );
        let second = atom_id(
            &mut problem,
            TypeNode::Class(ClassType::plain(b)),
            TypeNode::Flexible(t),
        );
        assert_eq!(
            canonicalize(vec![first, second, first, second, first]),
            [first, second]
        );
    }

    #[test]
    fn driver_picks_the_first_sat_term() {
        let (mut problem, a, b, t) = fixture_problem();
        let formula = AtomFormula::Disjunction(vec![
            atom(
                &mut problem,
                TypeNode::Class(ClassType::plain(a)),
                TypeNode::Flexible(t),
            ),
            atom(
                &mut problem,
                TypeNode::Class(ClassType::plain(b)),
                TypeNode::Flexible(t),
            ),
        ]);
        let units = [unit(&formula)];
        assert_eq!(
            run_units(&units, &Input::fixture(&problem)).render(""),
            "satisfiable\nmodel:\n  ?T = a\n"
        );
    }

    #[test]
    fn metavar_only_in_unselected_branch_is_unconstrained() {
        let file = validate_ok(
            "class a;\nclass b;\nmetavar ?T;\nmetavar ?U;\nassert (a <: ?T) or (b <: ?U);",
        );
        let units = work_units(&file);
        assert_eq!(
            run_units(&units, &Input::new(&file)).render(""),
            "satisfiable\nmodel:\n  ?T = a\n  ?U = unconstrained\n"
        );
    }

    #[test]
    fn subsumed_union_members_drop() {
        let file = validate_ok(
            "class animal;\nclass dog extends animal;\nmetavar ?T;\nassert dog <: ?T;\nassert animal <: ?T;",
        );
        let units = work_units(&file);
        let SolveOutcome::Satisfiable(model) = run_units(&units, &Input::new(&file)) else {
            panic!("expected related bounds to stay satisfiable");
        };
        let [entry] = model.entries() else {
            panic!("expected one model entry");
        };
        assert_eq!(entry.value().render(), "animal");
    }

    #[test]
    fn union_members_follow_declaration_order() {
        let file = validate_ok(
            "class zebra;\nclass apple;\nmetavar ?T;\nassert zebra <: ?T;\nassert apple <: ?T;",
        );
        let units = work_units(&file);
        let SolveOutcome::Satisfiable(model) = run_units(&units, &Input::new(&file)) else {
            panic!("expected unrelated lowers to stay satisfiable");
        };
        let [entry] = model.entries() else {
            panic!("expected one model entry");
        };
        assert_eq!(entry.value().render(), "zebra | apple");
    }

    #[test]
    fn reported_model_satisfies_its_source_formula() {
        let source = "class animal;\nclass dog extends animal;\nclass cat extends animal;\nmetavar ?T;\nassert (dog <: ?T) and ((?T <: cat) or (?T <: animal));";
        let file = validate_ok(source);
        let units = work_units(&file);
        let SolveOutcome::Satisfiable(model) = run_units(&units, &Input::new(&file)) else {
            panic!("expected the second branch to satisfy");
        };
        let [entry] = model.entries() else {
            panic!("expected one model entry");
        };
        assert_eq!(entry.value().render(), "dog");
        assert!(model_holds(ModelInput::Source(source), &model));
    }

    #[test]
    fn minimization_drops_the_irrelevant_unit() {
        let source = "class animal;\nclass dog extends animal;\nclass cat extends animal;\nmetavar ?T;\nassert needs_dog: dog <: ?T;\nassert needs_cat: ?T <: cat;\nassert irrelevant: object <: object;";
        let file = validate_ok(source);
        let units = work_units(&file);
        assert_eq!(
            run_units(&units, &Input::new(&file)).render(source),
            "unsatisfiable\ncore:\n  needs_dog\n  needs_cat\n"
        );
    }

    #[test]
    fn minimized_core_is_subset_minimal_over_units() {
        let source = "class animal;\nclass dog extends animal;\nclass cat extends animal;\nmetavar ?T;\nassert bad: (dog <: ?T) and (?T <: cat) and (object <: object);";
        let file = validate_ok(source);
        let units = work_units(&file);
        assert_eq!(
            run_units(&units, &Input::new(&file)).render(source),
            "unsatisfiable\ncore:\n  bad (5:14)\n  bad (5:30)\n"
        );
        let [assertion] = file.assertions() else {
            panic!("expected one assertion");
        };
        let formulas: Vec<&AtomFormula> =
            assertion.units.iter().map(|unit| &unit.formula).collect();
        assert_eq!(formulas.len(), 3);
        let mut shared = SharedStats::default();
        let mut remainder_is_sat = |formulas: &[&AtomFormula]| {
            expand_all(formulas.iter().copied())
                .into_iter()
                .map(canonicalize)
                .any(|term| {
                    matches!(
                        check_atoms(&term, &Input::new(&file), &mut shared),
                        TheoryResult::Satisfiable(_)
                    )
                })
        };
        assert!(!remainder_is_sat(&formulas[..2]));
        assert!(remainder_is_sat(&formulas[1..]));
        assert!(remainder_is_sat(&formulas[..1]));
    }

    #[test]
    fn sole_survivor_renders_bare_label_or_location() {
        let source = "class animal;\nclass dog extends animal;\nclass cat extends animal;\nmetavar ?T;\nassert dog <: ?T;\nassert needs_cat: ?T <: cat;";
        let file = validate_ok(source);
        let units = work_units(&file);
        let outcome = run_units(&units, &Input::new(&file));
        assert_eq!(
            outcome.render(source),
            "unsatisfiable\ncore:\n  5:8\n  needs_cat\n"
        );
        let SolveOutcome::Unsatisfiable(core) = &outcome else {
            panic!("expected an unsatisfiable core");
        };
        let [first, second] = core.units() else {
            panic!("expected two core units");
        };
        assert_eq!(first.label(), None);
        assert_eq!(first.span(), Span::new(85, 94));
        assert_eq!(second.label(), Some("needs_cat"));
    }

    #[test]
    fn outcome_exposes_read_accessors() {
        let (mut problem, a, b, t) = fixture_problem();
        let formula = AtomFormula::Disjunction(vec![
            atom(
                &mut problem,
                TypeNode::Class(ClassType::plain(a)),
                TypeNode::Flexible(t),
            ),
            atom(
                &mut problem,
                TypeNode::Class(ClassType::plain(b)),
                TypeNode::Flexible(t),
            ),
        ]);
        let units = [unit(&formula)];
        let outcome = run_units(&units, &Input::fixture(&problem));
        let SolveOutcome::Satisfiable(model) = &outcome else {
            panic!("expected a satisfiable model");
        };
        let [entry] = model.entries() else {
            panic!("expected one entry");
        };
        assert_eq!(entry.metavar(), "T");
        assert_eq!(entry.value().render(), "a");
    }
}
