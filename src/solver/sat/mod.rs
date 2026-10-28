//! Lazy SAT search over validated core units.
//!
//! [`encode_fragment`] uses Plaisted--Greenbaum constraints. A conjunction
//! helper implies each child. A disjunction helper implies at least one child.
//! The input has no Boolean negation, so only these forward implications are
//! needed. A synthetic root requires every core unit.
//!
//! The encoding stores native varisat literals. Each distinct source atom owns
//! one positive literal. Sources allocate at first occurrence, compound helpers
//! after their children, and the root last.
//!
//! [`solve_fragment`] loads the clauses into one incremental solver. It checks
//! each positive source activation against the shared theory. A rejection adds
//! one clause that forbids that complete activation. Clauses remain across
//! solver calls. Each activation contains each atom at most once.
//!
//! [`run_varisat`] checks the whole input and returns the first accepted model.
//! If no activation holds, it minimizes a core with [`minimize`]. Model creation
//! and theory checks use the shared [`build_model`] and [`check_atoms`] functions.

use std::collections::BTreeSet;

use varisat::{CnfFormula, ExtendFormula, Lit, Solver};

use crate::frontend::problem::{AtomFormula, AtomId};
use crate::solver::input::Input;

use super::theory::{TheoryResult, TheorySolution};
use super::{SatStats, SharedStats, SolveOutcome, WorkUnit, build_model, check_atoms, minimize};

/// One source atom and its positive literal, in first-occurrence order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct SourceAtom {
    atom: AtomId,
    literal: Lit,
}

/// Plaisted--Greenbaum encoding with source records and stable allocation order.
///
/// Sources allocate at first occurrence. Compounds allocate after their children.
/// The synthetic root allocates last. Clauses stay in emission order.
#[derive(Debug, Default)]
struct Encoder {
    sources: Vec<SourceAtom>,
    formula: CnfFormula,
}

impl Encoder {
    /// Encode one formula, returning its representative literal: the
    /// positive literal of its source variable for atoms, a fresh
    /// auxiliary variable implying its definition for connectives.
    fn encode(&mut self, formula: &AtomFormula) -> Lit {
        match formula {
            AtomFormula::Atom(atom) => {
                if let Some(source) = self.sources.iter().find(|source| source.atom == *atom) {
                    return source.literal;
                }
                let literal = self.formula.new_lit();
                self.sources.push(SourceAtom {
                    atom: *atom,
                    literal,
                });
                literal
            }
            AtomFormula::Conjunction(children) => {
                let child_lits: Vec<Lit> =
                    children.iter().map(|child| self.encode(child)).collect();
                self.conjunction(&child_lits)
            }
            AtomFormula::Disjunction(children) => {
                let child_lits: Vec<Lit> =
                    children.iter().map(|child| self.encode(child)).collect();
                self.disjunction(&child_lits)
            }
        }
    }

    /// Constrain a fresh auxiliary variable to imply the conjunction
    /// of `children`: each child follows from the variable. The
    /// reverse direction is unnecessary because every compound
    /// occurs at positive polarity only, so only the forward
    /// Plaisted--Greenbaum implication is emitted. With no children
    /// the implication is vacuous and no clause is emitted.
    fn conjunction(&mut self, children: &[Lit]) -> Lit {
        let literal = self.formula.new_lit();
        for child in children {
            self.formula.add_clause(&[!literal, *child]);
        }
        literal
    }

    /// Constrain a fresh auxiliary variable to imply the disjunction
    /// of `children`, mirroring [`Encoder::conjunction`]. With no
    /// children the variable is constant false.
    fn disjunction(&mut self, children: &[Lit]) -> Lit {
        let literal = self.formula.new_lit();
        let mut clause = vec![!literal];
        clause.extend_from_slice(children);
        self.formula.add_clause(&clause);
        literal
    }
}

/// Encode the whole fragment: one representative per formula under a
/// synthetic root conjunction, then the root assertion. Returns the
/// source records and every generated clause in emission order.
fn encode_fragment(formulas: &[&AtomFormula]) -> Encoder {
    let mut encoder = Encoder::default();
    let mut unit_lits = Vec::with_capacity(formulas.len());
    for formula in formulas {
        unit_lits.push(encoder.encode(formula));
    }
    let root = encoder.conjunction(&unit_lits);
    encoder.formula.add_clause(&[root]);
    encoder
}

/// Blocking clause for one rejected activation: every active source
/// variable negated, in activation order. An empty activation yields
/// the empty clause, which reads as false.
fn lemma_clause(active: &[SourceAtom]) -> Vec<Lit> {
    active.iter().map(|source| !source.literal).collect()
}

/// Outcome of one complete encode-plus-loop check: the accepting
/// witness with this instance's variable and generated-clause counts.
/// `None` means the instance is unsatisfiable under the theory.
struct Fragment {
    solution: Option<TheorySolution>,
    vars: usize,
    clauses: usize,
}

/// Read the source comparisons marked true in one SAT assignment.
/// Keep their stored order. A comparison is selected only when its positive
/// literal appears in the assignment. Helper and omitted variables add no comparison.
fn activation(model: &[Lit], sources: &[SourceAtom]) -> Vec<SourceAtom> {
    let model: BTreeSet<Lit> = model.iter().copied().collect();
    sources
        .iter()
        .filter(|source| model.contains(&source.literal))
        .copied()
        .collect()
}

/// Run one complete encode-plus-loop check over a formula list: the
/// encoding, then solve, read the activation, and
/// check it against the theory until an activation holds or the
/// instance goes unsatisfiable. Counts every generated clause,
/// solver call, theory lemma, and theory call into the statistics;
/// never minimizes. An empty formula list takes the degenerate path:
/// no variables, no clauses, no solver calls, one theory check of
/// the empty activation.
///
/// # Panics
///
/// Panics if varisat returns an internal error or no model for a satisfiable
/// result. Also panics if the theory rejects the empty activation.
fn solve_fragment(
    formulas: &[&AtomFormula],
    input: &Input,
    engine: &mut SatStats,
    shared: &mut SharedStats,
) -> Fragment {
    if formulas.is_empty() {
        let TheoryResult::Satisfiable(solution) = check_atoms(&[], input, shared) else {
            panic!("theory rejected the empty activation");
        };
        return Fragment {
            solution: Some(solution),
            vars: 0,
            clauses: 0,
        };
    }
    let encoding = encode_fragment(formulas);
    let vars = encoding.formula.var_count();
    let clauses = encoding.formula.len();
    engine.generated_clauses += clauses;
    let mut instance = Solver::new();
    // Register every user variable before loading any clause. Keep this order
    // to preserve deterministic models and SAT counters.
    for _ in 0..vars {
        instance.new_var();
    }
    instance.add_formula(&encoding.formula);
    loop {
        engine.sat_calls += 1;
        match instance.solve() {
            Ok(true) => {}
            Ok(false) => {
                tracing::debug!("instance unsatisfiable under accumulated lemmas");
                return Fragment {
                    solution: None,
                    vars,
                    clauses,
                };
            }
            Err(error) => panic!("varisat solver failed: {error:?}"),
        }
        let Some(model) = instance.model() else {
            panic!("varisat reported satisfiable without a model");
        };
        let active = activation(&model, &encoding.sources);
        let atoms: Vec<AtomId> = active.iter().map(|source| source.atom).collect();
        match check_atoms(&atoms, input, shared) {
            TheoryResult::Satisfiable(solution) => {
                tracing::debug!(atoms = atoms.len(), "activation accepted");
                return Fragment {
                    solution: Some(solution),
                    vars,
                    clauses,
                };
            }
            TheoryResult::Unsatisfiable => {
                tracing::debug!(atoms = atoms.len(), "activation rejected; adding lemma");
                let lemma = lemma_clause(&active);
                engine.theory_lemmas += 1;
                instance.add_clause(&lemma);
            }
        }
    }
}

/// Run the lazy-SAT engine over all units using the class declarations in the input. Run one
/// complete encode-plus-loop check, then the first accepting
/// activation's model or a minimized core. The encoding summary
/// covers the initial instance only; every counter includes
/// minimization re-checks.
pub fn run_varisat(
    units: &[WorkUnit<'_>],
    input: &Input,
    engine: &mut SatStats,
    shared: &mut SharedStats,
) -> SolveOutcome {
    let formulas: Vec<&AtomFormula> = units.iter().map(|unit| unit.formula).collect();
    let fragment = solve_fragment(&formulas, input, engine, shared);
    tracing::info!(
        variables = fragment.vars,
        clauses = fragment.clauses,
        "encoded SAT instance"
    );
    if let Some(solution) = fragment.solution {
        SolveOutcome::Satisfiable(build_model(input.declarations(), solution))
    } else {
        tracing::debug!("initial instance unsatisfiable; minimizing a core");
        let mut check = |remaining: &[&AtomFormula]| {
            solve_fragment(remaining, input, engine, shared)
                .solution
                .is_some()
        };
        SolveOutcome::Unsatisfiable(minimize(units, &mut check))
    }
}

#[cfg(test)]
mod tests {
    use crate::frontend::test_support::{RawProblem, lookup_class, lookup_metavar};
    use varisat::{CnfFormula, Lit};

    use super::{SourceAtom, activation, encode_fragment, lemma_clause, run_varisat};
    use crate::frontend::problem::{AtomFormula, ClassType, TypeNode};
    use crate::solver::dnf::run_dnf;
    use crate::solver::input::Input;
    use crate::solver::test_support::{FIXTURE_DECLARATIONS, atom, atom_id, fixture_problem, unit};
    use crate::solver::{
        DnfStats, ModelInput, SatStats, SharedStats, SolveOutcome, WorkUnit, assert_core_minimal,
        model_holds, validate_ok, work_units,
    };

    #[test]
    fn pg_conjunction_shape() {
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
        let formula = AtomFormula::Conjunction(vec![first, second]);
        let encoding = encode_fragment(&[&formula]);
        let [lit_a, lit_b, compound, root] = [0, 1, 2, 3].map(|index| Lit::from_index(index, true));
        // Positive-only polarity needs just the forward implication:
        // no reverse clause constrains the variable from its children.
        assert_eq!(
            encoding.formula,
            CnfFormula::from(vec![
                vec![!compound, lit_a],
                vec![!compound, lit_b],
                vec![!root, compound],
                vec![root],
            ])
        );
    }

    #[test]
    fn pg_disjunction_shape() {
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
        let encoding = encode_fragment(&[&formula]);
        let [lit_a, lit_b, compound, root] = [0, 1, 2, 3].map(|index| Lit::from_index(index, true));
        assert_eq!(
            encoding.formula,
            CnfFormula::from(vec![
                vec![!compound, lit_a, lit_b],
                vec![!root, compound],
                vec![root],
            ])
        );
    }

    #[test]
    fn pg_empty_connectives_shape() {
        let empty_and = AtomFormula::Conjunction(Vec::new());
        let empty_or = AtomFormula::Disjunction(Vec::new());
        let encoding = encode_fragment(&[&empty_and, &empty_or]);
        let [truthy, falsy, root] = [0, 1, 2].map(|index| Lit::from_index(index, true));
        // The empty conjunction's forward implication is vacuous, so
        // its variable floats unconstrained; the empty disjunction
        // still asserts its own negation.
        assert_eq!(
            encoding.formula,
            CnfFormula::from(vec![
                vec![!falsy],
                vec![!root, truthy],
                vec![!root, falsy],
                vec![root],
            ])
        );
    }

    #[test]
    fn shared_atoms_reuse_one_variable() {
        let (mut problem, a, _, t) = fixture_problem();
        let first = atom(
            &mut problem,
            TypeNode::Class(ClassType::plain(a)),
            TypeNode::Flexible(t),
        );
        let second = atom(
            &mut problem,
            TypeNode::Class(ClassType::plain(a)),
            TypeNode::Flexible(t),
        );
        let formula = AtomFormula::Disjunction(vec![first, second]);
        let encoding = encode_fragment(&[&formula]);
        assert_eq!(encoding.formula.var_count(), 3);
        assert_eq!(encoding.sources.len(), 1);
    }

    #[test]
    fn activation_and_lemma_use_positive_sources_in_order() {
        let (mut problem, a, b, t) = fixture_problem();
        let one = atom_id(
            &mut problem,
            TypeNode::Class(ClassType::plain(a)),
            TypeNode::Flexible(t),
        );
        let other = atom_id(
            &mut problem,
            TypeNode::Flexible(t),
            TypeNode::Class(ClassType::plain(b)),
        );
        let third = atom_id(
            &mut problem,
            TypeNode::Class(ClassType::plain(b)),
            TypeNode::Flexible(t),
        );
        let sources = [
            SourceAtom {
                atom: one,
                literal: Lit::from_index(0, true),
            },
            SourceAtom {
                atom: third,
                literal: Lit::from_index(1, true),
            },
            SourceAtom {
                atom: other,
                literal: Lit::from_index(3, true),
            },
        ];
        let model = [
            sources[2].literal,
            Lit::from_index(2, true),
            !sources[0].literal,
            sources[1].literal,
        ];
        let active = activation(&model, &sources);
        assert_eq!(active, [sources[1], sources[2]]);
        assert_eq!(
            lemma_clause(&active),
            vec![Lit::from_index(1, false), Lit::from_index(3, false)]
        );
        assert!(activation(&[], &sources).is_empty());
        assert!(lemma_clause(&[]).is_empty());
    }

    /// Run the varisat driver over units, returning the outcome with
    /// its statistics for exact counter assertions.
    fn run_with_stats(
        units: &[WorkUnit<'_>],
        input: &Input<'_>,
    ) -> (SolveOutcome, SatStats, SharedStats) {
        let mut engine = SatStats::default();
        let mut shared = SharedStats::default();
        let outcome = run_varisat(units, input, &mut engine, &mut shared);
        (outcome, engine, shared)
    }

    #[test]
    fn lazy_loop_rejects_once_then_proves_unsat() {
        let (mut problem, a, b, t) = fixture_problem();
        let lower = atom(
            &mut problem,
            TypeNode::Class(ClassType::plain(a)),
            TypeNode::Flexible(t),
        );
        let upper = atom(
            &mut problem,
            TypeNode::Flexible(t),
            TypeNode::Class(ClassType::plain(b)),
        );
        let formula = AtomFormula::Conjunction(vec![lower, upper]);
        let units = [unit(&formula)];
        // Unrelated classes: each bound alone holds, the pair cannot.
        let (outcome, engine, shared) = run_with_stats(&units, &Input::fixture(&problem));
        let SolveOutcome::Unsatisfiable(core) = &outcome else {
            panic!("expected an unsatisfiable core");
        };
        assert_eq!(core.units().len(), 1);
        // Four initial clauses, two solver calls around one lemma; the
        // single-unit minimization re-checks the empty remainder with
        // one more theory call and no new clauses.
        assert_eq!(engine.generated_clauses(), 4);
        assert_eq!(engine.sat_calls(), 2);
        assert_eq!(engine.theory_lemmas(), 1);
        assert_eq!(shared.theory_calls(), 2);
        assert_eq!(shared.activated_atoms_sum(), 2);
        assert_eq!(shared.peak_activated_atoms(), 2);
    }

    #[test]
    fn model_matches_accepting_activation() {
        let declarations = "class a extends b; class b; metavar ?T;";
        let mut problem = RawProblem::new(declarations);
        let (a, b, t) = (
            lookup_class(&problem.declarations, "a"),
            lookup_class(&problem.declarations, "b"),
            lookup_metavar(&problem.declarations, "T"),
        );
        let lower = atom(
            &mut problem,
            TypeNode::Class(ClassType::plain(a)),
            TypeNode::Flexible(t),
        );
        let upper = atom(
            &mut problem,
            TypeNode::Flexible(t),
            TypeNode::Class(ClassType::plain(b)),
        );
        let formula = AtomFormula::Conjunction(vec![lower, upper]);
        let units = [unit(&formula)];
        let (outcome, engine, shared) = run_with_stats(&units, &Input::fixture(&problem));
        let SolveOutcome::Satisfiable(model) = &outcome else {
            panic!("expected a model");
        };
        assert!(model_holds(
            ModelInput::Canonical {
                declarations,
                input: &Input::fixture(&problem),
                formulas: &[&formula],
            },
            model,
        ));
        assert_eq!(engine.sat_calls(), 1);
        assert_eq!(engine.theory_lemmas(), 0);
        assert_eq!(shared.theory_calls(), 1);
    }

    #[test]
    fn unsat_core_is_minimal_with_exact_totals() {
        let file = validate_ok(
            "class animal;\nclass dog extends animal;\nclass cat extends animal;\nmetavar ?T;\nassert dog <: ?T;\nassert ?T <: cat;",
        );
        let units = work_units(&file);
        let (outcome, engine, shared) = run_with_stats(&units, &Input::new(&file));
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
            run_varisat(
                rest,
                &Input::new(&file),
                &mut SatStats::default(),
                &mut SharedStats::default(),
            )
        };
        assert_core_minimal(&units, core, &mut rerun);
        // Three initial clauses and two solver calls around one lemma;
        // each minimization remainder re-encodes two clauses with
        // one solver call and one single-atom theory check.
        assert_eq!(engine.generated_clauses(), 7);
        assert_eq!(engine.sat_calls(), 4);
        assert_eq!(engine.theory_lemmas(), 1);
        assert_eq!(shared.theory_calls(), 3);
        assert_eq!(shared.activated_atoms_sum(), 4);
        assert_eq!(shared.peak_activated_atoms(), 2);
    }

    #[test]
    fn empty_disjunction_unit_is_unsatisfiable() {
        let (problem, _, _, _) = fixture_problem();
        let formula = AtomFormula::Disjunction(Vec::new());
        let units = [unit(&formula)];
        let (outcome, engine, shared) = run_with_stats(&units, &Input::fixture(&problem));
        let SolveOutcome::Unsatisfiable(core) = &outcome else {
            panic!("expected an unsatisfiable core");
        };
        assert_eq!(core.units().len(), 1);
        // The false unit conflicts with the root assertion on the
        // first solve: one emission pass of three clauses, one solver call, no
        // lemmas, and the single-unit minimization re-checks the
        // empty remainder once.
        assert_eq!(engine.generated_clauses(), 3);
        assert_eq!(engine.sat_calls(), 1);
        assert_eq!(engine.theory_lemmas(), 0);
        assert_eq!(shared.theory_calls(), 1);
        assert_eq!(shared.activated_atoms_sum(), 0);
        assert_eq!(shared.peak_activated_atoms(), 0);
    }

    #[test]
    fn empty_conjunction_unit_is_satisfiable() {
        let (problem, _, _, _) = fixture_problem();
        let formula = AtomFormula::Conjunction(Vec::new());
        let units = [unit(&formula)];
        let (outcome, engine, shared) = run_with_stats(&units, &Input::fixture(&problem));
        let SolveOutcome::Satisfiable(model) = &outcome else {
            panic!("expected a model");
        };
        assert!(model_holds(
            ModelInput::Canonical {
                declarations: FIXTURE_DECLARATIONS,
                input: &Input::fixture(&problem),
                formulas: &[&formula],
            },
            model,
        ));
        assert_eq!(engine.generated_clauses(), 2);
        assert_eq!(engine.sat_calls(), 1);
        assert_eq!(engine.theory_lemmas(), 0);
        assert_eq!(shared.theory_calls(), 1);
        assert_eq!(shared.activated_atoms_sum(), 0);
        assert_eq!(shared.peak_activated_atoms(), 0);
    }

    #[test]
    fn empty_units_take_the_degenerate_path() {
        let (problem, _, _, _) = fixture_problem();
        let (outcome, engine, shared) = run_with_stats(&[], &Input::fixture(&problem));
        let SolveOutcome::Satisfiable(_) = &outcome else {
            panic!("expected the empty conjunction to satisfy");
        };
        assert_eq!(engine.generated_clauses(), 0);
        assert_eq!(engine.sat_calls(), 0);
        assert_eq!(engine.theory_lemmas(), 0);
        assert_eq!(shared.theory_calls(), 1);
        assert_eq!(shared.activated_atoms_sum(), 0);
        assert_eq!(shared.peak_activated_atoms(), 0);
    }
}
