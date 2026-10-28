//! Boolean engine entry points, reports, and core reduction.
//!
//! Solve a [`ValidatedFile`] produced by the frontend with one of three engines:
//!
//! - [`solve_dnf`] expands formulas into conjunctions before checking them.
//! - [`solve_direct`] searches the formula tree and checks its selected comparisons.
//! - [`solve_varisat`] encodes Boolean choices and checks the comparisons marked true.
//!
//! Each entry point returns a [`SolveReport`] with a [`SolveOutcome`], shared work
//! counters, and engine counters. Counters include core reduction. Elapsed time
//! can differ between runs.
//!
//! A satisfiable result contains a valid [`Model`]. An unsatisfiable result
//! contains a subset-minimal [`Core`] under the specified search. Search rejection
//! does not exclude models outside that search. All engines agree on the verdict.
//! Models and cores can differ between engines.
//!
//! The `dnf`, `direct`, and `sat` modules implement the Boolean engines. The
//! `theory` module checks each complete list of selected comparisons. The `model`
//! module converts checked solutions to public assignment entries. The `cores`
//! module owns core reduction and construction. Every engine uses the same type
//! checks, model conversion, progress events, and core reduction.
//!
//! Solve calls emit tracing progress events. Rendering methods return text.
//! The caller selects the output stream for results and counters.

mod cores;
mod direct;
mod dnf;
mod input;
mod model;
mod reachability;
mod sat;
#[cfg(test)]
mod test_support;
#[cfg(test)]
mod tests;
mod theory;

use std::time::Instant;

use crate::frontend::Span;
use crate::frontend::ValidatedFile;
use crate::frontend::problem::{AtomFormula, AtomId};
use cores::minimize;
use input::Input;

use self::theory::{TheoryResult, solve_conjunction};
use model::build_model;

#[doc(inline)]
pub use cores::{Core, CoreUnit};
#[doc(inline)]
pub use model::{AssignedNode, AssignedNodeId, AssignedValue, Model, ModelEntry, ModelValue};
#[cfg(test)]
use test_support::{ModelInput, assert_core_minimal, model_holds, validate_ok};

/// Solve one validated file with the eager-DNF engine.
///
/// Reports the verdict, shared work counters, and DNF counters.
#[must_use]
pub fn solve_dnf(file: &ValidatedFile) -> SolveReport<DnfStats> {
    solve(file, dnf::run_dnf)
}

/// Solve one validated file with direct syntax-directed search.
///
/// Reports the verdict, shared work counters, and direct-search
/// counters.
#[must_use]
pub fn solve_direct(file: &ValidatedFile) -> SolveReport<DirectStats> {
    solve(file, direct::run_direct)
}

/// varisat solver identity recorded in `--stats`: crate name and
/// version.
pub const VARISAT_SOLVER: &str = "varisat-0.2.2";

/// Solve one validated file with the varisat-backed lazy-SAT engine.
///
/// Reports the verdict, shared work counters, and SAT counters.
///
/// # Panics
///
/// Panics when the underlying SAT solver reports an internal error
/// or claims satisfiability without a model. It also panics if the type solver
/// rejects an empty list of comparisons. Each case signals a solver bug.
#[must_use]
pub fn solve_varisat(file: &ValidatedFile) -> SolveReport<SatStats> {
    solve(file, sat::run_varisat)
}

/// Collect every flattened core unit of a validated file in source
/// order, with the label and span each core entry reports.
fn work_units(file: &ValidatedFile) -> Vec<WorkUnit<'_>> {
    file.assertions()
        .iter()
        .flat_map(|assertion| {
            assertion.units.iter().map(|unit| WorkUnit {
                formula: &unit.formula,
                label: assertion.label.as_deref(),
                span: unit.span,
            })
        })
        .collect()
}

/// Keep timing, shared counters, and file events identical across engines.
fn solve<S: Default>(
    file: &ValidatedFile,
    run: impl FnOnce(&[WorkUnit<'_>], &Input<'_>, &mut S, &mut SharedStats) -> SolveOutcome,
) -> SolveReport<S> {
    let started = Instant::now();
    let units = work_units(file);
    let mut engine = S::default();
    let mut shared = SharedStats::default();
    tracing::info!(
        assertions = file.assertions().len(),
        units = units.len(),
        metavars = file.declarations().metavar_count(),
        "solving file"
    );
    let outcome = run(&units, &Input::new(file), &mut engine, &mut shared);
    shared.elapsed_ms = u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX);
    tracing::info!(
        verdict = match &outcome {
            SolveOutcome::Satisfiable(_) => "satisfiable",
            SolveOutcome::Unsatisfiable(_) => "unsatisfiable",
        },
        "solved"
    );
    SolveReport {
        outcome,
        shared,
        engine,
    }
}

/// Check one atom conjunction against the input class metadata and count the call:
/// one more theory call, the deduplicated atom count added to the
/// running sum, and the peak updated. Every engine routes every
/// `solve_conjunction` call through here so the shared counters
/// cover minimization as well as the initial search.
fn check_atoms(atoms: &[AtomId], input: &Input, shared: &mut SharedStats) -> TheoryResult {
    shared.theory_calls += 1;
    shared.activated_atoms_sum += atoms.len();
    shared.peak_activated_atoms = shared.peak_activated_atoms.max(atoms.len());
    solve_conjunction(atoms, input)
}

/// Verdict plus work counters for one engine run. The type parameter
/// carries the engine-specific counters, so an engine can only
/// produce its own statistics.
#[derive(Debug)]
pub struct SolveReport<S> {
    outcome: SolveOutcome,
    shared: SharedStats,
    engine: S,
}

impl<S> SolveReport<S> {
    /// The verdict: one model for the first satisfiable branch, or a
    /// subset-minimal core when every branch fails.
    pub fn outcome(&self) -> &SolveOutcome {
        &self.outcome
    }

    /// Engine-neutral work counters for the run.
    #[must_use]
    pub fn shared_stats(&self) -> &SharedStats {
        &self.shared
    }

    /// Engine-specific counters for the run.
    #[must_use]
    pub fn engine_stats(&self) -> &S {
        &self.engine
    }
}

/// DNF counters: the summed final term counts.
#[derive(Debug, Default)]
pub struct DnfStats {
    materialized_terms: usize,
}

impl DnfStats {
    /// Sum of the final term counts returned by each complete
    /// expansion, including minimization re-expansions.
    #[must_use]
    pub fn materialized_terms(&self) -> usize {
        self.materialized_terms
    }
}

/// SAT counters: generated clauses, solver calls, theory lemmas.
#[derive(Debug, Default)]
pub struct SatStats {
    generated_clauses: usize,
    sat_calls: usize,
    theory_lemmas: usize,
}

impl SatStats {
    /// Every clause the encoder emitted, including
    /// minimization re-encodings but excluding theory lemmas.
    #[must_use]
    pub fn generated_clauses(&self) -> usize {
        self.generated_clauses
    }

    /// Every underlying SAT solver call, including minimization
    /// re-checks.
    #[must_use]
    pub fn sat_calls(&self) -> usize {
        self.sat_calls
    }

    /// Every blocking clause added after a rejected activation,
    /// including minimization re-checks.
    #[must_use]
    pub fn theory_lemmas(&self) -> usize {
        self.theory_lemmas
    }
}

/// Direct-search counters: entered branches and abandoned branches.
#[derive(Debug, Default)]
pub struct DirectStats {
    branch_attempts: usize,
    backtracks: usize,
}

impl DirectStats {
    /// Each disjunction child the search entered.
    #[must_use]
    pub fn branch_attempts(&self) -> usize {
        self.branch_attempts
    }

    /// Each failed child attempt that restored branch state.
    #[must_use]
    pub fn backtracks(&self) -> usize {
        self.backtracks
    }
}

/// Engine-neutral work counters for one run, including minimization.
#[derive(Debug, Default)]
pub struct SharedStats {
    theory_calls: usize,
    activated_atoms_sum: usize,
    peak_activated_atoms: usize,
    elapsed_ms: u64,
}

impl SharedStats {
    /// Each actual `solve_conjunction` call.
    #[must_use]
    pub fn theory_calls(&self) -> usize {
        self.theory_calls
    }

    /// Sum of deduplicated atom counts passed to those calls.
    #[must_use]
    pub fn activated_atoms_sum(&self) -> usize {
        self.activated_atoms_sum
    }

    /// Largest deduplicated atom count passed to one call.
    #[must_use]
    pub fn peak_activated_atoms(&self) -> usize {
        self.peak_activated_atoms
    }

    /// The complete selected-engine operation, in milliseconds.
    #[must_use]
    pub fn elapsed_ms(&self) -> u64 {
        self.elapsed_ms
    }
}

/// One flattened core unit under check: the fragment plus the label
/// and span its core entry reports.
#[derive(Debug, Clone, Copy)]
struct WorkUnit<'a> {
    formula: &'a AtomFormula,
    label: Option<&'a str>,
    span: Span,
}

/// Verdict for one solved file: a model on success, a core on failure.
/// The verdict is data on stdout; the exit status only reports whether
/// the tool did its job.
#[derive(Debug, PartialEq, Eq)]
#[must_use]
pub enum SolveOutcome {
    /// The formula holds; the model assigns every metavariable.
    Satisfiable(Model),
    /// Search exhausts every branch without a model. The core is subset-minimal
    /// under the same search and complete input declarations. This does
    /// not exclude models outside the specified search.
    Unsatisfiable(Core),
}

impl SolveOutcome {
    /// Render the verdict for stdout: the verdict line plus the model
    /// or core block. Takes the source text for core line:col entries;
    /// the model needs none.
    #[must_use]
    pub fn render(&self, source: &str) -> String {
        match self {
            Self::Satisfiable(model) => model.render(),
            Self::Unsatisfiable(core) => core.render(source),
        }
    }
}
