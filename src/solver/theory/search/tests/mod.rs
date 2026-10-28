//! Shared helpers for scoped search tests.

mod conversions;
mod generics;

use crate::frontend::problem::AtomId;
use crate::solver::input::Input;

use super::super::TheoryResult;
use super::solve_conjunction;

fn solve(input: &Input<'_>, atom: AtomId) -> TheoryResult {
    solve_conjunction(&[atom], input)
}
