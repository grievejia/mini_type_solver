//! Solver core for the `mini_type_solver` prototype.
//!
//! This library holds the constraint-solving logic. The `mini_type_solver`
//! binary is a thin command-line frontend over this API.

#![expect(
    clippy::multiple_crate_versions,
    reason = "varisat 0.2.2 pins syn 1/2 alongside the graph's syn 3"
)]

mod indices;

pub mod frontend;
pub mod solver;
