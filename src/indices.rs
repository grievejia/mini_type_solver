//! Stable identifier bounds and ordered live parameter positions.

use std::collections::{BTreeMap, BTreeSet};

/// Check that a table position fits its identifier representation.
pub fn checked_u32(value: usize, context: &str) -> u32 {
    let Ok(value) = u32::try_from(value) else {
        panic!("{context} exceeds the supported identifier range");
    };
    value
}

/// Number live positions consecutively, preserving their increasing order.
pub fn parameter_positions(live: &BTreeSet<u32>) -> BTreeMap<u32, u32> {
    live.iter()
        .enumerate()
        .map(|(canonical, position)| {
            (
                *position,
                checked_u32(canonical, "canonical generic parameter position"),
            )
        })
        .collect()
}
