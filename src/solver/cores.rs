//! Subset-minimal conflict cores and their source entries.
//!
//! Only minimization constructs a core. Engine modules borrow its surviving units.

use std::collections::BTreeMap;

use crate::frontend::Span;
use crate::frontend::problem::AtomFormula;

use super::WorkUnit;

/// Greedily minimize the unit list to a subset-minimal core: drop each
/// unit in source order while the remainder stays unsatisfiable.
/// Conflict monotonicity makes the result subset-minimal and
/// deterministic, at one remainder check per unit. The predicate is
/// `FnMut` so each engine counts its minimization work without
/// interior mutability.
///
/// The complete unit list must be unsatisfiable. The predicate must use the same
/// input owners and search rules for every subset. Conflict must be monotone:
/// adding units to a rejected subset cannot make it satisfiable.
pub fn minimize(units: &[WorkUnit<'_>], check: &mut dyn FnMut(&[&AtomFormula]) -> bool) -> Core {
    let mut kept = vec![true; units.len()];
    for index in 0..units.len() {
        kept[index] = false;
        let remaining: Vec<&AtomFormula> = units
            .iter()
            .enumerate()
            .filter(|(other, _)| kept[*other])
            .map(|(_, unit)| unit.formula)
            .collect();
        if check(&remaining) {
            kept[index] = true;
            tracing::debug!(unit = index, "core unit kept");
        } else {
            tracing::debug!(unit = index, "core unit dropped");
        }
    }
    let core = units
        .iter()
        .enumerate()
        .filter(|(index, _)| kept[*index])
        .map(|(_, unit)| CoreUnit {
            label: unit.label.map(str::to_owned),
            span: unit.span,
        })
        .collect();
    Core { units: core }
}

/// Subset-minimal core under the specified search.
///
/// Search rejects the complete core and accepts each one-unit deletion in the
/// same environment. Every deletion uses the same checked declarations and
/// type bindings.
#[derive(Debug, PartialEq, Eq)]
pub struct Core {
    units: Vec<CoreUnit>,
}

/// One core entry: the raw assertion name when named, with the source
/// span used for `line:col` entries.
#[derive(Debug, PartialEq, Eq)]
pub struct CoreUnit {
    label: Option<String>,
    span: Span,
}

impl CoreUnit {
    /// Raw assertion name when the unit comes from a named assertion.
    #[must_use]
    pub fn label(&self) -> Option<&str> {
        self.label.as_deref()
    }

    /// Source span of the unit, used for `line:col` entries.
    #[must_use]
    pub fn span(&self) -> Span {
        self.span
    }
}

impl Core {
    /// Surviving units in source order.
    #[must_use]
    pub fn units(&self) -> &[CoreUnit] {
        &self.units
    }

    /// Render the core block for stdout. Label occurrences count in
    /// the final core: a sole unit from an assertion prints its label,
    /// or `line:col` when unnamed; repeated units from one named
    /// assertion print `label (line:col)` so entries stay
    /// distinguishable.
    #[must_use]
    pub fn render(&self, source: &str) -> String {
        let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
        for unit in &self.units {
            if let Some(label) = &unit.label {
                *counts.entry(label.as_str()).or_default() += 1;
            }
        }
        let mut out = String::from("unsatisfiable\ncore:\n");
        for unit in &self.units {
            out.push_str("  ");
            match &unit.label {
                Some(label) if counts.get(label.as_str()) != Some(&1) => {
                    let (line, col) = unit.span.start_line_col(source);
                    out.push_str(label);
                    out.push_str(" (");
                    out.push_str(&line.to_string());
                    out.push(':');
                    out.push_str(&col.to_string());
                    out.push(')');
                }
                Some(label) => out.push_str(label),
                None => {
                    let (line, col) = unit.span.start_line_col(source);
                    out.push_str(&line.to_string());
                    out.push(':');
                    out.push_str(&col.to_string());
                }
            }
            out.push('\n');
        }
        out
    }
}
