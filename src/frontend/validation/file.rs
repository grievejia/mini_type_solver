//! Core units and validated source declarations.
//!
//! Resolution interns atoms and retains source spans. Hierarchy validation
//! checks declarations before it publishes the complete file.

use std::fmt::Write;

use super::super::diagnostic::Span;
use super::BUILTIN_COUNT;
use super::{AtomId, AtomStore, Declarations, Hierarchy, TypeStore, ValidatedFile};

impl ValidatedFile {
    /// Read the complete declaration metadata.
    #[must_use]
    pub fn declarations(&self) -> &Declarations {
        &self.declarations
    }

    /// Read canonical semantic types.
    #[must_use]
    pub fn types(&self) -> &TypeStore {
        &self.types
    }

    /// Read canonical subtype atoms.
    #[must_use]
    pub fn atoms(&self) -> &AtomStore {
        &self.atoms
    }

    /// Read checked class hierarchy metadata.
    #[must_use]
    pub fn hierarchy(&self) -> &Hierarchy {
        &self.hierarchy
    }

    /// Read assertions in source order.
    #[must_use]
    pub fn assertions(&self) -> &[Assertion] {
        &self.assertions
    }

    /// Summary of the validated file: user and built-in class counts,
    /// metavariable count, assertion counts split by named and
    /// unnamed, and atom occurrences with the distinct count.
    #[must_use]
    pub fn render_summary(&self) -> String {
        let named = self
            .assertions
            .iter()
            .filter(|assertion| assertion.label.is_some())
            .count();
        let total = self.assertions.len();
        let occurrences: usize = self
            .assertions
            .iter()
            .flat_map(|assertion| assertion.units.iter())
            .map(|unit| count_occurrences(&unit.formula))
            .sum();
        format!(
            "classes: {} user, {BUILTIN_COUNT} builtin\nmetavars: {}\nassertions: {total} ({named} named, {} unnamed)\natoms: {occurrences} occurrences, {} distinct",
            self.declarations.user_class_count(),
            self.declarations.metavar_count(),
            total - named,
            self.atoms.atom_count()
        )
    }

    /// C3 linearizations, one `MRO(NAME) = [...]` line per
    /// user-defined class in declaration order. Each line is
    /// newline-terminated; the output is empty when no user classes
    /// exist.
    #[must_use]
    pub fn render_mro(&self) -> String {
        let mut out = String::new();
        for (id, _) in self
            .declarations
            .classes()
            .filter(|(id, _)| id.index() >= BUILTIN_COUNT)
        {
            let chain = self
                .hierarchy
                .linearization(id)
                .map(|id| self.declarations.class_name(id))
                .collect::<Vec<_>>()
                .join(", ");
            let _ = writeln!(out, "MRO({}) = [{chain}]", self.declarations.class_name(id));
        }
        out
    }
}

/// Formula over interned atoms with Boolean children in source order.
///
/// Core units retain source spans; atom leaves contain canonical identifiers.
#[derive(Debug, PartialEq, Eq)]
pub enum AtomFormula {
    Atom(AtomId),
    Conjunction(Vec<AtomFormula>),
    Disjunction(Vec<AtomFormula>),
}

/// One core unit with its source span.
///
/// Each operand of the outermost conjunction forms one unit. Nested conjunctions
/// stay inside their unit. An assertion without an outermost conjunction forms
/// one unit spanning the complete formula without formula parentheses.
#[derive(Debug)]
pub struct CoreUnit {
    pub formula: AtomFormula,
    /// Unit source span, kept for core rendering.
    pub span: Span,
}

/// One assertion over interned atoms, with core units and its label.
///
/// Resolution creates this record before hierarchy validation.
#[derive(Debug)]
pub struct Assertion {
    /// Label when the assertion is named, kept for solver output.
    pub label: Option<String>,
    pub units: Vec<CoreUnit>,
}

/// Count atom occurrences in one interned formula.
fn count_occurrences(formula: &AtomFormula) -> usize {
    match formula {
        AtomFormula::Atom(_) => 1,
        AtomFormula::Conjunction(children) | AtomFormula::Disjunction(children) => {
            children.iter().map(count_occurrences).sum()
        }
    }
}
