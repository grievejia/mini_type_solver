//! Find values that satisfy one selected set of `<:` comparisons.
//!
//! [`ClassRelation`] borrows declarations, checked hierarchy metadata, and
//! class-reference cycle facts from one [`Input`].
//! [`solve_conjunction`] keeps required comparisons and generic selections
//! during search. It returns one complete assignment after checking those records.

pub mod closed;
mod search;
#[cfg(test)]
pub mod test_support;
#[cfg(test)]
mod tests;

use std::collections::{BTreeMap, BTreeSet};

use super::input::Input;
use crate::frontend::problem::{
    ClassId, ClassType, Declarations, Hierarchy, MetaVarId, TemplateType,
};
use closed::{Builder, Value};
use search::Witness;
use search::graph::Graph;
use search::identities::Identities;
pub use search::solve_conjunction;

/// Complete class-name relation from the same environment used by search.
///
/// The caller supplies checked hierarchy metadata. Every shorter comparison
/// list keeps that environment. Invalid metadata is a programming error.
#[derive(Debug)]
pub struct ClassRelation<'a> {
    declarations: &'a Declarations,
    hierarchy: &'a Hierarchy,
    cycle_reaching_classes: &'a BTreeSet<ClassId>,
}

impl<'a> ClassRelation<'a> {
    /// Requires completed class metadata. Each C3 order starts with its class
    /// and ends with object. Ancestor templates follow the remaining order.
    fn new(input: &'a Input<'a>) -> Self {
        Self {
            declarations: input.declarations(),
            hierarchy: input.hierarchy(),
            cycle_reaching_classes: input.cycle_reaching_classes(),
        }
    }

    /// Find one proper ancestor with arguments in the lower class's parameter scope.
    fn ancestor_template(
        &self,
        lower: ClassId,
        upper: ClassId,
    ) -> Option<&ClassType<TemplateType>> {
        self.hierarchy
            .ancestors(lower)
            .iter()
            .find(|template| template.class == upper)
    }

    /// Subtype removal needs acyclic class references as well as finite values.
    /// Superclass arguments stay finite even when their class names form a cycle.
    fn has_reference_cycle(&self, roots: impl IntoIterator<Item = ClassId>) -> bool {
        roots
            .into_iter()
            .any(|class| self.cycle_reaching_classes.contains(&class))
    }
}

/// Constructor information that remains fixed while assignments grow.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Shape {
    Unknown,
    Class,
    Tuple(usize),
    Callable(usize),
}

impl Shape {
    /// Retain the known shape across unknown factors. Every compatible fixed
    /// factor has that same shape, so one mismatch rejects the intersection.
    fn conflict(shapes: impl IntoIterator<Item = Self>) -> bool {
        let mut fixed = Self::Unknown;
        for next in shapes {
            if next == Self::Unknown {
                continue;
            }
            if fixed != Self::Unknown && fixed != next {
                return true;
            }
            fixed = next;
        }
        false
    }
}

/// Outcome of one conjunction: the verdict plus public output on success.
#[derive(Debug, PartialEq, Eq)]
pub enum TheoryResult {
    /// Conjunction holds with one checked assignment.
    Satisfiable(TheorySolution),
    /// Search rejects this set and every containing set from the same input.
    Unsatisfiable,
}

/// Complete values for the variables in one checked assignment.
///
/// Every variable in the selected comparisons has an entry. A declared variable
/// without an entry is unconstrained. An entry can have the value `never`.
/// Values share immutable graph storage after the search ends.
#[derive(Debug, PartialEq, Eq)]
pub struct TheorySolution {
    assignments: BTreeMap<MetaVarId, Value>,
    #[cfg(test)]
    original_witness: BTreeMap<MetaVarId, Value>,
}

impl TheorySolution {
    /// Take the checked complete values for the selected comparisons.
    pub fn into_assignments(self) -> BTreeMap<MetaVarId, Value> {
        self.assignments
    }

    /// Close and check the witnesses before constructing public values.
    ///
    /// If any witness has recursion or a reachable cycle through class
    /// references, all witnesses retain only closure's structural normalization.
    /// Finite subtype removal requires acyclic values and class references.
    /// Components have disjoint declared metavariables. Their values retain the
    /// immutable graph after comparison records and normalization proofs are dropped.
    fn ranges(
        graph: &Graph,
        witnesses: Vec<Witness>,
        identities: &Identities,
        relation: &ClassRelation<'_>,
    ) -> Self {
        let mut builder = Builder::new(relation.declarations);
        let introductions = witnesses
            .iter()
            .flat_map(Witness::introductions)
            .collect::<Vec<_>>();
        builder.scopes(
            &introductions,
            witnesses.iter().flat_map(Witness::variable_ids),
            identities,
        );
        let mut roots = Vec::new();
        let prepared = witnesses
            .into_iter()
            .map(|witness| witness.prepare(graph, &mut builder, &mut roots, identities))
            .collect::<Vec<_>>();
        let values = builder.finish(&roots);
        let checked = prepared
            .into_iter()
            .map(|prepared| prepared.check(&values, graph, identities, relation))
            .collect::<Vec<_>>();
        drop(values);
        let structural_only = checked
            .iter()
            .any(|witness| witness.needs_structural_normalization(relation));
        #[cfg(test)]
        let original_witness = {
            let mut values = BTreeMap::new();
            for witness in &checked {
                values.extend(witness.witness_values());
            }
            values
        };
        let checked = if structural_only {
            checked
        } else {
            checked
                .into_iter()
                .map(|witness| witness.normalize(graph, identities, relation))
                .collect()
        };
        let mut assignments = BTreeMap::new();
        for witness in checked {
            assignments.extend(witness.witness_values());
        }
        Self {
            assignments,
            #[cfg(test)]
            original_witness,
        }
    }

    #[cfg(test)]
    pub fn witness(&self, metavar: MetaVarId) -> Option<&Value> {
        self.original_witness.get(&metavar)
    }
}
