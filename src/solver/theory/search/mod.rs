//! Check selected subtype comparisons with reversible changes to their bounds.

mod generics;
pub mod graph;
pub mod identities;
mod range;
#[cfg(test)]
mod tests;

use super::super::input::Input;
use super::{ClassRelation, TheoryResult, TheorySolution};
use crate::frontend::problem::{AtomId, MetaVarId};
use graph::Graph;
use identities::Identities;
pub use range::Witness;
use std::collections::{BTreeSet, VecDeque};

/// One connected atom group with its complete set of declared metavariables.
///
/// Component discovery constructs this record. The set contains all and only
/// the declared metavariables reachable from the atoms.
#[derive(Debug)]
struct Component {
    atoms: Vec<AtomId>,
    metavars: BTreeSet<MetaVarId>,
}

/// Solve the selected comparisons against the immutable input metadata.
///
/// The function groups atoms connected by shared metavariables. Each group is a
/// component. Metavariables inside constructors also connect atoms. Every atom
/// goes into one component, and components have no metavariables in common.
/// Since the class metadata is fixed, their assignments can be found separately
/// and combined.
///
/// Separate searches limit repeated checks and changes to one group.
/// They also avoid retrying unrelated choices when another component fails.
pub fn solve_conjunction(atoms: &[AtomId], input: &Input<'_>) -> TheoryResult {
    let atoms = atoms.iter().copied().collect::<BTreeSet<_>>();
    let relation = ClassRelation::new(input);
    let graph = &Graph::new(input.declarations());
    let identities = &mut Identities::new();
    let metavars = atoms
        .iter()
        .flat_map(|atom| input.atom_metavars(*atom))
        .copied()
        .collect::<BTreeSet<_>>();
    // Register active variables in declaration order before any type conversion.
    for metavar in metavars {
        identities.declared(metavar);
    }
    let mut assigned = BTreeSet::new();
    let mut seen_metavars = BTreeSet::new();
    let mut components = Vec::new();
    for seed in &atoms {
        if !assigned.insert(*seed) {
            continue;
        }
        let mut pending = VecDeque::from([*seed]);
        let mut component_atoms = Vec::new();
        let mut metavars = BTreeSet::new();
        while let Some(atom) = pending.pop_front() {
            component_atoms.push(atom);
            for metavar in input.atom_metavars(atom) {
                // Every selected neighbor is queued when the variable is first
                // visited. Later atoms do not need to read the same list again.
                if !seen_metavars.insert(*metavar) {
                    continue;
                }
                metavars.insert(*metavar);
                for neighbor in input.metavar_atoms(*metavar) {
                    if atoms.contains(&neighbor) && assigned.insert(neighbor) {
                        pending.push_back(neighbor);
                    }
                }
            }
        }
        component_atoms.sort();
        components.push(Component {
            atoms: component_atoms,
            metavars,
        });
    }

    let mut witnesses = Vec::new();
    for component in components {
        let Some(witness) = range::solve_component(graph, &component, input, identities, &relation)
        else {
            return TheoryResult::Unsatisfiable;
        };
        witnesses.push(witness);
    }
    TheoryResult::Satisfiable(TheorySolution::ranges(
        graph, witnesses, identities, &relation,
    ))
}
