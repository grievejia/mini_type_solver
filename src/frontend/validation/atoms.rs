//! Canonical subtype atoms and their resolution builder.
//!
//! Atom endpoints refer to the accompanying `TypeStore`. Equal endpoint pairs
//! share an identifier. Core units retain source spans separately.

use std::collections::BTreeMap;

use crate::indices::checked_u32;

use super::types::TypeId;

/// Identifier of one interned subtype atom, file-global.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct AtomId(u32);

/// One distinct subtype atom's bounds, shared by its occurrences.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Atom {
    /// Lower bound type, kept for solver queries.
    pub lower: TypeId,
    /// Upper bound type, kept for solver queries.
    pub upper: TypeId,
}

/// Distinct resolved subtype assertions for one problem.
#[derive(Debug, Clone, Default)]
pub struct AtomStore {
    atoms: Vec<Atom>,
}

impl AtomStore {
    /// Read the bounds of a canonical atom.
    #[must_use]
    pub fn atom(&self, id: AtomId) -> &Atom {
        &self.atoms[id.0 as usize]
    }

    /// Read the number of canonical atoms.
    #[must_use]
    pub fn atom_count(&self) -> usize {
        self.atoms.len()
    }

    /// Read every canonical atom in identifier order.
    pub fn entries(&self) -> impl Iterator<Item = (AtomId, &Atom)> {
        self.atoms
            .iter()
            .enumerate()
            .map(|(index, atom)| (AtomId(checked_u32(index, "atom count")), atom))
    }
}

/// Local atom construction during assertion resolution.
#[derive(Debug, Default)]
pub struct AtomBuilder {
    store: AtomStore,
    ids: BTreeMap<(TypeId, TypeId), AtomId>,
}

impl AtomBuilder {
    /// Start an empty canonical atom table.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Read the atom table already constructed.
    #[cfg(test)]
    #[must_use]
    pub fn atoms(&self) -> &AtomStore {
        &self.store
    }

    #[cfg(test)]
    #[must_use]
    pub fn from_store(store: AtomStore) -> Self {
        let ids = store
            .atoms
            .iter()
            .enumerate()
            .map(|(index, atom)| {
                (
                    (atom.lower, atom.upper),
                    AtomId(checked_u32(index, "atom count")),
                )
            })
            .collect();
        Self { store, ids }
    }

    /// Intern a subtype pair in source occurrence order.
    pub fn intern_atom(&mut self, lower: TypeId, upper: TypeId) -> AtomId {
        if let Some(id) = self.ids.get(&(lower, upper)) {
            return *id;
        }
        let id = AtomId(checked_u32(self.store.atoms.len(), "atom count"));
        self.ids.insert((lower, upper), id);
        self.store.atoms.push(Atom { lower, upper });
        id
    }

    /// Read an atom while resolving assertions.
    #[cfg(test)]
    #[must_use]
    pub fn atom(&self, id: AtomId) -> &Atom {
        self.store.atom(id)
    }

    /// Complete resolution and discard the construction index.
    #[must_use]
    pub fn finish(self) -> AtomStore {
        self.store
    }
}
