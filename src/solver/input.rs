//! Read access to one file's declarations, types, and comparisons.
//!
//! The borrowed data stays unchanged for every request. Programmatic fixtures
//! use checked declarations, arities, and bindings. The solver checks constructor
//! cycles and relationships between generic scopes.
//! Source-variable and class-reference cycle facts are computed once for the
//! complete input. Prefix and core checks borrow the same facts.

use std::collections::{BTreeMap, BTreeSet};

use crate::frontend::ValidatedFile;
use crate::frontend::problem::{
    AtomId, AtomStore, ClassId, Declarations, Hierarchy, MetaVarId, TemplateType, TypeStore,
};
#[cfg(test)]
use crate::frontend::test_support::RawProblem;

use super::reachability;

/// Fixed metadata and source facts for every theory request in one solve.
///
/// Each atom set contains all metavariables in both endpoints. The inverse
/// index contains exactly the atoms whose endpoints refer to each variable.
/// Class-reference cycle facts cover all declarations, including unused classes.
#[derive(Debug)]
pub struct Input<'a> {
    declarations: &'a Declarations,
    types: &'a TypeStore,
    atoms: &'a AtomStore,
    hierarchy: &'a Hierarchy,
    atom_metavars: BTreeMap<AtomId, BTreeSet<MetaVarId>>,
    metavar_atoms: BTreeMap<MetaVarId, BTreeSet<AtomId>>,
    cycle_reaching_classes: BTreeSet<ClassId>,
}

impl<'a> Input<'a> {
    pub fn new(file: &'a ValidatedFile) -> Self {
        Self::from_parts(
            file.declarations(),
            file.types(),
            file.atoms(),
            file.hierarchy(),
        )
    }

    fn from_parts(
        declarations: &'a Declarations,
        types: &'a TypeStore,
        atoms: &'a AtomStore,
        hierarchy: &'a Hierarchy,
    ) -> Self {
        let mut type_metavars = BTreeMap::new();
        let mut atom_metavars = BTreeMap::new();
        let mut metavar_atoms = BTreeMap::<MetaVarId, BTreeSet<AtomId>>::new();
        for (id, atom) in atoms.entries() {
            let mut metavars = BTreeSet::new();
            for endpoint in [atom.lower, atom.upper] {
                let endpoint_metavars = type_metavars.entry(endpoint).or_insert_with(|| {
                    let mut metavars = BTreeSet::new();
                    types.collect_metavars(endpoint, &mut metavars);
                    metavars
                });
                metavars.extend(endpoint_metavars.iter().copied());
            }
            for metavar in &metavars {
                metavar_atoms.entry(*metavar).or_default().insert(id);
            }
            atom_metavars.insert(id, metavars);
        }
        Self {
            declarations,
            types,
            atoms,
            hierarchy,
            atom_metavars,
            metavar_atoms,
            cycle_reaching_classes: cycle_reaching_classes(declarations, hierarchy),
        }
    }

    pub fn declarations(&self) -> &'a Declarations {
        self.declarations
    }

    pub fn types(&self) -> &'a TypeStore {
        self.types
    }

    pub fn atoms(&self) -> &'a AtomStore {
        self.atoms
    }

    pub fn hierarchy(&self) -> &'a Hierarchy {
        self.hierarchy
    }

    /// Classes that can reach a cycle through proper ancestor roots or class
    /// names in ancestor arguments. Built-in classes cannot reach such a cycle.
    pub fn cycle_reaching_classes(&self) -> &BTreeSet<ClassId> {
        &self.cycle_reaching_classes
    }

    /// All metavariables in both endpoints. The atom must belong to this input.
    pub fn atom_metavars(&self, atom: AtomId) -> &BTreeSet<MetaVarId> {
        let Some(metavars) = self.atom_metavars.get(&atom) else {
            panic!("source-variable facts require an atom from this input");
        };
        metavars
    }

    /// Atoms whose endpoints contain `metavar`. Unused variables have no atoms.
    pub fn metavar_atoms(&self, metavar: MetaVarId) -> impl Iterator<Item = AtomId> + '_ {
        self.metavar_atoms
            .get(&metavar)
            .into_iter()
            .flatten()
            .copied()
    }

    #[cfg(test)]
    pub fn fixture(problem: &'a RawProblem) -> Self {
        Self::from_parts(
            &problem.declarations,
            problem.types.types(),
            problem.atoms.atoms(),
            &problem.hierarchy,
        )
    }
}

/// The hierarchy must belong to these declarations. Only built-in classes have
/// no hierarchy entry. Template parameters do not add class-reference edges.
fn cycle_reaching_classes(declarations: &Declarations, hierarchy: &Hierarchy) -> BTreeSet<ClassId> {
    let mut edges = vec![Vec::new(); declarations.class_count()];
    for (class, _) in declarations.classes() {
        let children = &mut edges[class.index()];
        let mut arguments = Vec::new();
        for ancestor in hierarchy.ancestors(class) {
            children.push(ancestor.class.index());
            arguments.extend(&ancestor.arguments);
        }
        while let Some(argument) = arguments.pop() {
            match argument {
                TemplateType::Parameter { .. } => {}
                TemplateType::Class(class) => {
                    children.push(class.class.index());
                    arguments.extend(&class.arguments);
                }
                TemplateType::Tuple(parts)
                | TemplateType::Union(parts)
                | TemplateType::Intersection(parts) => arguments.extend(parts),
                TemplateType::Callable { params, ret } => {
                    arguments.extend(params);
                    arguments.push(ret);
                }
            }
        }
    }
    let cyclic = reachability::can_reach_cycle(&edges);
    declarations
        .classes()
        .filter_map(|(class, _)| cyclic.contains(&class.index()).then_some(class))
        .collect()
}
