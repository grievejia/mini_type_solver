//! Scope conversions must preserve bounds when a parameter leaves its scope.

use crate::frontend::problem::{BoundRef, Callable, TypeId};
use crate::frontend::test_support::{RawProblem, lookup_class, lookup_metavar};
use crate::solver::input::Input;
use crate::solver::test_support::atom_from_ids;

use super::{check_canonical, check_source_model};

fn named(problem: &mut RawProblem, name: &str, arguments: Vec<TypeId>) -> TypeId {
    let class = lookup_class(&problem.declarations, name);
    problem.types.intern_class(class, arguments)
}

fn generic(problem: &mut RawProblem, parameter: TypeId, ret: TypeId) -> TypeId {
    problem.types.intern_generic(
        1,
        &Callable {
            params: vec![parameter],
            ret,
        },
    )
}

#[test]
fn recursive_values_do_not_make_polymorphic_selections_legal() {
    let declarations = "class Inv[T]; metavar ?F; metavar ?R;";
    let mut problem = RawProblem::new(declarations);
    let f = lookup_metavar(&problem.declarations, "F");
    let r = lookup_metavar(&problem.declarations, "R");
    let f = problem.types.types().metavar_type(f);
    let r = problem.types.types().metavar_type(r);
    let bound = problem.types.intern_bound(BoundRef::new(0, 0));
    let identity = generic(&mut problem, bound, bound);
    let inv_f = named(&mut problem, "Inv", vec![f]);
    let tuple = problem.types.intern_tuple(vec![inv_f, r]);
    let target = problem.types.intern_callable(vec![tuple], tuple);
    let recursive = problem.types.intern_tuple(vec![r]);
    for include_cycle in [false, true] {
        let mut formulas = vec![
            atom_from_ids(&mut problem, identity, f),
            atom_from_ids(&mut problem, f, identity),
            atom_from_ids(&mut problem, identity, target),
        ];
        if include_cycle {
            formulas.push(atom_from_ids(&mut problem, recursive, r));
        }
        check_canonical(declarations, &Input::fixture(&problem), &formulas, false);
    }
}

#[test]
fn lower_generic_conflicts_are_rejected_before_witness_construction() {
    let declarations = "class A; class B; metavar ?T;";
    let mut problem = RawProblem::new(declarations);
    let bound = problem.types.intern_bound(BoundRef::new(0, 0));
    let identity = generic(&mut problem, bound, bound);
    let a = named(&mut problem, "A", vec![]);
    let b = named(&mut problem, "B", vec![]);
    let target = problem.types.intern_callable(vec![a], b);
    let t = lookup_metavar(&problem.declarations, "T");
    let t = problem.types.types().metavar_type(t);
    for mask in 0u8..4 {
        let formulas = [(identity, target), (a, t)]
            .into_iter()
            .enumerate()
            .filter(|(index, _)| mask & (1 << index) != 0)
            .map(|(_, (lower, upper))| atom_from_ids(&mut problem, lower, upper))
            .collect::<Vec<_>>();
        check_canonical(
            declarations,
            &Input::fixture(&problem),
            &formulas,
            mask & 1 == 0,
        );
    }
}

#[test]
fn source_scope_conversions_have_the_derived_results() {
    for (source, expected) in [
        (
            include_str!("../../../tests/data/solve/sat/class_invariant_transfer.input"),
            "satisfiable\nmodel:\n  ?M = object\n",
        ),
        (
            include_str!("../../../tests/data/solve/sat/class_deferred_transfer.input"),
            "satisfiable\nmodel:\n  ?M = (Dog) -> Parent[object]\n",
        ),
    ] {
        check_source_model(source, expected);
    }
}
