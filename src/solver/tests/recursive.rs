//! Recursive bounds must produce checked values under every Boolean engine.

use crate::frontend::problem::{AtomFormula, BoundRef, Callable};
use crate::frontend::test_support::{RawProblem, lookup_class};
use crate::solver::SolveOutcome;
use crate::solver::input::Input;
use crate::solver::test_support::atom_from_ids;

use super::{check_canonical, check_source, check_source_model};

#[test]
fn opposite_tuple_bounds_produce_one_guarded_definition() {
    let mut problem = RawProblem::new("");
    let t = problem.declare_metavar("T");
    let reference = problem.types.types().metavar_type(t);
    let tuple = problem.types.intern_tuple(vec![reference]);
    let formulas = [
        atom_from_ids(&mut problem, tuple, reference),
        atom_from_ids(&mut problem, reference, tuple),
    ];
    for outcome in check_canonical("", &Input::fixture(&problem), &formulas, true) {
        let SolveOutcome::Satisfiable(model) = outcome else {
            panic!("the bounds are the equation T = tuple[T]");
        };
        assert_eq!(model.entries()[0].value().render(), "mu R0. tuple[R0]");
    }
}

#[test]
fn an_upper_tuple_bound_does_not_force_equality() {
    let mut problem = RawProblem::new("");
    let t = problem.declare_metavar("T");
    let reference = problem.types.types().metavar_type(t);
    let tuple = problem.types.intern_tuple(vec![reference]);
    let formula = atom_from_ids(&mut problem, reference, tuple);
    for outcome in check_canonical("", &Input::fixture(&problem), &[formula], true) {
        let SolveOutcome::Satisfiable(model) = outcome else {
            panic!("never is below every tuple");
        };
        assert_eq!(model.entries()[0].value().render(), "never");
    }
}

#[test]
fn a_recursive_tuple_cannot_satisfy_a_different_tuple_length() {
    let mut problem = RawProblem::new("");
    let t = problem.declare_metavar("T");
    let reference = problem.types.types().metavar_type(t);
    let tuple = problem.types.intern_tuple(vec![reference]);
    let wrong = problem.types.intern_tuple(Vec::new());
    let formulas = [
        atom_from_ids(&mut problem, tuple, reference),
        atom_from_ids(&mut problem, reference, wrong),
    ];
    check_canonical("", &Input::fixture(&problem), &formulas, false);
}

#[test]
fn opposite_function_bounds_keep_the_recursive_parameter() {
    let source = "class A;";
    let mut problem = RawProblem::new(source);
    let a = lookup_class(&problem.declarations, "A");
    let t = problem.declare_metavar("T");
    let reference = problem.types.types().metavar_type(t);
    let a = problem.types.intern_class(a, Vec::new());
    let function = problem.types.intern_callable(vec![reference], a);
    let formulas = [
        atom_from_ids(&mut problem, function, reference),
        atom_from_ids(&mut problem, reference, function),
    ];
    for outcome in check_canonical(source, &Input::fixture(&problem), &formulas, true) {
        let SolveOutcome::Satisfiable(model) = outcome else {
            panic!("the bounds describe T = (T) -> A");
        };
        assert_eq!(model.entries()[0].value().render(), "mu R0. (R0) -> A");
    }
}

#[test]
fn invariant_arguments_do_not_create_a_cycle_from_an_upper_bound() {
    let source = "class Inv[T];";
    let mut problem = RawProblem::new(source);
    let inv = lookup_class(&problem.declarations, "Inv");
    let t = problem.declare_metavar("T");
    let z = problem.declare_metavar("Z");
    let t = problem.types.types().metavar_type(t);
    let z = problem.types.types().metavar_type(z);
    let instance = problem.types.intern_class(inv, vec![t]);
    let formulas = [
        atom_from_ids(&mut problem, t, instance),
        atom_from_ids(&mut problem, instance, z),
    ];
    for outcome in check_canonical(source, &Input::fixture(&problem), &formulas, true) {
        let SolveOutcome::Satisfiable(model) = outcome else {
            panic!("T=never and Z=Inv[never] satisfy both bounds");
        };
        assert_eq!(model.entries()[0].value().render(), "never");
        assert_eq!(model.entries()[1].value().render(), "Inv[never]");
    }
}

#[test]
fn a_recursive_tuple_conflict_remains_in_every_superset() {
    let mut problem = RawProblem::new("");
    let t = problem.declare_metavar("T");
    let reference = problem.types.types().metavar_type(t);
    let tuple = problem.types.intern_tuple(vec![reference]);
    let empty = problem.types.intern_tuple(vec![]);
    // Every subset uses the same atom IDs, regardless of which atoms it omits.
    let atoms = [(tuple, reference), (reference, tuple), (reference, empty)]
        .map(|(lower, upper)| problem.atoms.intern_atom(lower, upper));
    // The first and third bounds require tuple[T] <: tuple[]. The second
    // bound creates recursion but cannot remove that length mismatch.
    for mask in 0u8..8 {
        let selected = atoms
            .iter()
            .enumerate()
            .filter(|(index, _)| mask & (1 << index) != 0)
            .map(|(_, atom)| AtomFormula::Atom(*atom))
            .collect::<Vec<_>>();
        check_canonical(
            "",
            &Input::fixture(&problem),
            &selected,
            mask & 0b101 != 0b101,
        );
    }
}

#[test]
fn a_recursive_class_union_keeps_both_lower_contributions() {
    let declarations = "class A; class Box[+T];";
    let mut problem = RawProblem::new(declarations);
    let a = lookup_class(&problem.declarations, "A");
    let box_class = lookup_class(&problem.declarations, "Box");
    let t = problem.declare_metavar("T");
    let reference = problem.types.types().metavar_type(t);
    let a = problem.types.intern_class(a, vec![]);
    let recursive = problem.types.intern_class(box_class, vec![reference]);
    let union = problem.types.intern_union(vec![a, recursive]);
    let formulas = [
        atom_from_ids(&mut problem, union, reference),
        atom_from_ids(&mut problem, reference, union),
    ];
    for outcome in check_canonical(declarations, &Input::fixture(&problem), &formulas, true) {
        let SolveOutcome::Satisfiable(model) = outcome else {
            panic!("the bounds define T = A | Box[T]");
        };
        assert_eq!(model.entries()[0].value().render(), "mu R0. (A | Box[R0])");
    }
}

#[test]
fn mutually_recursive_values_with_separate_loops_render_and_pass_model_checks() {
    let mut problem = RawProblem::new("");
    let x = problem.declare_metavar("X");
    let y = problem.declare_metavar("Y");
    let x = problem.types.types().metavar_type(x);
    let y = problem.types.types().metavar_type(y);
    let tuple = problem.types.intern_tuple(vec![x, y]);
    let function = problem.types.intern_callable(vec![y], x);
    let formulas = [
        atom_from_ids(&mut problem, tuple, x),
        atom_from_ids(&mut problem, function, y),
    ];
    // X and Y each have a loop that does not pass through the other variable.
    // Both definitions need names when printing either root.
    for outcome in check_canonical("", &Input::fixture(&problem), &formulas, true) {
        let SolveOutcome::Satisfiable(model) = outcome else {
            panic!("the tuple and function equations have a guarded witness");
        };
        assert_eq!(
            model.entries()[0].value().render(),
            "mu R0. tuple[R0, mu R1. (R1) -> R0]"
        );
        assert_eq!(
            model.entries()[1].value().render(),
            "mu R0. (R0) -> mu R1. tuple[R1, R0]"
        );
    }
}

#[test]
fn equal_recursive_definitions_with_different_prefixes_share_one_printed_form() {
    let mut problem = RawProblem::new("");
    let x = problem.declare_metavar("X");
    let y = problem.declare_metavar("Y");
    let x = problem.types.types().metavar_type(x);
    let y = problem.types.types().metavar_type(y);
    let tuple = problem.types.intern_tuple(vec![y]);
    let formulas = [
        atom_from_ids(&mut problem, tuple, x),
        atom_from_ids(&mut problem, tuple, y),
    ];
    for outcome in check_canonical("", &Input::fixture(&problem), &formulas, true) {
        let SolveOutcome::Satisfiable(model) = outcome else {
            panic!("X = tuple[Y] and Y = tuple[Y] have the same guarded type");
        };
        for entry in model.entries() {
            assert_eq!(entry.value().render(), "mu R0. tuple[R0]");
        }
    }
}

#[test]
fn a_lower_generic_can_select_a_generic_free_recursive_tuple() {
    let mut problem = RawProblem::new("");
    let t = problem.declare_metavar("T");
    let t = problem.types.types().metavar_type(t);
    let tuple = problem.types.intern_tuple(vec![t]);
    let parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let identity = problem.types.intern_generic(
        1,
        &Callable {
            params: vec![parameter],
            ret: parameter,
        },
    );
    let target = problem.types.intern_callable(vec![t], t);
    let formulas = [
        atom_from_ids(&mut problem, tuple, t),
        atom_from_ids(&mut problem, identity, target),
    ];
    for outcome in check_canonical("", &Input::fixture(&problem), &formulas, true) {
        let SolveOutcome::Satisfiable(model) = outcome else {
            panic!("X can select the recursive tuple T");
        };
        // The generic-free copy P has P = tuple[P]. The return comparison
        // also contributes P to T, so T = P | tuple[T]. Recursive output
        // retains these structural alternatives without subtype removal.
        assert_eq!(
            model.entries()[0].value().render(),
            "mu R0. ((mu R1. tuple[R1]) | tuple[R0])"
        );
    }
}

#[test]
fn recursive_source_bounds_have_the_derived_witnesses() {
    // In the two-reversal case, T = (W) -> A and W = (T) -> A.
    // Both function nodes have the same structure and merge into one definition.

    for (source, witness) in [
        (
            include_str!("../../../tests/data/solve/sat/tuple_constructor_cycle.input"),
            "  ?T = mu R0. tuple[R0]\n",
        ),
        (
            include_str!("../../../tests/data/solve/sat/callable_direct_cycle.input"),
            "  ?T = mu R0. (R0) -> A\n",
        ),
        (
            include_str!("../../../tests/data/solve/sat/callable_indirect_cycle.input"),
            "  ?T = mu R0. (R0) -> A\n  ?U = mu R0. (R0) -> A\n",
        ),
        (
            include_str!("../../../tests/data/solve/sat/callable_signed_cycle.input"),
            "  ?T = mu R0. (R0) -> A\n  ?W = mu R0. (R0) -> A\n",
        ),
        (
            include_str!("../../../tests/data/solve/sat/callable_signed_indirect_cycle.input"),
            "  ?T = mu R0. (R0) -> A\n  ?U = mu R0. (R0) -> A\n  ?W = mu R0. (R0) -> A\n",
        ),
        (
            include_str!("../../../tests/data/solve/sat/callable_two_reversal_cycle.input"),
            "  ?T = mu R0. (R0) -> A\n  ?W = mu R0. (R0) -> A\n",
        ),
        (
            include_str!("../../../tests/data/solve/sat/callable_constructor_cycle.input"),
            "  ?M = mu R0. tuple[R0]\n  ?X = (mu R0. tuple[R0]) -> B\n  ?R = mu R0. tuple[R0]\n",
        ),
        (
            include_str!("../../../tests/data/solve/sat/generic_binder_cycle.input"),
            "  ?T = mu R0. tuple[R0]\n",
        ),
        (
            include_str!("../../../tests/data/solve/sat/generic_delayed_binder_cycle.input"),
            "  ?G = forall T0. (T0) -> tuple[T0]\n  ?T = mu R0. tuple[R0]\n",
        ),
        (
            include_str!("../../../tests/data/solve/sat/class_instance_cycle.input"),
            "  ?M = object\n  ?T = mu R0. Inv[R0]\n",
        ),
        (
            include_str!("../../../tests/data/solve/sat/box_equality.input"),
            "  ?X = never\n  ?Z = Box[never]\n",
        ),
    ] {
        check_source_model(source, &format!("satisfiable\nmodel:\n{witness}"));
    }
}

#[test]
fn a_covariant_self_reference_keeps_its_class_in_every_assertion_order() {
    let declarations = "class Seq[+T]; class S extends Seq[S]; metavar ?X;";
    let assertions = [
        "assert S <: ?X;",
        "assert ?X <: Seq[?X];",
        "assert Seq[?X] <: ?X;",
    ];
    for order in [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ] {
        let source = format!(
            "{declarations} {}",
            order.map(|index| assertions[index]).join(" ")
        );
        check_source_model(
            &source,
            "satisfiable\nmodel:\n  ?X = mu R0. (S | Seq[R0])\n",
        );
        check_source_model(
            &source,
            "satisfiable\nmodel:\n  ?X = mu R0. (S | Seq[R0])\n",
        );
    }
}

#[test]
fn nominal_unions_and_opposite_bounds_have_valid_witnesses() {
    check_source_model(
        include_str!("../../../tests/data/solve/sat/nominal_union.input"),
        "satisfiable\nmodel:\n  ?X = N[C] | C\n",
    );
    check_source(
        "class N[-T]; class C extends N[N[C]]; metavar ?X; assert ?X <: N[?X]; assert N[?X] <: ?X;",
        true,
    );
}

#[test]
fn an_unused_class_reference_cycle_does_not_disable_subtype_removal() {
    check_source_model(
        "class N[T];
         class Bad extends N[Bad];
         class A;
         class B extends A;
         metavar ?M;
         assert A | B <: ?M;",
        "satisfiable\nmodel:\n  ?M = A\n",
    );
}

#[test]
fn recursive_generic_arms_keep_separate_parameter_owners() {
    check_source(
        "class A; class B; metavar ?G; assert forall Z. (?G | Z) -> A <: ?G; assert forall V. (?G | V) -> B <: ?G;",
        true,
    );
}

#[test]
fn a_recursive_generic_can_refer_to_a_stored_closed_generic() {
    check_source(
        "class A; metavar ?G; metavar ?T; assert forall W. (W) -> W <: ?G; assert forall X. (tuple[?T, X]) -> ?G <: ?T;",
        true,
    );
}

#[test]
fn recursive_generic_comparison_returns_to_saved_bindings() {
    check_source(
        "class A; class B extends A; class Box[+T];
         metavar ?F; metavar ?G; metavar ?T;
         assert forall W. (Box[W | ?T]) -> (Box[W]) -> W | ?G <: ?G | ?G;
         assert forall W. (Box[(W) -> ?T]) -> ((B) -> B) -> (?G) -> W <: ?T;
         assert forall X. (?G) -> B | X <: ?T;",
        true,
    );
}

#[test]
fn recursive_generics_can_use_the_complete_union_in_their_parameters() {
    check_source(
        "class A; class B extends A; class Box[+T];
         metavar ?F; metavar ?G; metavar ?T;
         assert forall Z. (?G | Z) -> A <: ?G;
         assert forall V. ((?G | V) -> V | V) -> (tuple[A, ?F]) -> (V) -> A <: ?G;
         assert forall W. (tuple[?F, W]) -> ?F | W <: ?T;",
        true,
    );
}

#[test]
fn recursive_invariant_arguments_can_share_their_complete_values() {
    check_source(
        "class A; class B extends A; class C; class D extends B, C;
         class Inv[T]; class Box[+T]; class Neg[-T]; class P extends Box[A];
         metavar ?X; metavar ?Y; metavar ?Z;
         assert ?X <: ?X;
         assert Inv[tuple[?Y, ?X]] <: ?Y;
         assert (((?Y <: ?Z) and (Neg[?Z] <: ?Y | ?Z)) or (object <: ((D | C) | (C | D))));
         assert (?Z & (?Y & ?Z)) <: ?X;",
        true,
    );
}
