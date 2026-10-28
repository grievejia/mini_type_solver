//! Check combined type rules without sharing the solver's comparison code.

use std::fmt::Write;
use std::fs::{read_dir, read_to_string};
use std::path::Path;

use crate::solver::input::Input;
use crate::solver::test_support::{ModelInput, validate_ok};
use crate::solver::{SolveOutcome, work_units};

use super::{check_source, check_source_model, check_source_subsets, check_units};

#[test]
fn stored_solve_fixtures_have_valid_models_and_subset_minimal_cores() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/solve");
    for (directory, expected) in [("sat", true), ("unsat", false)] {
        let mut paths = read_dir(root.join(directory))
            .expect("stored solve fixture directory exists")
            .map(|entry| entry.expect("stored solve fixture is readable").path())
            .filter(|path| {
                path.extension()
                    .is_some_and(|extension| extension == "input")
            })
            .collect::<Vec<_>>();
        paths.sort();
        for path in paths {
            let source = read_to_string(&path).expect("stored solve fixture contains UTF-8");
            let file = validate_ok(&source);
            check_units(
                &work_units(&file),
                &Input::new(&file),
                ModelInput::Source(&source),
                expected,
                &format!("{}:\n{source}", path.display()),
            );
        }
    }
}

#[test]
fn recursive_cases_have_the_derived_witnesses_and_conflict() {
    for (source, expected) in [
        (
            include_str!("../../../benchmarks/recursive/01_tuple_self.input"),
            "satisfiable\nmodel:\n  ?T = mu R0. tuple[R0]\n",
        ),
        (
            include_str!("../../../benchmarks/recursive/02_callable_negative.input"),
            "satisfiable\nmodel:\n  ?T = mu R0. (R0) -> A\n",
        ),
        (
            include_str!("../../../benchmarks/recursive/03_callable_double_negative.input"),
            "satisfiable\nmodel:\n  ?T = mu R0. (R0) -> A\n  ?W = mu R0. (R0) -> A\n",
        ),
        (
            include_str!("../../../benchmarks/recursive/04_class_invariant_self.input"),
            "satisfiable\nmodel:\n  ?T = mu R0. Inv[R0]\n",
        ),
        (
            include_str!("../../../benchmarks/recursive/05_covariant_nominal.input"),
            "satisfiable\nmodel:\n  ?X = mu R0. (S | Seq[R0])\n",
        ),
        (
            include_str!("../../../benchmarks/recursive/07_generic_recursive.input"),
            "satisfiable\nmodel:\n  ?T = mu R0. forall T0. (T0) -> R0\n",
        ),
    ] {
        check_source_model(source, expected);
    }
    check_source(
        include_str!("../../../benchmarks/recursive/06_nominal_contravariant_unsat.input"),
        false,
    );
    let mut source = String::new();
    let mut expected = String::from("satisfiable\nmodel:\n");
    for index in 0..8 {
        let _ = writeln!(source, "metavar ?T{index};");
        let _ = writeln!(expected, "  ?T{index} = mu R0. tuple[R0]");
    }
    for index in 0..8 {
        let next = (index + 1) % 8;
        let _ = writeln!(source, "assert tuple[?T{index}] <: ?T{next};");
        let _ = writeln!(source, "assert ?T{next} <: tuple[?T{index}];");
    }
    check_source_model(&source, &expected);
}

#[test]
fn contravariant_and_invariant_rejections_hold_in_every_containing_subset() {
    // Con[X] <: Con[Y] requires Y <: X. The last three assertions then
    // require Cat <: Animal. Dog <: X does not cause that conflict.
    check_source_subsets(
        "class Animal; class Dog extends Animal; class Cat; class Con[-T];
         metavar ?X; metavar ?Y;
         assert Dog <: ?X; assert Con[?X] <: Con[?Y];
         assert Cat <: ?Y; assert ?X <: Animal;",
        &[0b1110],
    );
    // Inv[R] contributes a class value to R. Invariant equality with X
    // cannot make that value satisfy the tuple upper bound. The opposite
    // bound R <: Inv[R] cannot remove the mismatch.
    check_source_subsets(
        "class Inv[T]; metavar ?R; metavar ?X;
         assert Inv[?R] <: ?R; assert ?R <: Inv[?R];
         assert Inv[?R] <: Inv[?X]; assert ?X <: tuple[object];",
        &[0b1101],
    );
}

#[test]
fn generic_selections_keep_their_conflicts_when_recursive_bounds_are_added() {
    // One use can select Dog. The other use requires Cat <: X <: Dog.
    // Each use has its own selection, and the tuple loop changes neither use.
    check_source_subsets(
        "class Dog; class Cat; metavar ?G; metavar ?R;
         assert forall X. (X) -> tuple[X, X] <: ?G;
         assert ?G <: (Dog) -> tuple[Dog, Dog];
         assert ?G <: (Cat) -> tuple[Cat, Dog];
         assert tuple[?R] <: ?R;",
        &[0b0101],
    );
    // The recursive tuple can be copied into generic-free storage. The
    // generic parameter must still satisfy the unrelated A and B bounds.
    check_source_subsets(
        "class A; class B; metavar ?G; metavar ?R;
         assert forall X. (X) -> tuple[?R, X] <: ?G;
         assert tuple[?R] <: ?R;
         assert ?G <: (A) -> tuple[?R, B];",
        &[0b101],
    );
}

#[test]
fn scope_conversion_rejections_hold_for_each_source_subset() {
    check_source_subsets(
        include_str!("../../../tests/data/solve/unsat/generic_class_negative_core.input"),
        &[0b101],
    );
    for source in [
        include_str!("../../../tests/data/solve/unsat/class_retained_transfer.input"),
        "class Inv[T]; metavar ?M;
         assert ?M <: (Inv[never]) -> Inv[never];
         assert (?M) -> object
             <: forall Y. (forall Z. (Inv[Z & Y]) -> Inv[Z]) -> object;",
    ] {
        check_source_subsets(source, &[0b11]);
    }
}

#[test]
fn polymorphic_selections_stay_forbidden_after_recursive_values_are_added() {
    // The upper bound keeps F below the generic identity. Inv[F] requires
    // an exact copy inside a generic-free selection, which cannot retain it.
    // Without the upper bound, F=object permits an ordinary selection.
    check_source_model(
        "class Inv[T]; metavar ?F;
         assert forall X. (X) -> X <: ?F;
         assert forall Z. (Z) -> Z <: (Inv[?F]) -> Inv[?F];",
        "satisfiable\nmodel:\n  ?F = object\n",
    );
    check_source_subsets(
        "class Inv[T]; metavar ?F; metavar ?R;
         assert forall X. (X) -> X <: ?F;
         assert ?F <: forall Y. (Y) -> Y;
         assert forall Z. (Z) -> Z <: (Inv[?F]) -> Inv[?F];
         assert tuple[?R] <: ?R;",
        &[0b0111],
    );
}

#[test]
fn a_failed_nominal_cycle_does_not_reject_the_next_recursive_alternative() {
    // N is declared before C. The first tuple alternative fails at C <: N[C].
    // The second one keeps only the guarded tuple equation for R.
    check_source_model(
        "class N[-T]; class C extends N[N[C]]; metavar ?R;
         assert tuple[?R] <: ?R;
         assert tuple[C, ?R] <: tuple[N[C], tuple[]] | tuple[C, tuple[?R]];",
        "satisfiable\nmodel:\n  ?R = mu R0. tuple[R0]\n",
    );
}

#[test]
fn generic_instance_rollback_keeps_an_existing_recursive_witness() {
    // B precedes A, so the failed A -> B instance is tried first.
    // Its requirement and selection must not survive the successful A -> A use.
    check_source(
        "class B; class A; metavar ?R;
         assert tuple[?R] <: ?R;
         assert forall X. (X) -> X
             <: (forall Y. (Y) -> Y) -> (((A) -> B) | ((A) -> A));",
        true,
    );
}

#[test]
fn source_scope_conversions_preserve_the_ordered_ancestor_and_child_choices() {
    check_source_model(
        "class Parent[+T]; class Inv[T] extends Parent[T]; metavar ?M;
         assert (?M) -> object <: forall Y. (Inv[Y]) -> object;",
        "satisfiable\nmodel:\n  ?M = Parent[object]\n",
    );
    check_source_model(
        "class Box[+T]; metavar ?M;
         assert (?M) -> object <: forall Y. ((Box[Y]) -> object) -> object;",
        "satisfiable\nmodel:\n  ?M = (Box[never]) -> object\n",
    );
}

#[test]
fn recursive_and_generic_names_avoid_declared_names_and_keep_parameter_owners() {
    let source = "class A; metavar ?R0; metavar ?T0;
                  metavar ?G; metavar ?U;
                  assert forall Z. (?G | Z) -> A <: ?G; assert ?G <: ?U;";
    check_source_model(
        source,
        "satisfiable\nmodel:\n  ?R0 = unconstrained\n  ?T0 = unconstrained\n  ?G = mu R1. forall T1. (T1 | R1) -> A\n  ?U = mu R1. forall T1. (T1 | R1) -> A\n",
    );
}

#[test]
fn core_reduction_keeps_the_later_conflict_in_source_order() {
    let lower = "assert lower: A <: ?T;";
    let upper = "assert upper: ?T <: B;";
    let generic = "assert generic: forall X. (X) -> tuple[X, X] <: (A) -> tuple[A, B];";
    let recursive = "assert recursive: tuple[?R] <: ?R;";
    // The class pair requires A <: B. The generic alone requires A <: X <: B.
    // The tuple loop is satisfiable and cannot affect either rejection.
    for (assertions, expected) in [
        ([lower, upper, generic, recursive], &[Some("generic")][..]),
        (
            [generic, lower, upper, recursive],
            &[Some("lower"), Some("upper")][..],
        ),
    ] {
        let source = format!(
            "class A; class B; metavar ?T; metavar ?R; {}",
            assertions.join(" ")
        );
        let file = validate_ok(&source);
        for outcome in check_units(
            &work_units(&file),
            &Input::new(&file),
            ModelInput::Source(&source),
            false,
            &source,
        ) {
            let SolveOutcome::Unsatisfiable(core) = outcome else {
                panic!("both independent conflicts reject the complete input");
            };
            let labels = core
                .units()
                .iter()
                .map(|unit| unit.label())
                .collect::<Vec<_>>();
            assert_eq!(labels, expected);
        }
    }
}
