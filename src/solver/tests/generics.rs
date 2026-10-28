//! Tests for generic callable laws, restrictions, deferred instances, and scope conversion.

use crate::frontend::problem::{BoundRef, Callable, ClassId};
use crate::frontend::test_support::{RawProblem, generic_identity, lookup_class};
use crate::solver::input::Input;
use crate::solver::test_support::atom_from_ids;

use super::{check_canonical, check_source, check_source_model, check_source_subsets};

#[test]
fn nested_generic_bindings_preserve_shadowing_after_parameter_reordering() {
    for upper in [
        "forall X, Y. (X) -> (forall X. (X) -> tuple[Y, X])",
        "forall Y, X. (X) -> (forall X. (X) -> tuple[Y, X])",
    ] {
        let source =
            format!("assert forall A, B. (A) -> (forall A. (A) -> tuple[B, A]) <: {upper};");
        check_source(&source, true);
    }
}

#[test]
fn reordered_generic_parameter_roles_are_subtypes_in_both_directions() {
    let first = "forall X, Y. (X, Y) -> X";
    let second = "forall Y, X. (X, Y) -> X";
    for (lower, upper) in [(first, second), (second, first)] {
        check_source(&format!("assert {lower} <: {upper};"), true);
    }
}

#[test]
fn nested_exact_rewrite_matches_its_expansion_in_independent_source_checks() {
    let restricted = "forall X in {A, B}, Y. (X, Y) -> forall Z. (Z) -> tuple[X, Y, Z]";
    let expanded = "(forall Y. (A, Y) -> forall Z. (Z) -> tuple[A, Y, Z])
                  & (forall Y. (B, Y) -> forall Z. (Z) -> tuple[B, Y, Z])";
    check_source(
        &format!(
            "class A; class B;
             assert ({restricted}) <: ({expanded});
             assert ({expanded}) <: ({restricted});"
        ),
        true,
    );
}

#[test]
fn stored_generic_uses_select_independently_and_each_use_shares_its_selection() {
    let declarations = "class Dog; class Cat; metavar ?F; assert forall X. (X) -> X <: ?F;";
    for comparisons in [
        "assert ?F <: (Dog) -> Dog; assert ?F <: (Cat) -> Cat;",
        "assert tuple[?F, ?F] <: tuple[(Dog) -> Dog, (Cat) -> Cat];",
    ] {
        check_source(&format!("{declarations} {comparisons}"), true);
    }
    check_source(
        "class A; class B; assert () -> (forall X. (X) -> never) <: forall T in {A, B}. () -> (forall U. (U) -> T);",
        true,
    );
    check_source(
        "class Dog; class Cat; assert forall X. (X) -> tuple[X, X] <: (Dog) -> tuple[Dog, Cat];",
        false,
    );
}

#[test]
fn generic_selections_apply_before_invariant_argument_comparisons() {
    check_source(
        "class Inv[T];
         assert forall X. (X) -> Inv[X] <: forall Y. (Y) -> Inv[object];",
        true,
    );
}

#[test]
fn a_never_selection_removes_the_complete_lower_return_arm() {
    check_source(
        "class C; assert forall X. () -> (X & C) <: () -> never;",
        true,
    );
}

#[test]
fn generic_callable_laws_hold_under_every_engine_and_independent_checking() {
    let declarations = "class A;";
    let mut problem = RawProblem::new(declarations);
    let a = lookup_class(&problem.declarations, "A");
    let a_type = problem.types.intern_class(a, Vec::new());
    let object = problem.types.intern_class(ClassId::OBJECT, Vec::new());
    let never = problem.types.intern_class(ClassId::NEVER, Vec::new());
    let generic = generic_identity(&mut problem);
    let a_identity = problem.types.intern_callable(vec![a_type], a_type);
    let bottom_function = problem.types.intern_callable(vec![object], never);

    let generic_to_monomorphic = atom_from_ids(&mut problem, generic, a_identity);
    check_canonical(
        declarations,
        &Input::fixture(&problem),
        &[generic_to_monomorphic],
        true,
    );

    let universal_bottom = atom_from_ids(&mut problem, bottom_function, generic);
    check_canonical(
        declarations,
        &Input::fixture(&problem),
        &[universal_bottom],
        true,
    );

    let invalid_universal = atom_from_ids(&mut problem, a_identity, generic);
    check_canonical(
        declarations,
        &Input::fixture(&problem),
        &[invalid_universal],
        false,
    );

    let rigid_parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let tuple_a = problem.types.intern_tuple(vec![a_type]);
    let tuple_body = Callable {
        params: vec![rigid_parameter],
        ret: tuple_a,
    };
    let rigid_to_tuple = problem.types.intern_generic(1, &tuple_body);
    let invalid_rigid_shape = atom_from_ids(&mut problem, generic, rigid_to_tuple);
    check_canonical(
        declarations,
        &Input::fixture(&problem),
        &[invalid_rigid_shape],
        false,
    );
}

#[test]
fn generic_callable_source_laws_have_expected_verdicts() {
    for (source, expected) in [
        ("class A;\nassert forall X. (X) -> X <: (A) -> A;", true),
        ("assert (object) -> never <: forall X. (X) -> X;", true),
        ("class A;\nassert (A) -> A <: forall X. (X) -> X;", false),
        (
            "assert forall X. (X) -> X <: forall Y. (Y) -> object;",
            true,
        ),
        (
            "assert forall Y. (Y) -> object <: forall X. (X) -> X;",
            false,
        ),
        (
            "assert forall X, Y. (X, Y) -> X <: forall Z. (Z, Z) -> Z;",
            true,
        ),
        (
            "assert forall Z. (Z, Z) -> Z <: forall X, Y. (X, Y) -> X;",
            false,
        ),
        (
            "class A;\nclass B;\nassert forall X. (X) -> X <: ((A) -> A) & ((B) -> B);",
            true,
        ),
        (
            "class A;\nassert forall X. (A) -> ((X) -> X) <: (A) -> forall Z. (Z) -> Z;",
            false,
        ),
        (
            "assert forall X. (X) -> X <: (forall Y. (Y) -> Y) -> forall Z. (Z) -> Z;",
            false,
        ),
        (
            "class A;\nassert forall X. (X) -> A <: (forall Y. (Y) -> Y) -> A;",
            true,
        ),
        (
            "assert forall X. (X) -> X <: (forall Y. (Y) -> Y) -> ((never) -> object);",
            true,
        ),
        (
            "class A;\nassert (forall X. (X) -> X) & ((A) -> A) <: never;",
            false,
        ),
        (
            "class A;\nassert (forall X. (X) -> X) & ((A, A) -> A) <: never;",
            true,
        ),
        (
            "class A;\nclass B;\nassert (forall X. (X) -> A | B) <: (forall X. (X) -> A) | (forall X. (X) -> B);",
            false,
        ),
        (
            "class A;\nclass B;\nassert forall X. (X) -> X <: ((A) -> B) | ((B) -> A) | ((A) -> A);",
            true,
        ),
        (
            "class A;\nclass C;\nassert (A | C) -> never <: forall X <: A | C. (X) -> X;",
            true,
        ),
        (
            "class B;\nclass C;\nassert forall Y. ((Y & B) | (Y & C)) -> Y <: forall X <: B | C. (X) -> X;",
            true,
        ),
        (
            "class A;\nclass B;\nclass C;\nassert (C) -> object <: forall X <: tuple[A]. (X & B) -> object;",
            true,
        ),
        (
            "class A;\nclass B;\nassert (A | B) -> never <: forall X in {A, B}. (X) -> X;",
            true,
        ),
        (
            "class A;\nclass B;\nassert forall X in {A, B}. (X) -> X <: (B) -> B;",
            true,
        ),
        (
            "class A;\nclass B;\nassert forall X in {A, B}, Y in {A, B}. (X, Y) -> tuple[X, Y] <: (B, A) -> tuple[B, A];",
            true,
        ),
        (
            "class A;\nclass B;\nclass C;\nassert forall X in {A, B}. (X) -> X <: (C) -> C;",
            false,
        ),
    ] {
        check_source(source, expected);
    }
}

#[test]
fn generic_requirement_source_regressions_have_expected_verdicts() {
    for (source, expected) in [
        // One substituted body shares X across both return requirements.
        // Its witness is ((A) -> A) & ((B) -> B).
        (
            "class A;\nclass B;\nassert forall X. (X) -> X <: (forall Y. (Y) -> Y) -> (((A) -> A) & ((B) -> B));",
            true,
        ),
        // Constructor descent keeps both requirements at one tuple position.
        // Its witness is tuple[((A) -> A) & ((B) -> B)].
        (
            "class A;\nclass B;\nassert forall X. (X) -> X <: (tuple[forall Y. (Y) -> Y]) -> tuple[((A) -> A) & ((B) -> B)];",
            true,
        ),
        // Two callable parameter reversals preserve the nested requirement.
        (
            "class A;\nclass B;\nassert ((forall X. (X) -> X) -> A) -> A <: (((tuple[forall Y. (Y) -> Y]) -> tuple[((A) -> A) & ((B) -> B)]) -> A) -> A;",
            true,
        ),
        // The deferred factor cannot empty X & C during search. The guard
        // still requires C <: D or its own callable instance below D.
        (
            "class A;\nclass C;\nclass D;\nmetavar ?Z;\nassert forall X. (X) -> tuple[X & C, X] <: (forall Y. (Y) -> Y) -> tuple[?Z, (A) -> A];\nassert ?Z <: D;",
            false,
        ),
        // The deferred factor has unknown shape. C remains in X & C,
        // and neither C nor the guard's callable instance is below D.
        (
            "class C;\nclass D;\nassert forall X. (X, X) -> (X & C) <: (forall Y. (Y) -> Y, C) -> D;",
            false,
        ),
        // The deferred choice that returns through Z must keep its outward
        // route. Its widened callable cannot satisfy the rigid identity.
        (
            "class B;\nmetavar ?K;\nmetavar ?Z;\nassert forall X. (X, X) -> tuple[X & ((B) -> ?K), X] <: forall R. (forall Y. (Y) -> Y, ?Z) -> tuple[?Z, (R) -> R];",
            false,
        ),
        (
            "class A;\nclass B;\nassert forall X. (X) -> X <: ((forall Y. (Y) -> Y) & ((object) -> A)) -> ((B) -> A);",
            true,
        ),
        // Converting the nested universal type out of X's scope gives the
        // generic-free witness ((object) -> never) -> A.
        (
            "class A;\nassert forall X. (X) -> A <: ((forall Y. (Y) -> Y) -> A) -> A;",
            true,
        ),
        // The surrounding universal type replaces Y with rigid R. The
        // deferred source forall Z. (Z) -> R widens to object before it is
        // stored, and Z = B satisfies the (B) -> object requirement.
        (
            "class A;\nclass B;\nassert forall X. (X) -> X <: ((forall Y. (forall Z. (Z) -> Y) -> Y) -> A) -> ((((B) -> object) -> never) -> A);",
            true,
        ),
        // Widening R to object makes the (B) -> C requirement fail. Using
        // never in the covariant return would incorrectly accept it.
        (
            "class A;\nclass B;\nclass C;\nassert forall X. (X) -> X <: ((forall Y. (forall Z. (Z) -> Y) -> Y) -> A) -> ((((B) -> C) -> never) -> A);",
            false,
        ),
        // W records forall Y. (Y) -> X1+. The use needs X1+ <: A. This
        // relation holds before and after the link propagates A from X1.
        (
            "class A;\nclass B;\nassert forall W. ((A) -> W) -> W <: (forall X. (X) -> tuple[forall Y. (Y) -> X]) -> tuple[(B) -> A];",
            true,
        ),
        // The lower bound puts A in X1. Its outward proxy must then fail the
        // requirement X1+ <: never.
        (
            "class A;\nclass B;\nassert forall W. ((A) -> W) -> W <: (forall X. (X) -> tuple[forall Y. (Y) -> X]) -> tuple[(B) -> never];",
            false,
        ),
    ] {
        check_source(source, expected);
    }
}

#[test]
fn generic_source_models_close_deferred_selections() {
    check_source_model(
        "metavar ?T;\nassert forall X. (X) -> X <: (forall Y. (Y) -> Y) -> ?T;",
        "satisfiable\nmodel:\n  ?T = object\n",
    );
    check_source_model(
        "class A;\nmetavar ?U;\nassert forall X. (X) -> X <: (?U) -> A;\nassert A <: ?U;",
        "satisfiable\nmodel:\n  ?U = A\n",
    );
    check_source_model(
        "class A;\nclass B extends A;\nmetavar ?V;\nassert forall X. (X) -> X <: (forall Y. (Y) -> Y) -> ((?V) -> A);\nassert B <: ?V;",
        "satisfiable\nmodel:\n  ?V = B\n",
    );
    check_source_model(
        // The proxy of G lives below rigid Z. It can use (Z) -> Z as its
        // instance while the public assignment for G stays generic.
        "metavar ?G;\nassert forall Y. (Y) -> Y <: ?G;\nassert forall X. (X) -> X <: forall Z. (?G) -> ((Z) -> Z);",
        "satisfiable\nmodel:\n  ?G = forall T0. (T0) -> T0\n",
    );
    check_source_model(
        "class A;\nclass B;\nmetavar ?H;\nassert forall Y. (Y) -> Y <: ?H;\nassert forall X. (X) -> ?H <: (A) -> ((B) -> B);",
        "satisfiable\nmodel:\n  ?H = forall T0. (T0) -> T0\n",
    );
    check_source_model(
        // Z becomes rigid below X. Widening it to object removes Y from
        // forall Y. () -> (Y | Z), so X stores () -> object directly.
        "class A;\nmetavar ?T;\nassert forall X. (X) -> X <: ((forall Z. (forall Y. () -> (Y | Z)) -> Z) -> A) -> ?T;",
        "satisfiable\nmodel:\n  ?T = ((() -> object) -> never) -> A\n",
    );
    check_source_model(
        "class A;\nmetavar ?T;\nassert forall X. (X & tuple[A]) -> X <: ?T;",
        "satisfiable\nmodel:\n  ?T = forall T0. (T0 & tuple[A]) -> T0\n",
    );
}

#[test]
fn generic_source_models_close_scope_conversions() {
    check_source_model(
        "metavar ?T;\nassert forall X. (X) -> tuple[X, tuple[X]] <: forall Y. (Y) -> tuple[Y, ?T];",
        "satisfiable\nmodel:\n  ?T = tuple[object]\n",
    );
    check_source_model(
        "class A;\nmetavar ?T;\nassert forall X. (X) -> ((X) -> A) <: forall Y. (Y) -> ?T;",
        "satisfiable\nmodel:\n  ?T = (never) -> A\n",
    );
    check_source_model(
        "metavar ?U;\nassert forall X. (X) -> tuple[X, X] <: forall Z. (forall Y. (Y) -> Y) -> tuple[(Z) -> Z, ?U];",
        "satisfiable\nmodel:\n  ?U = (never) -> object\n",
    );
    check_source_model(
        "class A;\nmetavar ?V;\nassert forall X. ((?V) -> X) -> X <: (forall S. (S) -> tuple[S]) -> object;\nassert A <: ?V;",
        "satisfiable\nmodel:\n  ?V = A\n",
    );
    check_source_model(
        "class A;\nclass B;\nmetavar ?V;\nmetavar ?T;\nassert forall X. (X, X) -> tuple[X] <: (A, ?V) -> ?T;\nassert B <: ?V;",
        "satisfiable\nmodel:\n  ?V = B\n  ?T = tuple[A | B]\n",
    );
    check_source_model(
        "class A;\nmetavar ?T;\nassert (?T) -> A <: forall Z. (forall W. (W) -> Z) -> A;",
        "satisfiable\nmodel:\n  ?T = forall T0. (T0) -> object\n",
    );
}

#[test]
fn restricted_source_models_render_rewritten_types() {
    check_source_model(
        include_str!("../../../tests/data/solve/sat/restricted_generic_model.input"),
        include_str!("../../../tests/data/solve/sat/restricted_generic_model.stdout"),
    );
    check_source_model(
        include_str!("../../../tests/data/solve/sat/restricted_metavar_disappears.input"),
        include_str!("../../../tests/data/solve/sat/restricted_metavar_disappears.stdout"),
    );
    check_source_model(
        include_str!("../../../tests/data/solve/sat/rewritten_scope_model.input"),
        include_str!("../../../tests/data/solve/sat/rewritten_scope_model.stdout"),
    );
}

#[test]
fn restricted_scope_requirements_keep_the_rewritten_witness() {
    check_source_model(
        "class B;\nmetavar ?T;\n\
         assert forall Z. (Z) -> Z <: ?T;\n\
         assert (() -> ?T) -> B\n\
             <: forall X. (() -> forall Y. (Y & X) -> (Y & X)) -> B;",
        "satisfiable\nmodel:\n  ?T = (forall T0. (never) -> T0) | (forall T0. (T0) -> T0)\n",
    );
}

#[test]
fn generic_source_models_track_proxies_of_declared_references() {
    check_source_model(
        "class A;\nclass B;\nmetavar ?G;\nassert forall X. (X) -> X <: (?G) -> (((A) -> A) & ((B) -> B));\nassert forall Y. (Y) -> Y <: ?G;",
        "satisfiable\nmodel:\n  ?G = forall T0. (T0) -> T0\n",
    );
    check_source_model(
        "class A;\nmetavar ?T;\nmetavar ?U;\nassert tuple[?T] <: ?U;\nassert forall X. (X) -> X <: (?U) -> tuple[A];\nassert A <: ?T;",
        "satisfiable\nmodel:\n  ?T = A\n  ?U = tuple[A]\n",
    );
    check_source_model(
        "class A;\nclass B;\nclass C extends B;\nmetavar ?K;\nmetavar ?G;\nassert forall Y. (Y) -> ?K <: ?G;\nassert forall X. (X) -> X <: (?G) -> ((A) -> B);\nassert C <: ?K;",
        "satisfiable\nmodel:\n  ?K = C\n  ?G = forall T0. (T0) -> C\n",
    );
}

#[test]
fn generic_source_models_preserve_stored_generic_factors() {
    check_source_model(
        "metavar ?T;\nassert forall X. (X) -> X <: ?T;\nassert forall Y. () -> Y <: ?T;",
        "satisfiable\nmodel:\n  ?T = (forall T0. () -> T0) | (forall T0. (T0) -> T0)\n",
    );
    check_source_model(
        "class A;\nmetavar ?T;\nassert (forall X. (X) -> X) -> A <: ?T;\nassert ((A) -> A) -> A <: ?T;",
        "satisfiable\nmodel:\n  ?T = (((A) -> A) -> A) | ((forall T0. (T0) -> T0) -> A)\n",
    );
    check_source_model(
        "class A;\nmetavar ?T;\nassert ((forall X. (X) -> X) -> A) & (((A) -> A) -> A) <: ?T;",
        "satisfiable\nmodel:\n  ?T = (((A) -> A) -> A) & ((forall T0. (T0) -> T0) -> A)\n",
    );
}

#[test]
fn generic_model_fixture_holds_under_independent_checking() {
    check_source_model(
        include_str!("../../../tests/data/solve/sat/generic_model.input"),
        include_str!("../../../tests/data/solve/sat/generic_model.stdout"),
    );
}

#[test]
fn separate_arbitrary_parameters_keep_their_introduction_positions() {
    check_source(
        "assert forall X, Y. (X, Y) -> tuple[X, Y] <: forall Z, W. (Z, W) -> tuple[Z | W, Z | W];",
        true,
    );
}

#[test]
fn a_closed_generic_bound_uses_its_recorded_selection() {
    check_source_model(
        include_str!("../../../tests/data/solve/sat/generic_class_shared.input"),
        include_str!("../../../tests/data/solve/sat/generic_class_shared.stdout"),
    );
    check_source_model(
        "class B; class A extends D; class D; metavar ?X;
        assert (((A) -> D) -> B) & (((A) -> A) -> B) <: ?X;
        assert ?X <: (forall Z. (Z) -> Z) -> B;",
        "satisfiable\nmodel:\n  ?X = ((A) -> D) -> B\n",
    );
}

#[test]
fn removing_an_unused_binder_still_converts_nested_generics_for_storage() {
    check_source(
        "class A; metavar ?T;
        assert forall X. (A) -> ((X) -> A) <: (A) -> forall Z. (forall Y. (?T) -> (Y | Z)) -> A;
        assert forall W. (W) -> W <: ?T;",
        true,
    );
}

#[test]
fn generic_equation_membership_survives_normalization_and_variable_links() {
    // B <: A removes B from a return union. It also removes B & W from
    // A | (B & W), which makes W unused and removes the whole binder.
    for (lower, expected) in [
        ("forall W. (W) -> A | B", "forall T0. (T0) -> A"),
        ("forall W. (A | (B & W)) -> A", "(A) -> A"),
    ] {
        for linked in [false, true] {
            let link = if linked {
                "metavar ?G; assert ?F <: ?G;"
            } else {
                ""
            };
            let mut witness = format!("satisfiable\nmodel:\n  ?F = {expected}\n");
            if linked {
                witness.push_str("  ?G = ");
                witness.push_str(expected);
                witness.push('\n');
            }
            check_source_model(
                &format!(
                    "class A; class B extends A; metavar ?F;
                    assert {lower} <: ?F; {link}"
                ),
                &witness,
            );
        }
    }
}

#[test]
fn each_deferred_requirement_passes_its_own_instance_in_every_order() {
    let prefix = "class A; class C; class D; metavar ?Z; metavar ?W;";
    let first =
        "assert first: forall X. (X) -> tuple[X & C, X] <: (forall Y. (Y) -> Y) -> tuple[?Z, ?W];";
    let guard = "assert guard: ?Z <: D;";
    let demand = "assert demand: ?W <: (A) -> A;";
    for order in [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ] {
        let assertions = [first, guard, demand];
        let source = format!(
            "{prefix} {}",
            order.map(|index| assertions[index]).join(" ")
        );
        let conflict = order
            .iter()
            .enumerate()
            .filter(|(_, assertion)| **assertion < 2)
            .fold(0, |mask, (index, _)| mask | 1 << index);
        check_source_subsets(&source, &[conflict]);
    }
    check_source_model(
        &format!("{prefix} {first}"),
        "satisfiable\nmodel:\n  ?Z = C\n  ?W = object\n",
    );
    check_source_model(
        &format!("{prefix} {first} {demand}"),
        "satisfiable\nmodel:\n  ?Z = never\n  ?W = (A) -> A\n",
    );
}
