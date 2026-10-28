//! Check expected values and failed choices under all three engines.

use crate::solver::input::Input;
use crate::solver::test_support::{ModelInput, validate_ok};
use crate::solver::work_units;

use super::{check_source, check_source_model, check_source_subsets, check_units};

#[test]
fn a_variable_loop_keeps_every_lower_expression_when_checking_a_union() {
    let source = "class A; class B; metavar ?X; metavar ?Y;
        assert A <: ?X; assert ?X <: ?Y; assert ?Y <: ?X;
        assert ?X <: A | B;";
    check_source_model(source, "satisfiable\nmodel:\n  ?X = A\n  ?Y = A\n");
    check_source_model(
        &format!("{source} assert B <: ?X;"),
        "satisfiable\nmodel:\n  ?X = A | B\n  ?Y = A | B\n",
    );
}

#[test]
fn written_parts_that_already_match_do_not_add_variable_bounds() {
    for comparison in [
        "?Y <: ?X | ?Y",
        "?Y & B <: ?X | ?Y",
        "(?Y & B) | tuple[A] <: ?X | ?Y | tuple[A]",
    ] {
        check_source_model(
            &format!(
                "class A; class B; metavar ?X; metavar ?Y;
                assert A <: ?Y; assert {comparison};"
            ),
            "satisfiable\nmodel:\n  ?X = never\n  ?Y = A\n",
        );
    }
    // Matching Y does not cover B in the first comparison. Matching tuple
    // constructors does not cover different elements in the second one.
    check_source(
        "class A; class B; metavar ?X; metavar ?Y;
        assert A <: ?Y; assert ?Y <: A;
        assert ?Y | B <: ?X | ?Y; assert ?X <: A;",
        false,
    );
    check_source(
        "class A; class B; metavar ?X; metavar ?Y;
        assert A <: ?Y; assert ?Y <: A;
        assert tuple[?Y] <: ?X | tuple[B]; assert ?X <: never;",
        false,
    );
}

#[test]
fn lower_intersections_choose_upper_arms_separately() {
    let prefix = "class A; class B; class E; class C extends B; class D extends E;
        metavar ?X; assert C & A <: ?X; assert D & A <: ?X;";
    check_source(&format!("{prefix} assert ?X & A <: B | E;"), true);
    check_source(
        &format!("{prefix} assert (?X & A <: B) or (?X & A <: E);"),
        false,
    );
}

#[test]
fn incompatible_fixed_shapes_remove_only_their_expanded_arm() {
    let prefix = "class A; class B; metavar ?X;
        assert A | tuple[B] <: ?X; assert ?X <: A | tuple[B];";
    check_source(
        &format!("{prefix} assert ?X & tuple[object] <: tuple[B];"),
        true,
    );
    check_source(
        &format!("{prefix} assert (?X <: tuple[B]) or (tuple[object] <: tuple[B]);"),
        false,
    );
}

#[test]
fn an_upper_variable_receives_the_complete_intersection() {
    check_source_model(
        "class A; class B; metavar ?Y;
        assert A & B <: ?Y; assert ?Y <: A; assert ?Y <: B;",
        "satisfiable\nmodel:\n  ?Y = A & B\n",
    );
    check_source(
        "class A; class B; metavar ?Y;
        assert (A <: ?Y) or (B <: ?Y); assert ?Y <: A; assert ?Y <: B;",
        false,
    );
}

#[test]
fn unguarded_self_contributions_have_finite_witnesses() {
    for relation in ["?X & A <: ?X", "tuple[?X & A] <: tuple[?X]"] {
        check_source_model(
            &format!(
                "class A; class B; metavar ?X;
            assert {relation}; assert B <: ?X;"
            ),
            "satisfiable\nmodel:\n  ?X = B\n",
        );
    }
    check_source_model(
        "class A; class B; metavar ?X; metavar ?Y;
        assert ?X & A <: ?Y; assert ?Y <: ?X; assert B <: ?Y;",
        "satisfiable\nmodel:\n  ?X = B\n  ?Y = B\n",
    );
}

#[test]
fn sequential_elimination_keeps_other_variables_contributions() {
    check_source_model(
        "class A; class B1; class B2; metavar ?X; metavar ?Y;
        assert ?Y <: ?X; assert B1 <: ?X; assert ?X & A <: ?Y; assert B2 <: ?Y;",
        "satisfiable\nmodel:\n  ?X = B1 | B2\n  ?Y = A & B1 | B2\n",
    );
}

#[test]
fn failed_constructor_alternative_rolls_back_its_bounds() {
    // X precedes Y in the type order. The first part of the right-side union
    // adds A to X before B <: C fails. The second part needs X=B and Y=A.
    check_source_model(
        "class A; class B; class C; metavar ?X; metavar ?Y;
        assert tuple[A, B] <: tuple[?X, C] | tuple[?Y, ?X]; assert ?X <: B;",
        "satisfiable\nmodel:\n  ?X = B\n  ?Y = A\n",
    );
}

#[test]
fn a_discarded_alternative_does_not_recheck_its_variable_readers() {
    // The first part checks X & A <: B, then fails C <: D. That check must be
    // discarded before E is added to X after choosing the second part.
    check_source_model(
        "class B; class A; class C; class D; class E; class Box[+T];
        metavar ?X; metavar ?Y;
        assert B <: ?X;
        assert tuple[Box[?X & A], C] <: tuple[Box[B], D] | tuple[?Y, ?Y];
        assert E <: ?X;",
        "satisfiable\nmodel:\n  ?X = B | E\n  ?Y = C | Box[B & A | A & E]\n",
    );
}

#[test]
fn links_and_later_contributions_recheck_intersections() {
    check_source(
        "class A; class B; class C; metavar ?X; metavar ?Y;
        assert ?Y & A <: B; assert ?X <: ?Y; assert C <: ?X;",
        false,
    );
    check_source(
        "class A; class B; class C extends B; metavar ?X; metavar ?Y;
        assert ?Y & A <: B; assert ?X <: ?Y; assert C <: ?X;",
        true,
    );
    check_source_model(
        "class A; metavar ?X; metavar ?Y;
        assert A <: ?Y; assert ?Y <: ?X; assert ?X & ?Y <: A;",
        "satisfiable\nmodel:\n  ?X = A\n  ?Y = A\n",
    );
}

#[test]
fn the_eighth_union_alternative_retains_its_required_lower_bound() {
    let source = include_str!("../../../benchmarks/synthetic/24_eight_way_union_choice.input");
    check_source_model(
        source,
        "satisfiable\nmodel:\n  ?T0 = never\n  ?T1 = never\n  ?T2 = never\n  ?T3 = never\n  ?T4 = never\n  ?T5 = never\n  ?T6 = never\n  ?T7 = a\n",
    );
}

#[test]
fn finite_rejections_remain_valid_in_every_containing_subset() {
    // Each bit identifies one assertion. The masks list the smallest failing
    // combinations. Other combinations pass with a permitted choice, or with
    // never when no rule requires an expression below the variable.
    let cases: &[(&str, &[usize])] = &[
        ("class A; class B; class E; class C extends B; class D extends E;
          metavar ?X; assert C & A <: ?X; assert D & A <: ?X; assert ?X & A <: B | E;", &[]),
        ("class A; class B; class E; class C extends B; class D extends E;
          metavar ?X; assert C & A <: ?X; assert D & A <: ?X; assert (?X & A <: B) or (?X & A <: E);", &[0b111]),
        ("class A; class B; metavar ?X; assert A | tuple[B] <: ?X;
          assert ?X <: A | tuple[B]; assert ?X & tuple[object] <: tuple[B];", &[]),
        ("class A; class B; metavar ?X; assert A | tuple[B] <: ?X;
          assert ?X <: A | tuple[B]; assert (?X <: tuple[B]) or (tuple[object] <: tuple[B]);", &[0b101]),
        ("class A; class B; metavar ?Y; assert A & B <: ?Y; assert ?Y <: A; assert ?Y <: B;", &[]),
        ("class A; class B; metavar ?Y; assert (A <: ?Y) or (B <: ?Y); assert ?Y <: A; assert ?Y <: B;", &[0b111]),
        ("class A; class B1; class B2; metavar ?X; metavar ?Y;
          assert ?Y <: ?X; assert B1 <: ?X; assert ?X & A <: ?Y; assert B2 <: ?Y;", &[]),
        ("class A; class B; class C; metavar ?X; metavar ?Y;
          assert ?Y & A <: B; assert ?X <: ?Y; assert C <: ?X;", &[0b111]),
    ];
    for (source, conflicts) in cases {
        check_source_subsets(source, conflicts);
    }
}

#[test]
fn subsets_keep_the_full_input_environment_with_generic_assertions() {
    let source = "class A; metavar ?X;
        assert A <: ?X; assert forall T. (T) -> T <: (A) -> A;";
    let file = validate_ok(source);
    let input = Input::new(&file);
    let units = work_units(&file);
    let selected = &units[..1];
    let formulas = selected.iter().map(|unit| unit.formula).collect::<Vec<_>>();
    check_units(
        selected,
        &input,
        ModelInput::Canonical {
            declarations: source,
            input: &input,
            formulas: &formulas,
        },
        true,
        source,
    );
    check_units(&units, &input, ModelInput::Source(source), true, source);
}

#[test]
fn variable_loops_through_unions_keep_their_upper_checks() {
    let source = "class A; class B; metavar ?X; metavar ?Y;
        assert A | ?Y <: ?X; assert B | ?X <: ?Y;
        assert ?X <: A | B;";
    check_source_model(source, "satisfiable\nmodel:\n  ?X = A | B\n  ?Y = A | B\n");
    check_source(&format!("{source} assert ?Y <: A;"), false);
}
