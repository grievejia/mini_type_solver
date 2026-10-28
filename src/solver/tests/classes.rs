//! Tests for class variance, inherited arguments, invariant transfers, and closed models.

use super::model_text;

use crate::frontend::problem::{BoundRef, Callable, ClassId};
use crate::frontend::test_support::{RawProblem, generic_identity, lookup_class, lookup_metavar};
use crate::solver::input::Input;

use super::super::test_support::{ModelInput, atom_from_ids, validate_ok};
use super::super::work_units;
use super::{check_canonical, check_source, check_source_model, check_units};

#[test]
fn erased_class_reference_cycles_allow_inherited_comparisons() {
    for (argument, normalized) in [
        ("object | B", "object"),
        ("B & never", "never"),
        ("tuple[object | B]", "tuple[object]"),
    ] {
        let source = format!(
            "class G[T]; class A extends G[{argument}]; class B extends G[A]; assert A <: G[{normalized}]; assert B <: G[A];"
        );
        check_source(&source, true);
    }
}

#[test]
fn class_instances_follow_declared_variance_and_root_shape() {
    let declarations = "class Animal; class Dog extends Animal; class Other; class Co[+T]; class Contra[-T]; class Inv[T]; class Mixed[+P, -Q, R];";
    let mut problem = RawProblem::new(declarations);
    let animal = problem
        .types
        .intern_class(lookup_class(&problem.declarations, "Animal"), Vec::new());
    let dog = problem
        .types
        .intern_class(lookup_class(&problem.declarations, "Dog"), Vec::new());
    let other = problem
        .types
        .intern_class(lookup_class(&problem.declarations, "Other"), Vec::new());
    let object = problem.types.intern_class(ClassId::OBJECT, Vec::new());
    let never = problem.types.intern_class(ClassId::NEVER, Vec::new());
    let mut instances = Vec::new();
    for name in ["Co", "Contra", "Inv"] {
        let class = lookup_class(&problem.declarations, name);
        instances.push((
            problem.types.intern_class(class, vec![dog]),
            problem.types.intern_class(class, vec![animal]),
        ));
    }
    let mixed = lookup_class(&problem.declarations, "Mixed");
    let mixed_lower = problem.types.intern_class(mixed, vec![dog, animal, dog]);
    let mixed_upper = problem.types.intern_class(mixed, vec![animal, dog, dog]);
    let mixed_wrong_invariant = problem.types.intern_class(mixed, vec![animal, dog, animal]);
    let (co_dog, co_animal) = instances[0];
    let (contra_dog, contra_animal) = instances[1];
    let (inv_dog, inv_animal) = instances[2];
    let inv = lookup_class(&problem.declarations, "Inv");
    let inv_other = problem.types.intern_class(inv, vec![other]);
    let inv_never = problem.types.intern_class(inv, vec![never]);
    let overlap = problem.types.intern_intersection(vec![inv_dog, inv_other]);
    let tuple = problem.types.intern_tuple(vec![dog]);
    let callable = problem.types.intern_callable(vec![dog], animal);
    let disjoint_tuple = problem.types.intern_intersection(vec![inv_dog, tuple]);
    let disjoint_callable = problem.types.intern_intersection(vec![inv_dog, callable]);
    let dog_or_other = problem.types.intern_union(vec![dog, other]);
    let inside_union = problem.types.intern_class(inv, vec![dog_or_other]);
    let outside_union = problem.types.intern_union(vec![inv_dog, inv_other]);
    for (lower, upper, expected) in [
        (mixed_lower, mixed_upper, true),
        (mixed_upper, mixed_lower, false),
        (mixed_lower, mixed_wrong_invariant, false),
        (co_dog, co_animal, true),
        (co_animal, co_dog, false),
        (contra_animal, contra_dog, true),
        (contra_dog, contra_animal, false),
        (inv_dog, inv_animal, false),
        (inv_animal, inv_dog, false),
        (never, inv_dog, true),
        (inv_dog, object, true),
        (inv_never, never, false),
        (overlap, never, false),
        (disjoint_tuple, never, true),
        (disjoint_callable, never, true),
        (inside_union, outside_union, false),
        (outside_union, inside_union, false),
    ] {
        let formula = atom_from_ids(&mut problem, lower, upper);
        check_canonical(
            declarations,
            &Input::fixture(&problem),
            &[formula],
            expected,
        );
    }
}

#[test]
fn ancestor_arguments_substitute_live_values_in_c3_order() {
    let declarations = "class Animal; class Dog extends Animal; class Hidden extends Animal; class Base[+T]; class Left[T] extends Base[tuple[T]]; class Right[T] extends Base[tuple[T]]; class Diamond[T] extends Left[T], Right[T]; class Plain extends Diamond[Dog]; class HiddenLeaf extends Base[Hidden];";
    let mut problem = RawProblem::new(declarations);
    let animal = problem
        .types
        .intern_class(lookup_class(&problem.declarations, "Animal"), Vec::new());
    let dog = problem
        .types
        .intern_class(lookup_class(&problem.declarations, "Dog"), Vec::new());
    let base = lookup_class(&problem.declarations, "Base");
    let diamond = lookup_class(&problem.declarations, "Diamond");
    let plain = problem
        .types
        .intern_class(lookup_class(&problem.declarations, "Plain"), Vec::new());
    let hidden_leaf = problem.types.intern_class(
        lookup_class(&problem.declarations, "HiddenLeaf"),
        Vec::new(),
    );
    let tuple_animal = problem.types.intern_tuple(vec![animal]);
    let base_tuple = problem.types.intern_class(base, vec![tuple_animal]);
    let base_animal = problem.types.intern_class(base, vec![animal]);
    let diamond_dog = problem.types.intern_class(diamond, vec![dog]);
    let bound = problem.types.intern_bound(BoundRef::new(0, 0));
    let diamond_selection = problem.types.intern_class(diamond, vec![bound]);
    let lower_body = Callable {
        params: vec![bound],
        ret: diamond_selection,
    };
    let lower = problem.types.intern_generic(1, &lower_body);
    let bound_tuple = problem.types.intern_tuple(vec![bound]);
    let base_bound = problem.types.intern_class(base, vec![bound_tuple]);
    let upper_body = Callable {
        params: vec![bound],
        ret: base_bound,
    };
    let upper = problem.types.intern_generic(1, &upper_body);
    for (lower, upper, expected) in [
        (lower, upper, true),
        (diamond_dog, base_tuple, true),
        (plain, base_tuple, true),
        (base_tuple, diamond_dog, false),
        (hidden_leaf, base_animal, true),
    ] {
        let formula = atom_from_ids(&mut problem, lower, upper);
        check_canonical(
            declarations,
            &Input::fixture(&problem),
            &[formula],
            expected,
        );
    }
}

#[test]
fn invariant_arguments_share_outer_values_and_separate_inner_binders() {
    let declarations =
        "class Dog; class Inv[T]; class Parent[+T]; class Child[T] extends Parent[T]; metavar ?T;";
    let mut problem = RawProblem::new(declarations);
    let dog = problem
        .types
        .intern_class(lookup_class(&problem.declarations, "Dog"), Vec::new());
    let inv = lookup_class(&problem.declarations, "Inv");
    let parent = lookup_class(&problem.declarations, "Parent");
    let child = lookup_class(&problem.declarations, "Child");
    let selected = lookup_metavar(&problem.declarations, "T");
    let selected = problem.types.types().metavar_type(selected);
    let inv_selected = problem.types.intern_class(inv, vec![selected]);
    let inv_dog = problem.types.intern_class(inv, vec![dog]);
    let equality = atom_from_ids(&mut problem, inv_selected, inv_dog);
    let outcomes = check_canonical(declarations, &Input::fixture(&problem), &[equality], true);
    for outcome in outcomes {
        assert_eq!(model_text(&outcome), "satisfiable\nmodel:\n  ?T = Dog\n");
    }

    let inner = problem.types.intern_bound(BoundRef::new(0, 0));
    let outer = problem.types.intern_bound(BoundRef::new(1, 0));
    let body = Callable {
        params: vec![inner],
        ret: outer,
    };
    let inner_generic = problem.types.intern_generic(1, &body);
    let inner_inv = problem.types.intern_class(inv, vec![inner_generic]);
    let body = Callable {
        params: Vec::new(),
        ret: inner_inv,
    };
    let outer_generic = problem.types.intern_generic(1, &body);
    // Different outer syntax shares the same outer selection in both
    // invariant directions. Only the argument-owned binder is fresh.
    let wider_parameter = problem.types.intern_union(vec![inner, dog]);
    let upper_inner_body = Callable {
        params: vec![wider_parameter],
        ret: outer,
    };
    let upper_inner = problem.types.intern_generic(1, &upper_inner_body);
    let upper_inv = problem.types.intern_class(inv, vec![upper_inner]);
    let upper_body = Callable {
        params: Vec::new(),
        ret: upper_inv,
    };
    let upper = problem.types.intern_generic(1, &upper_body);
    let formula = atom_from_ids(&mut problem, outer_generic, upper);
    check_canonical(declarations, &Input::fixture(&problem), &[formula], true);

    let object = problem.types.intern_class(ClassId::OBJECT, Vec::new());
    let child_selection = problem.types.intern_class(child, vec![inner]);
    let lower_body = Callable {
        params: vec![inner],
        ret: child_selection,
    };
    let lower = problem.types.intern_generic(1, &lower_body);
    let fixed_parent = problem.types.intern_class(parent, vec![object]);
    let upper_body = Callable {
        params: vec![inner],
        ret: fixed_parent,
    };
    let upper = problem.types.intern_generic(1, &upper_body);
    let formula = atom_from_ids(&mut problem, lower, upper);
    check_canonical(declarations, &Input::fixture(&problem), &[formula], true);

    let lower = problem.types.intern_callable(vec![inv_selected], object);
    let upper_inv = problem.types.intern_class(inv, vec![inner]);
    let upper_body = Callable {
        params: vec![upper_inv],
        ret: object,
    };
    let upper = problem.types.intern_generic(1, &upper_body);
    let formula = atom_from_ids(&mut problem, lower, upper);
    check_canonical(declarations, &Input::fixture(&problem), &[formula], false);
}

#[test]
fn class_argument_deferred_choices_receive_later_instances() {
    let declarations = "class A; class B; class Co[+T]; class Pair[+L, +R];";
    let mut problem = RawProblem::new(declarations);
    let co = lookup_class(&problem.declarations, "Co");
    let pair = lookup_class(&problem.declarations, "Pair");
    let a = problem
        .types
        .intern_class(lookup_class(&problem.declarations, "A"), Vec::new());
    let b = problem
        .types
        .intern_class(lookup_class(&problem.declarations, "B"), Vec::new());
    let bound = problem.types.intern_bound(BoundRef::new(0, 0));
    let inner_body = Callable {
        params: vec![bound],
        ret: bound,
    };
    let generic_argument = problem.types.intern_generic(1, &inner_body);
    let source = problem.types.intern_class(co, vec![generic_argument]);
    let a_identity = problem.types.intern_callable(vec![a], a);
    let b_identity = problem.types.intern_callable(vec![b], b);
    let co_a = problem.types.intern_class(co, vec![a_identity]);
    let co_b = problem.types.intern_class(co, vec![b_identity]);
    let lower_tuple = problem.types.intern_tuple(vec![bound, bound]);
    let upper_tuple = problem.types.intern_tuple(vec![co_a, co_b]);
    let lower_pair = problem.types.intern_class(pair, vec![bound, bound]);
    let upper_pair = problem.types.intern_class(pair, vec![co_a, co_b]);
    // The selection must include the generic source and meet both slots.
    // Co[(A) -> A] & Co[(B) -> B] is a witness in each case.
    for (lower_ret, upper_ret) in [(lower_tuple, upper_tuple), (lower_pair, upper_pair)] {
        let lower_body = Callable {
            params: vec![bound],
            ret: lower_ret,
        };
        let lower = problem.types.intern_generic(1, &lower_body);
        let upper = problem.types.intern_callable(vec![source], upper_ret);
        let formula = atom_from_ids(&mut problem, lower, upper);
        check_canonical(declarations, &Input::fixture(&problem), &[formula], true);
    }
}

#[test]
fn exact_class_copies_follow_later_values_in_both_storage_kinds() {
    let declarations = "class Dog; class Inv[T]; metavar ?T; metavar ?M;";
    let mut problem = RawProblem::new(declarations);
    let dog = problem
        .types
        .intern_class(lookup_class(&problem.declarations, "Dog"), Vec::new());
    let inv = lookup_class(&problem.declarations, "Inv");
    let (t, m) = (
        lookup_metavar(&problem.declarations, "T"),
        lookup_metavar(&problem.declarations, "M"),
    );
    let t = problem.types.types().metavar_type(t);
    let m = problem.types.types().metavar_type(m);
    let x = problem.types.intern_bound(BoundRef::new(0, 0));
    let inv_x = problem.types.intern_class(inv, vec![x]);
    let body = Callable {
        params: vec![x],
        ret: inv_x,
    };
    let lower = problem.types.intern_generic(1, &body);
    let upper = problem.types.intern_callable(vec![t], m);
    let moved = atom_from_ids(&mut problem, lower, upper);
    let later = atom_from_ids(&mut problem, dog, t);
    for outcome in check_canonical(
        declarations,
        &Input::fixture(&problem),
        &[moved, later],
        true,
    ) {
        assert_eq!(
            model_text(&outcome),
            "satisfiable\nmodel:\n  ?T = Dog\n  ?M = Inv[Dog]\n"
        );
    }

    let generic = generic_identity(&mut problem);
    let inv_t = problem.types.intern_class(inv, vec![t]);
    let upper = problem.types.intern_callable(vec![inv_t], inv_t);
    let moved = atom_from_ids(&mut problem, generic, upper);
    let later = atom_from_ids(&mut problem, dog, t);
    let limit = atom_from_ids(&mut problem, t, dog);
    check_canonical(
        declarations,
        &Input::fixture(&problem),
        &[moved, later, limit],
        true,
    );
}

#[test]
fn negative_class_results_accept_demanded_arms_and_recheck_their_sources() {
    let declarations = "class Dog; class Inv[T]; metavar ?T; metavar ?M;";
    let mut problem = RawProblem::new(declarations);
    let dog = problem
        .types
        .intern_class(lookup_class(&problem.declarations, "Dog"), Vec::new());
    let inv = lookup_class(&problem.declarations, "Inv");
    let object = problem.types.intern_class(ClassId::OBJECT, Vec::new());
    let (t, m) = (
        lookup_metavar(&problem.declarations, "T"),
        lookup_metavar(&problem.declarations, "M"),
    );
    let t = problem.types.types().metavar_type(t);
    let m = problem.types.types().metavar_type(m);
    let inv_t = problem.types.intern_class(inv, vec![t]);
    let inv_dog = problem.types.intern_class(inv, vec![dog]);
    let callback = problem.types.intern_callable(vec![inv_t], object);
    let required = problem.types.intern_callable(vec![inv_dog], object);
    let upper = problem.types.intern_callable(vec![callback], m);
    let identity = generic_identity(&mut problem);
    let moved = atom_from_ids(&mut problem, identity, upper);
    let demanded = atom_from_ids(&mut problem, m, required);
    for outcome in check_canonical(
        declarations,
        &Input::fixture(&problem),
        &[moved, demanded],
        true,
    ) {
        assert_eq!(
            model_text(&outcome),
            "satisfiable\nmodel:\n  ?T = Dog\n  ?M = (Inv[Dog]) -> object\n"
        );
    }

    let y = problem.types.intern_bound(BoundRef::new(0, 0));
    let inv_y = problem.types.intern_class(inv, vec![y]);
    let callback = problem.types.intern_callable(vec![inv_y], object);
    let body = Callable {
        params: vec![callback],
        ret: m,
    };
    let universal = problem.types.intern_generic(1, &body);
    let moved = atom_from_ids(&mut problem, identity, universal);
    // Moving the callback outward makes a general result. Moving ?M
    // into another selection must create generic-free proxies of that general
    // result.
    let upper = problem.types.intern_callable(vec![m], m);
    let repeated = atom_from_ids(&mut problem, identity, upper);
    check_canonical(
        declarations,
        &Input::fixture(&problem),
        &[moved, repeated],
        true,
    );
    let moved = atom_from_ids(&mut problem, identity, universal);
    let demanded = atom_from_ids(&mut problem, m, required);
    // Inv[Dog] cannot be below Inv[Y] for every arbitrary Y. The pending
    // source bound must reject this demanded arm even after D grows.
    check_canonical(
        declarations,
        &Input::fixture(&problem),
        &[moved, demanded],
        false,
    );
}

#[test]
fn retained_negative_class_arguments_copy_only_independent_references() {
    let declarations = "class Dog; class Inv[T]; metavar ?T; metavar ?M;";
    let mut problem = RawProblem::new(declarations);
    let dog = problem
        .types
        .intern_class(lookup_class(&problem.declarations, "Dog"), Vec::new());
    let inv = lookup_class(&problem.declarations, "Inv");
    let object = problem.types.intern_class(ClassId::OBJECT, Vec::new());
    let (t, m) = (
        lookup_metavar(&problem.declarations, "T"),
        lookup_metavar(&problem.declarations, "M"),
    );
    let t = problem.types.types().metavar_type(t);
    let m = problem.types.types().metavar_type(m);
    let z = problem.types.intern_bound(BoundRef::new(0, 0));
    let x = problem.types.intern_bound(BoundRef::new(1, 0));
    let parameter = problem.types.intern_intersection(vec![z, x]);
    let inv_parameter = problem.types.intern_class(inv, vec![parameter]);
    let inv_z = problem.types.intern_class(inv, vec![z]);
    let body = Callable {
        params: vec![inv_parameter],
        ret: inv_z,
    };
    let retained = problem.types.intern_generic(1, &body);
    let outer_x = problem.types.intern_bound(BoundRef::new(0, 0));
    let body = Callable {
        params: vec![outer_x],
        ret: retained,
    };
    let lower = problem.types.intern_generic(1, &body);
    let upper = problem.types.intern_callable(vec![t], m);
    let moved = atom_from_ids(&mut problem, lower, upper);
    let later = atom_from_ids(&mut problem, dog, t);
    for outcome in check_canonical(
        declarations,
        &Input::fixture(&problem),
        &[moved, later],
        true,
    ) {
        assert_eq!(
            model_text(&outcome),
            "satisfiable\nmodel:\n  ?T = Dog\n  ?M = forall T0. (Inv[T0 & Dog]) -> Inv[T0]\n"
        );
    }

    let identity = generic_identity(&mut problem);
    let inv_owned = problem.types.intern_class(inv, vec![identity]);
    let callback = problem.types.intern_callable(vec![inv_owned], object);
    let never = problem.types.intern_class(ClassId::NEVER, Vec::new());
    let required = problem.types.intern_callable(vec![never], object);
    let upper = problem.types.intern_callable(vec![callback], required);
    let moved = atom_from_ids(&mut problem, identity, upper);
    // The complete generic argument owns its binder. It does not exclude
    // an independent negative result for its outer Inv factor.
    check_canonical(declarations, &Input::fixture(&problem), &[moved], true);
}

#[test]
fn class_models_preserve_complete_arguments_and_retained_binders() {
    let declarations = "class A; class Inv[T]; metavar ?T;";
    let mut problem = RawProblem::new(declarations);
    let inv = lookup_class(&problem.declarations, "Inv");
    let a = problem
        .types
        .intern_class(lookup_class(&problem.declarations, "A"), Vec::new());
    let selected = lookup_metavar(&problem.declarations, "T");
    let selected = problem.types.types().metavar_type(selected);
    let inner = problem.types.intern_bound(BoundRef::new(0, 0));
    let outer = problem.types.intern_bound(BoundRef::new(1, 0));
    let body = Callable {
        params: vec![inner],
        ret: outer,
    };
    let generic_argument = problem.types.intern_generic(1, &body);
    let instance = problem.types.intern_class(inv, vec![generic_argument]);
    let body = Callable {
        params: vec![a],
        ret: instance,
    };
    let generic = problem.types.intern_generic(1, &body);
    let formula = atom_from_ids(&mut problem, generic, selected);
    for outcome in check_canonical(declarations, &Input::fixture(&problem), &[formula], true) {
        assert_eq!(
            model_text(&outcome),
            "satisfiable\nmodel:\n  ?T = forall T0. (A) -> Inv[forall T1. (T1) -> T0]\n"
        );
    }
}

#[test]
fn class_model_normalization_preserves_later_argument_bindings() {
    check_source_model(
        "class A;
         class Parent[T];
         class Child[First, Second] extends Parent[tuple[First, Second]];
         metavar ?T;
         assert forall X. () -> (Child[A, X] | Parent[tuple[A, X]]) <: ?T;",
        "satisfiable\nmodel:\n  ?T = forall T0. () -> Parent[tuple[A, T0]]\n",
    );
}

#[test]
fn generic_class_fixtures_have_checked_source_models() {
    for (source, expected) in [
        (
            include_str!("../../../tests/data/solve/sat/class_application_order.input"),
            include_str!("../../../tests/data/solve/sat/class_application_order.stdout"),
        ),
        (
            include_str!("../../../tests/data/solve/sat/generic_class_model.input"),
            include_str!("../../../tests/data/solve/sat/generic_class_model.stdout"),
        ),
        (
            include_str!("../../../tests/data/solve/sat/generic_class_transfers.input"),
            include_str!("../../../tests/data/solve/sat/generic_class_transfers.stdout"),
        ),
        (
            include_str!("../../../tests/data/solve/sat/generic_class_hierarchy.input"),
            include_str!("../../../tests/data/solve/sat/generic_class_hierarchy.stdout"),
        ),
        (
            include_str!("../../../tests/data/solve/sat/generic_class_shared.input"),
            include_str!("../../../tests/data/solve/sat/generic_class_shared.stdout"),
        ),
    ] {
        check_source_model(source, expected);
    }
}

#[test]
fn generic_class_source_laws_preserve_variance_and_overlap() {
    let declarations = "class Animal; class Dog extends Animal; class Cat; class Co[+T]; class Con[-T]; class Inv[T]; class P[+T]; class Left extends P[Dog]; class Right extends P[Cat];";
    for (relation, expected) in [
        ("Co[Dog] <: Co[Animal]", true),
        ("Co[Animal] <: Co[Dog]", false),
        ("Con[Animal] <: Con[Dog]", true),
        ("Con[Dog] <: Con[Animal]", false),
        ("Inv[Dog] <: Inv[Animal]", false),
        ("Inv[Animal] <: Inv[Dog]", false),
        ("Inv[forall X. (X) -> X] <: Inv[forall Y. (Y) -> Y]", true),
        ("Inv[Dog] & Inv[Cat] <: never", false),
        ("Left & Right <: never", false),
        ("Left & P[Cat] <: never", false),
        ("Inv[never] <: never", false),
        ("Inv[Dog] & tuple[Dog] <: never", true),
        ("Inv[Dog] & ((Dog) -> Dog) <: never", true),
        ("Inv[Dog | Cat] <: Inv[Dog] | Inv[Cat]", false),
        ("Inv[Dog] | Inv[Cat] <: Inv[Dog | Cat]", false),
        ("Co[Dog] | Co[Cat] <: Co[Dog | Cat]", true),
        ("Co[Dog | Cat] <: Co[Dog] | Co[Cat]", false),
    ] {
        check_source(&format!("{declarations} assert {relation};"), expected);
    }
}

#[test]
fn class_argument_models_use_rewritten_callable_restrictions() {
    let declarations = "class Animal; class Dog extends Animal; class Box[T]; metavar ?F;";
    for (generic, expected) in [
        (
            "forall X <: Animal. (Box[X]) -> Box[X]",
            "forall T0. (Box[T0 & Animal]) -> Box[T0 & Animal]",
        ),
        (
            "forall X in {Dog, Animal}. (Box[X]) -> Box[X]",
            "((Box[Animal]) -> Box[Animal]) & ((Box[Dog]) -> Box[Dog])",
        ),
        (
            "forall X <: never. (Box[X]) -> Box[X]",
            "(Box[never]) -> Box[never]",
        ),
    ] {
        check_source_model(
            &format!("{declarations} assert {generic} <: ?F;"),
            &format!("satisfiable\nmodel:\n  ?F = {expected}\n"),
        );
    }
}

#[test]
fn class_transfers_accept_subsets_in_the_same_environment() {
    let source = include_str!("../../../tests/data/solve/sat/generic_class_shared.input");
    let file = validate_ok(source);
    let units = work_units(&file);
    // Removing a demand keeps the original declarations and atom identities.
    // Both tuple slots still share one result.
    for omitted in [None, Some(0), Some(2)] {
        let selected = units
            .iter()
            .enumerate()
            .filter(|(index, _)| Some(*index) != omitted)
            .map(|(_, unit)| *unit)
            .collect::<Vec<_>>();
        let formulas = selected.iter().map(|unit| unit.formula).collect::<Vec<_>>();
        check_units(
            &selected,
            &Input::new(&file),
            ModelInput::Canonical {
                declarations: source,
                input: &Input::new(&file),
                formulas: &formulas,
            },
            true,
            source,
        );
    }
}

#[test]
fn class_models_close_nested_arguments_in_structural_order() {
    let declarations = "class Zed[P, Q, R]; class zebra; class Alpha[T]; class apple; metavar ?Arg; metavar ?Model; metavar ?Order;";
    let mut problem = RawProblem::new(declarations);
    let zebra = problem
        .types
        .intern_class(lookup_class(&problem.declarations, "zebra"), Vec::new());
    let apple = problem
        .types
        .intern_class(lookup_class(&problem.declarations, "apple"), Vec::new());
    let zed = lookup_class(&problem.declarations, "Zed");
    let alpha = lookup_class(&problem.declarations, "Alpha");
    let (arg, model, order) = (
        lookup_metavar(&problem.declarations, "Arg"),
        lookup_metavar(&problem.declarations, "Model"),
        lookup_metavar(&problem.declarations, "Order"),
    );
    let arg = problem.types.types().metavar_type(arg);
    let model = problem.types.types().metavar_type(model);
    let order = problem.types.types().metavar_type(order);
    let never = problem.types.intern_class(ClassId::NEVER, Vec::new());
    let nested = problem.types.intern_class(alpha, vec![arg]);
    let tuple = problem.types.intern_tuple(vec![arg, never]);
    let intersection = problem.types.intern_intersection(vec![apple, zebra]);
    let callable = problem.types.intern_callable(vec![apple], zebra);
    let generic = generic_identity(&mut problem);
    let compound = problem
        .types
        .intern_union(vec![generic, callable, intersection]);
    let structured = problem
        .types
        .intern_class(zed, vec![nested, tuple, compound]);
    let first = problem.types.intern_class(zed, vec![zebra, zebra, apple]);
    let second = problem.types.intern_class(zed, vec![zebra, apple, zebra]);
    let alpha_zebra = problem.types.intern_class(alpha, vec![zebra]);
    let empty_tuple = problem.types.intern_tuple(Vec::new());
    let ordered = problem
        .types
        .intern_union(vec![empty_tuple, alpha_zebra, second, first, apple]);
    let formulas = [
        atom_from_ids(&mut problem, structured, model),
        atom_from_ids(&mut problem, ordered, order),
        atom_from_ids(&mut problem, zebra, arg),
        atom_from_ids(&mut problem, apple, arg),
    ];
    for outcome in check_canonical(declarations, &Input::fixture(&problem), &formulas, true) {
        assert_eq!(
            model_text(&outcome),
            "satisfiable\nmodel:\n  ?Arg = zebra | apple\n  ?Model = Zed[Alpha[zebra | apple], tuple[zebra | apple, never], zebra & apple | ((apple) -> zebra) | (forall T0. (T0) -> T0)]\n  ?Order = Zed[zebra, zebra, apple] | Zed[zebra, apple, zebra] | Alpha[zebra] | apple | tuple[]\n"
        );
    }
}

#[test]
fn class_model_normalization_keeps_invariant_constructor_boundaries() {
    let declarations = "class zebra; class apple; class Inv[T]; metavar ?Arg; metavar ?Model;";
    let mut problem = RawProblem::new(declarations);
    let zebra = problem
        .types
        .intern_class(lookup_class(&problem.declarations, "zebra"), Vec::new());
    let apple = problem
        .types
        .intern_class(lookup_class(&problem.declarations, "apple"), Vec::new());
    let inv = lookup_class(&problem.declarations, "Inv");
    let (arg, model) = (
        lookup_metavar(&problem.declarations, "Arg"),
        lookup_metavar(&problem.declarations, "Model"),
    );
    let arg = problem.types.types().metavar_type(arg);
    let model = problem.types.types().metavar_type(model);
    let never = problem.types.intern_class(ClassId::NEVER, Vec::new());
    let inv_never = problem.types.intern_class(inv, vec![never]);
    let inv_zebra = problem.types.intern_class(inv, vec![zebra]);
    let inv_apple = problem.types.intern_class(inv, vec![apple]);
    let overlap = problem
        .types
        .intern_intersection(vec![inv_apple, inv_zebra]);
    let argument_union = problem.types.intern_union(vec![zebra, apple]);
    let inside_union = problem.types.intern_class(inv, vec![argument_union]);
    let outside_union = problem.types.intern_union(vec![inv_zebra, inv_apple]);
    let live = problem.types.intern_class(inv, vec![arg]);
    let equal_intersection = problem.types.intern_intersection(vec![live, inv_zebra]);
    let equal_union = problem.types.intern_union(vec![live, inv_zebra]);
    let bound = problem.types.intern_bound(BoundRef::new(0, 0));
    let inv_bound = problem.types.intern_class(inv, vec![bound]);
    let retained_intersection = problem
        .types
        .intern_intersection(vec![inv_bound, inv_zebra]);
    let body = Callable {
        params: Vec::new(),
        ret: retained_intersection,
    };
    let retained = problem.types.intern_generic(1, &body);
    for (value, expected) in [
        (inv_never, "Inv[never]"),
        (overlap, "Inv[zebra] & Inv[apple]"),
        (inside_union, "Inv[zebra | apple]"),
        (outside_union, "Inv[zebra] | Inv[apple]"),
        (equal_intersection, "Inv[zebra]"),
        (equal_union, "Inv[zebra]"),
        (retained, "forall T0. () -> Inv[T0] & Inv[zebra]"),
    ] {
        let formulas = [
            atom_from_ids(&mut problem, value, model),
            atom_from_ids(&mut problem, zebra, arg),
        ];
        for outcome in check_canonical(declarations, &Input::fixture(&problem), &formulas, true) {
            assert_eq!(
                model_text(&outcome),
                format!("satisfiable\nmodel:\n  ?Arg = zebra\n  ?Model = {expected}\n")
            );
        }
    }
}

#[test]
fn plain_subclass_of_generic_declaration_keeps_its_plain_ancestors() {
    check_source(
        include_str!("../../../tests/data/validate/valid/generic_classes.input"),
        true,
    );
}
