//! Tests for tuple and callable subtyping, constructor shape, and live references.

use crate::solver::test_support::atom_from_ids;

use super::model_text;

use crate::frontend::problem::ClassId;
use crate::frontend::test_support::{RawProblem, lookup_class};
use crate::solver::input::Input;

use super::{callable_type, check_canonical, check_source, check_source_model};

#[test]
fn callable_subtyping_reverses_parameters_and_preserves_returns() {
    let declarations = "class a; class b extends a;";
    let mut problem = RawProblem::new(declarations);
    let a = lookup_class(&problem.declarations, "a");
    let b = lookup_class(&problem.declarations, "b");
    let a_type = problem.types.intern_class(a, Vec::new());
    let b_type = problem.types.intern_class(b, Vec::new());
    let never = problem.types.intern_class(ClassId::NEVER, Vec::new());
    let object = problem.types.intern_class(ClassId::OBJECT, Vec::new());
    let a_to_b = callable_type(&mut problem, &[a_type], b_type);
    let b_to_a = callable_type(&mut problem, &[b_type], a_type);
    let zero_b = callable_type(&mut problem, &[], b_type);
    let zero_a = callable_type(&mut problem, &[], a_type);
    let multiple_lower = callable_type(&mut problem, &[a_type, a_type], b_type);
    let multiple_upper = callable_type(&mut problem, &[b_type, b_type], a_type);

    for (lower, upper, expected) in [
        (a_to_b, b_to_a, true),
        (b_to_a, a_to_b, false),
        (zero_b, zero_a, true),
        (multiple_lower, multiple_upper, true),
        (zero_a, a_to_b, false),
        (a_to_b, zero_a, false),
        (never, a_to_b, true),
        (a_to_b, object, true),
        (a_to_b, never, false),
        (object, a_to_b, false),
    ] {
        let formulas = [atom_from_ids(&mut problem, lower, upper)];
        check_canonical(declarations, &Input::fixture(&problem), &formulas, expected);
    }
}

#[test]
fn callable_parameter_subsumption_keeps_the_contravariant_supertype() {
    let declarations = "class a; class b extends a; class c;";
    let mut problem = RawProblem::new(declarations);
    let t_metavar = problem.declare_metavar("T");
    let class_a = lookup_class(&problem.declarations, "a");
    let class_b = lookup_class(&problem.declarations, "b");
    let class_c = lookup_class(&problem.declarations, "c");
    let a_type = problem.types.intern_class(class_a, Vec::new());
    let b_type = problem.types.intern_class(class_b, Vec::new());
    let c_type = problem.types.intern_class(class_c, Vec::new());
    let t_type = problem.types.types().metavar_type(t_metavar);
    let a_to_c = callable_type(&mut problem, &[a_type], c_type);
    let b_to_c = callable_type(&mut problem, &[b_type], c_type);
    let formulas = [
        atom_from_ids(&mut problem, a_to_c, t_type),
        atom_from_ids(&mut problem, b_to_c, t_type),
    ];
    let outcomes = check_canonical(declarations, &Input::fixture(&problem), &formulas, true);

    for outcome in outcomes {
        assert_eq!(
            model_text(&outcome),
            "satisfiable\nmodel:\n  ?T = (b) -> c\n"
        );
    }
}

#[test]
fn callable_disjointness_uses_outer_shape_and_arity() {
    let declarations = "class a; class b;";
    let mut problem = RawProblem::new(declarations);
    let a = lookup_class(&problem.declarations, "a");
    let b = lookup_class(&problem.declarations, "b");
    let a_type = problem.types.intern_class(a, Vec::new());
    let b_type = problem.types.intern_class(b, Vec::new());
    let never = problem.types.intern_class(ClassId::NEVER, Vec::new());
    let tuple_a = problem.types.intern_tuple(vec![a_type]);
    let zero = callable_type(&mut problem, &[], a_type);
    let one_a = callable_type(&mut problem, &[a_type], a_type);
    let one_b = callable_type(&mut problem, &[b_type], b_type);
    let callable_and_class = problem.types.intern_intersection(vec![one_a, a_type]);
    let callable_and_tuple = problem.types.intern_intersection(vec![one_a, tuple_a]);
    let different_arities = problem.types.intern_intersection(vec![zero, one_a]);
    let same_arity = problem.types.intern_intersection(vec![one_a, one_b]);

    for (lower, expected) in [
        (callable_and_class, true),
        (callable_and_tuple, true),
        (different_arities, true),
        (same_arity, false),
    ] {
        let formulas = [atom_from_ids(&mut problem, lower, never)];
        check_canonical(declarations, &Input::fixture(&problem), &formulas, expected);
    }
}

#[test]
fn callable_constructor_does_not_distribute_over_boolean_types() {
    let declarations = "class a; class b;";
    let mut problem = RawProblem::new(declarations);
    let a = lookup_class(&problem.declarations, "a");
    let b = lookup_class(&problem.declarations, "b");
    let a_type = problem.types.intern_class(a, Vec::new());
    let b_type = problem.types.intern_class(b, Vec::new());
    let object = problem.types.intern_class(ClassId::OBJECT, Vec::new());
    let union = problem.types.intern_union(vec![a_type, b_type]);
    let intersection = problem.types.intern_intersection(vec![a_type, b_type]);
    let return_a = callable_type(&mut problem, &[], a_type);
    let return_b = callable_type(&mut problem, &[], b_type);
    let return_union = callable_type(&mut problem, &[], union);
    let return_intersection = callable_type(&mut problem, &[], intersection);
    let outer_union = problem.types.intern_union(vec![return_a, return_b]);
    let outer_intersection = problem.types.intern_intersection(vec![return_a, return_b]);
    let param_a = callable_type(&mut problem, &[a_type], object);
    let param_b = callable_type(&mut problem, &[b_type], object);
    let param_union = callable_type(&mut problem, &[union], object);
    let param_intersection = callable_type(&mut problem, &[intersection], object);
    let param_outer_union = problem.types.intern_union(vec![param_a, param_b]);
    let param_outer_intersection = problem.types.intern_intersection(vec![param_a, param_b]);

    for (lower, upper, expected) in [
        (outer_union, return_union, true),
        (return_union, outer_union, false),
        (return_intersection, outer_intersection, true),
        (outer_intersection, return_intersection, false),
        (param_union, param_outer_intersection, true),
        (param_outer_intersection, param_union, false),
        (param_outer_union, param_intersection, true),
        (param_intersection, param_outer_union, false),
    ] {
        let formulas = [atom_from_ids(&mut problem, lower, upper)];
        check_canonical(declarations, &Input::fixture(&problem), &formulas, expected);
    }
}

#[test]
fn callable_models_use_structural_order_and_precedence() {
    let declarations = "class a; class b; class c;";
    let mut problem = RawProblem::new(declarations);
    let mut metavars = Vec::new();
    for name in [
        "Zero",
        "Multiple",
        "NestedParameter",
        "NestedReturn",
        "Standalone",
        "OrderedUnion",
        "Intersection",
    ] {
        let id = problem.declare_metavar(name);
        metavars.push(id);
    }
    let a = lookup_class(&problem.declarations, "a");
    let b = lookup_class(&problem.declarations, "b");
    let c = lookup_class(&problem.declarations, "c");
    let a_type = problem.types.intern_class(a, Vec::new());
    let b_type = problem.types.intern_class(b, Vec::new());
    let c_type = problem.types.intern_class(c, Vec::new());
    let a_to_a = callable_type(&mut problem, &[a_type], a_type);
    let a_to_b = callable_type(&mut problem, &[a_type], b_type);
    let b_to_a = callable_type(&mut problem, &[b_type], a_type);
    let b_to_c = callable_type(&mut problem, &[b_type], c_type);
    let zero = callable_type(&mut problem, &[], c_type);
    let multiple = callable_type(&mut problem, &[a_type, b_type], c_type);
    let nested_parameter = callable_type(&mut problem, &[a_to_b], c_type);
    let nested_return = callable_type(&mut problem, &[a_type], b_to_c);
    let empty_tuple = problem.types.intern_tuple(Vec::new());
    let callable_intersection = problem.types.intern_intersection(vec![a_to_b, b_to_a]);
    let metavar_types = metavars
        .iter()
        .map(|metavar| problem.types.types().metavar_type(*metavar))
        .collect::<Vec<_>>();
    let formulas = [
        atom_from_ids(&mut problem, zero, metavar_types[0]),
        atom_from_ids(&mut problem, multiple, metavar_types[1]),
        atom_from_ids(&mut problem, nested_parameter, metavar_types[2]),
        atom_from_ids(&mut problem, nested_return, metavar_types[3]),
        atom_from_ids(&mut problem, a_to_b, metavar_types[4]),
        atom_from_ids(&mut problem, c_type, metavar_types[5]),
        atom_from_ids(&mut problem, empty_tuple, metavar_types[5]),
        atom_from_ids(&mut problem, zero, metavar_types[5]),
        atom_from_ids(&mut problem, a_to_a, metavar_types[5]),
        atom_from_ids(&mut problem, a_to_b, metavar_types[5]),
        atom_from_ids(&mut problem, multiple, metavar_types[5]),
        atom_from_ids(&mut problem, callable_intersection, metavar_types[6]),
    ];
    let outcomes = check_canonical(declarations, &Input::fixture(&problem), &formulas, true);

    for outcome in outcomes {
        assert_eq!(
            model_text(&outcome),
            "satisfiable\nmodel:\n  ?Zero = () -> c\n  ?Multiple = (a, b) -> c\n  ?NestedParameter = ((a) -> b) -> c\n  ?NestedReturn = (a) -> (b) -> c\n  ?Standalone = (a) -> b\n  ?OrderedUnion = c | tuple[] | (() -> c) | ((a) -> a) | ((a) -> b) | ((a, b) -> c)\n  ?Intersection = ((a) -> b) & ((b) -> a)\n"
        );
    }
}

#[test]
fn callable_parameter_reference_tracks_later_assignment_growth() {
    let declarations = "class A; class B extends C; class C;";
    let mut problem = RawProblem::new(declarations);
    let u_metavar = problem.declare_metavar("U");
    let t_metavar = problem.declare_metavar("T");
    let class_a = lookup_class(&problem.declarations, "A");
    let class_b = lookup_class(&problem.declarations, "B");
    let class_c = lookup_class(&problem.declarations, "C");
    let a_type = problem.types.intern_class(class_a, Vec::new());
    let b_type = problem.types.intern_class(class_b, Vec::new());
    let c_type = problem.types.intern_class(class_c, Vec::new());
    let u_type = problem.types.types().metavar_type(u_metavar);
    let t_type = problem.types.types().metavar_type(t_metavar);
    let lower = callable_type(&mut problem, &[u_type], b_type);
    let upper = callable_type(&mut problem, &[a_type], c_type);
    let formulas = [
        atom_from_ids(&mut problem, lower, t_type),
        atom_from_ids(&mut problem, t_type, upper),
    ];
    let outcomes = check_canonical(declarations, &Input::fixture(&problem), &formulas, true);

    for outcome in outcomes {
        assert_eq!(
            model_text(&outcome),
            "satisfiable\nmodel:\n  ?U = A\n  ?T = (A) -> B\n"
        );
    }
}

#[test]
fn tuple_type_laws_have_expected_verdicts() {
    for (source, expected) in [
        (
            "assert tuple[] <: tuple[];\nassert tuple[tuple[]] <: tuple[tuple[]];",
            true,
        ),
        (
            "class animal;\nclass dog extends animal;\nassert tuple[dog] <: tuple[animal];",
            true,
        ),
        (
            "class animal;\nclass dog extends animal;\nassert tuple[animal] <: tuple[dog];",
            false,
        ),
        ("assert tuple[] <: tuple[object];", false),
        ("assert tuple[object] <: tuple[];", false),
        ("class a;\nassert tuple[a] <: a;", false),
        ("class a;\nassert a <: tuple[a];", false),
        ("class a;\nassert tuple[a] & a <: never;", true),
        ("assert tuple[never] <: never;", false),
        ("assert never <: tuple[never];", true),
        (
            "class a;\nclass b;\nassert tuple[a] | tuple[b] <: tuple[a | b];",
            true,
        ),
        (
            "class a;\nclass b;\nassert tuple[a | b] <: tuple[a] | tuple[b];",
            false,
        ),
        (
            "class a;\nclass b;\nassert tuple[a & b] <: tuple[a] & tuple[b];",
            true,
        ),
        (
            "class a;\nclass b;\nassert tuple[a] & tuple[b] <: tuple[a & b];",
            false,
        ),
    ] {
        check_source(source, expected);
    }
}

#[test]
fn callable_type_laws_have_expected_verdicts() {
    for (source, expected) in [
        (
            "class Animal;\nclass Dog extends Animal;\nassert (Animal) -> Dog <: (Dog) -> Animal;",
            true,
        ),
        (
            "class Animal;\nclass Dog extends Animal;\nassert (Dog) -> Animal <: (Animal) -> Dog;",
            false,
        ),
        (
            "class Animal;\nclass Dog extends Animal;\nassert () -> Dog <: () -> Animal;",
            true,
        ),
        (
            "class Animal;\nclass Dog extends Animal;\nassert () -> Animal <: () -> Dog;",
            false,
        ),
        (
            "class Animal;\nclass Dog extends Animal;\nassert (Animal, Dog) -> Dog <: (Dog, Dog) -> Animal;",
            true,
        ),
        (
            "class Animal;\nclass Dog extends Animal;\nassert (Dog, Dog) -> Animal <: (Animal, Dog) -> Dog;",
            false,
        ),
        ("class A;\nassert () -> A <: (A) -> A;", false),
        (
            "class Animal;\nclass Dog extends Animal;\nassert tuple[(Animal) -> Dog] <: tuple[(Dog) -> Animal];",
            true,
        ),
        (
            "class Animal;\nclass Dog extends Animal;\nassert tuple[(Dog) -> Animal] <: tuple[(Animal) -> Dog];",
            false,
        ),
        (
            "class Animal;\nclass Dog extends Animal;\nassert (tuple[Animal]) -> tuple[Dog] <: (tuple[Dog]) -> tuple[Animal];",
            true,
        ),
        (
            "class Animal;\nclass Dog extends Animal;\nassert (tuple[Dog]) -> tuple[Animal] <: (tuple[Animal]) -> tuple[Dog];",
            false,
        ),
        (
            "class Animal;\nclass Dog extends Animal;\nassert ((Dog) -> Animal) -> Dog <: ((Animal) -> Dog) -> Animal;",
            true,
        ),
        ("class A;\nclass B;\nassert (A) -> B <: A;", false),
        ("class A;\nclass B;\nassert A <: (A) -> B;", false),
        ("class A;\nclass B;\nassert (A) -> B <: tuple[A];", false),
        ("class A;\nclass B;\nassert tuple[A] <: (A) -> B;", false),
        ("class A;\nclass B;\nassert ((A) -> B) & A <: never;", true),
        (
            "class A;\nclass B;\nassert ((A) -> B) & tuple[A] <: never;",
            true,
        ),
        (
            "class A;\nclass B;\nassert ((A) -> B) & ((B) -> A) <: never;",
            false,
        ),
        (
            "class A;\nclass B;\nassert (() -> A) | (() -> B) <: () -> A | B;",
            true,
        ),
        (
            "class A;\nclass B;\nassert () -> A | B <: (() -> A) | (() -> B);",
            false,
        ),
        (
            "class A;\nclass B;\nassert (A | B) -> object <: ((A) -> object) & ((B) -> object);",
            true,
        ),
        (
            "class A;\nclass B;\nassert ((A) -> object) & ((B) -> object) <: (A | B) -> object;",
            false,
        ),
    ] {
        check_source(source, expected);
    }
}

#[test]
fn callable_source_models_close_nested_and_branch_state() {
    check_source_model(
        "class A;\nclass C;\nclass B extends C;\nmetavar ?U;\nmetavar ?T;\nassert (?U) -> B <: ?T;\nassert ?T <: (A) -> C;",
        "satisfiable\nmodel:\n  ?U = A\n  ?T = (A) -> B\n",
    );
    check_source_model(
        "class B;\nmetavar ?U;\nmetavar ?T;\nassert (?U) -> B <: ?T;",
        "satisfiable\nmodel:\n  ?U = never\n  ?T = (never) -> B\n",
    );
    check_source_model(
        "class B;\nmetavar ?T;\nassert (object <: object) or (object <: (?T) -> B);",
        "satisfiable\nmodel:\n  ?T = unconstrained\n",
    );
}

#[test]
fn callable_source_models_pin_parentheses_and_factor_order() {
    check_source_model(
        "class A;\nclass B;\nclass C;\nmetavar ?Union;\nmetavar ?Intersection;\nassert C <: ?Union;\nassert (A) -> B <: ?Union;\nassert ((A) -> B) & ((B) -> A) <: ?Intersection;",
        "satisfiable\nmodel:\n  ?Union = C | ((A) -> B)\n  ?Intersection = ((A) -> B) & ((B) -> A)\n",
    );
}

#[test]
fn tuple_source_models_render_closed_values_and_branch_state() {
    check_source_model(
        "metavar ?T;\nmetavar ?U;\nassert tuple[?U] <: ?T;",
        "satisfiable\nmodel:\n  ?T = tuple[never]\n  ?U = never\n",
    );
    check_source_model(
        "metavar ?T;\nassert (object <: object) or (object <: tuple[?T]);",
        "satisfiable\nmodel:\n  ?T = unconstrained\n",
    );
    check_source_model(
        "class B;\nclass C;\nmetavar ?U;\nmetavar ?T;\nassert B <: ?U;\nassert C <: ?U;\nassert tuple[?U, ?U] <: ?T;",
        "satisfiable\nmodel:\n  ?U = B | C\n  ?T = tuple[B | C, B | C]\n",
    );
}

#[test]
fn nested_tuple_conflict_has_a_minimal_source_core() {
    check_source(
        "class a;\nclass b;\nmetavar ?T;\nassert require_a: tuple[tuple[a]] <: ?T;\nassert require_b: ?T <: tuple[tuple[b]];",
        false,
    );
}
