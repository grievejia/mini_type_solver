//! Tests for Boolean formulas, engine verdicts, and public model rendering.

use crate::frontend::test_support::{RawProblem, lookup_class};
use crate::solver::input::Input;

use super::super::test_support::{ModelInput, model_holds, validate_ok};
use super::super::theory::TheoryResult;
use super::super::{AtomFormula, build_model, solve_conjunction, work_units};
use super::{Engine, check_atom_conjunction, check_source, check_source_model, run_engine};

#[test]
fn compound_type_laws_have_expected_verdicts() {
    for (source, expected) in [
        // An upper union cannot split into two required upper bounds.
        (
            "class a;\nclass b;\nmetavar ?T;\nassert a <: ?T;\nassert b <: ?T;\nassert ?T <: a | b;",
            true,
        ),
        // A lower intersection cannot split into two required lower bounds.
        (
            "class a;\nclass b;\nmetavar ?T;\nassert a & b <: ?T;\nassert ?T <: a & b;",
            true,
        ),
        // Intersection distributes over union in both directions.
        (
            "class a;\nclass b;\nclass c;\nassert (a | b) & c <: (a & c) | (b & c);\nassert (a & c) | (b & c) <: (a | b) & c;",
            true,
        ),
        // Unrelated classes can overlap in the open world.
        ("class a;\nclass b;\nassert a & b <: never;", false),
        // Upper intersection decomposition must reject this open-world case.
        ("class a;\nclass b;\nassert object <: a & b;", false),
        // The first update adds `a` to T. Its upper bound forces a retry with U.
        (
            "class a;\nclass b;\nmetavar ?T;\nmetavar ?U;\nassert a <: ?T | ?U;\nassert ?T <: b;",
            true,
        ),
        // Both alternatives violate an upper bound, so search must exhaust them.
        (
            "class a;\nclass b;\nmetavar ?T;\nmetavar ?U;\nassert a <: ?T | ?U;\nassert ?T <: b;\nassert ?U <: b;",
            false,
        ),
        // Assigning T makes the lower intersection fail without another update.
        (
            "class a;\nclass b;\nmetavar ?T;\nassert ?T & a <: b;\nassert a <: ?T;",
            false,
        ),
    ] {
        check_atom_conjunction(source, expected);
    }
}

#[test]
fn nested_outer_formulas_have_expected_verdicts() {
    for (source, expected) in [
        (
            "class a;\nclass b;\nmetavar ?T;\nmetavar ?U;\nassert ((a <: ?T | ?U) and (?T <: b) and (?U <: b)) or ((a <: ?T | ?U) and (?T <: b));",
            true,
        ),
        (
            "class a;\nclass b;\nassert (object <: a | b) or (a & b <: never);",
            false,
        ),
    ] {
        check_source(source, expected);
    }
}

#[test]
fn engines_return_expected_verdicts_with_valid_models_and_minimal_cores() {
    check_source(
        "class animal;\nclass dog extends animal;\nclass cat extends animal;\nmetavar ?T;\nassert dog <: ?T;\nassert ?T <: cat;",
        false,
    );
    check_source(
        "class animal;\nclass dog extends animal;\nmetavar ?T;\nassert dog <: ?T;",
        true,
    );
    // Branching satisfiable input: engines may choose different
    // branches, so only the verdict and each model are pinned.
    check_source(
        "class animal;\nclass dog extends animal;\nclass cat extends animal;\nmetavar ?T;\nassert (dog <: ?T) or (cat <: ?T);",
        true,
    );
    check_source(
        "class a;\nclass b;\nmetavar ?T;\nmetavar ?U;\nassert (a | b) <: (?T | ?U);",
        true,
    );
    check_source("class a;\nclass b;\nassert object <: a | b;", false);
    check_source("metavar ?T;\nmetavar ?U;\nassert object <: ?T | ?U;", true);
    check_source(
        "class a;\nclass b;\nassert a & b <: a;\nassert a & b <: b;",
        true,
    );
}

#[test]
fn dnf_model_arms_follow_declaration_order() {
    let source = "class zebra;\nclass apple;\nmetavar ?T;\nassert zebra <: ?T;\nassert apple <: ?T;\nassert ?T <: zebra | apple;";
    let file = validate_ok(source);
    let units = work_units(&file);
    for engine in [Engine::Dnf, Engine::Direct, Engine::Varisat] {
        assert_eq!(
            run_engine(engine, &units, &Input::new(&file)).render(source),
            "satisfiable\nmodel:\n  ?T = zebra | apple\n"
        );
    }
}

#[test]
fn public_model_converts_independent_dnf_assignments() {
    let source = "class a;\nclass b;\nmetavar ?T;\nmetavar ?U;\nmetavar ?V;\nassert a <: ?T | ?U;\nassert b <: ?V;";
    let file = validate_ok(source);
    let units = work_units(&file);
    for engine in [Engine::Dnf, Engine::Direct, Engine::Varisat] {
        assert_eq!(
            run_engine(engine, &units, &Input::new(&file)).render(source),
            "satisfiable\nmodel:\n  ?T = a\n  ?U = never\n  ?V = b\n"
        );
    }
}

#[test]
fn dnf_model_renders_intersection_factors() {
    let source = "class zebra;\nclass apple;\nmetavar ?T;\nassert zebra & apple <: ?T;\nassert ?T <: zebra & apple;";
    let file = validate_ok(source);
    let units = work_units(&file);
    for engine in [Engine::Dnf, Engine::Direct, Engine::Varisat] {
        assert_eq!(
            run_engine(engine, &units, &Input::new(&file)).render(source),
            "satisfiable\nmodel:\n  ?T = zebra & apple\n"
        );
    }
}

#[test]
fn canonicalization_can_make_a_metavariable_unconstrained() {
    let source = "class a;\nmetavar ?T;\nassert a <: object | ?T;";
    let file = validate_ok(source);
    let units = work_units(&file);
    for engine in [Engine::Dnf, Engine::Direct, Engine::Varisat] {
        assert_eq!(
            run_engine(engine, &units, &Input::new(&file)).render(source),
            "satisfiable\nmodel:\n  ?T = unconstrained\n"
        );
    }
}

#[test]
fn public_model_renders_structural_tuple_values() {
    let declarations = "class a; class b;";
    let mut problem = RawProblem::new(declarations);
    let mut metavars = Vec::new();
    for name in ["Empty", "Structured", "OuterUnion", "OuterIntersection"] {
        let id = problem.declare_metavar(name);
        metavars.push(id);
    }
    let a = lookup_class(&problem.declarations, "a");
    let b = lookup_class(&problem.declarations, "b");
    let a_type = problem.types.intern_class(a, Vec::new());
    let b_type = problem.types.intern_class(b, Vec::new());
    let tuple_a = problem.types.intern_tuple(vec![a_type]);
    let tuple_b = problem.types.intern_tuple(vec![b_type]);
    let element_union = problem.types.intern_union(vec![a_type, b_type]);
    let element_intersection = problem.types.intern_intersection(vec![a_type, b_type]);
    let empty_tuple = problem.types.intern_tuple(Vec::new());
    let structured_tuple =
        problem
            .types
            .intern_tuple(vec![tuple_a, element_union, element_intersection]);
    let outer_intersection = problem.types.intern_intersection(vec![tuple_a, tuple_b]);
    let atoms = [
        problem
            .atoms
            .intern_atom(empty_tuple, problem.types.types().metavar_type(metavars[0])),
        problem.atoms.intern_atom(
            structured_tuple,
            problem.types.types().metavar_type(metavars[1]),
        ),
        problem
            .atoms
            .intern_atom(tuple_a, problem.types.types().metavar_type(metavars[2])),
        problem
            .atoms
            .intern_atom(tuple_b, problem.types.types().metavar_type(metavars[2])),
        problem.atoms.intern_atom(
            outer_intersection,
            problem.types.types().metavar_type(metavars[3]),
        ),
    ];
    let TheoryResult::Satisfiable(solution) = solve_conjunction(&atoms, &Input::fixture(&problem))
    else {
        panic!("expected tuple model fixture to satisfy");
    };
    let model = build_model(&problem.declarations, solution);

    assert_eq!(
        model.render(),
        "satisfiable\nmodel:\n  ?Empty = tuple[]\n  ?Structured = tuple[tuple[a], a | b, a & b]\n  ?OuterUnion = tuple[a] | tuple[b]\n  ?OuterIntersection = tuple[a] & tuple[b]\n"
    );
    let formulas = atoms
        .iter()
        .map(|atom| AtomFormula::Atom(*atom))
        .collect::<Vec<_>>();
    let formula_refs = formulas.iter().collect::<Vec<_>>();
    assert!(model_holds(
        ModelInput::Canonical {
            declarations,
            input: &Input::fixture(&problem),
            formulas: &formula_refs,
        },
        &model,
    ));
}

#[test]
fn documented_chain_prints_its_checked_witness() {
    check_source_model(
        "class Animal; class Dog extends Animal; metavar ?T; metavar ?U;
        assert Dog <: ?T; assert ?T <: ?U; assert ?U <: Animal;",
        "satisfiable\nmodel:\n  ?T = Dog\n  ?U = Dog\n",
    );
}
