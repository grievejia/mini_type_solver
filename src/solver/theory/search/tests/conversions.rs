//! Scope conversions checked through complete subtype requests.
use super::super::super::TheoryResult;
use super::solve;
use crate::frontend::problem::{BoundRef, Callable};
use crate::frontend::test_support::{RawProblem, generic_identity, lookup_class};
use crate::solver::build_model;
use crate::solver::input::Input;

#[test]
fn contravariant_generic_conversion_keeps_the_source_below_the_selection() {
    let mut problem = RawProblem::new("class A;");
    let a = lookup_class(&problem.declarations, "A");
    let a_type = problem.types.intern_class(a, Vec::new());
    let parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let lower_body = Callable {
        params: vec![parameter],
        ret: a_type,
    };
    let lower = problem.types.intern_generic(1, &lower_body);
    let nested = generic_identity(&mut problem);
    let nested_parameter = problem.types.intern_callable(vec![nested], a_type);
    let upper = problem
        .types
        .intern_callable(vec![nested_parameter], a_type);
    let atom = problem.atoms.intern_atom(lower, upper);
    assert!(matches!(
        solve(&Input::fixture(&problem), atom),
        TheoryResult::Satisfiable(_)
    ));
}

#[test]
fn covariant_rigid_escape_widens_to_object() {
    let mut problem = RawProblem::new("");
    let selected = problem.declare_metavar("T");
    let lower_parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let nested = problem.types.intern_tuple(vec![lower_parameter]);
    let lower_return = problem.types.intern_tuple(vec![lower_parameter, nested]);
    let lower_body = Callable {
        params: vec![lower_parameter],
        ret: lower_return,
    };
    let lower = problem.types.intern_generic(1, &lower_body);

    let upper_parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let upper_return = problem.types.intern_tuple(vec![
        upper_parameter,
        problem.types.types().metavar_type(selected),
    ]);
    let upper_body = Callable {
        params: vec![upper_parameter],
        ret: upper_return,
    };
    let upper = problem.types.intern_generic(1, &upper_body);
    let atom = problem.atoms.intern_atom(lower, upper);
    let TheoryResult::Satisfiable(solution) = solve(&Input::fixture(&problem), atom) else {
        panic!("covariant rigid escape must be satisfiable");
    };
    let model = build_model(&problem.declarations, solution);
    assert_eq!(model.entries()[0].value().render(), "tuple[object]");
}

#[test]
fn contravariant_rigid_escape_narrows_to_never() {
    let mut problem = RawProblem::new("class A;");
    let a = lookup_class(&problem.declarations, "A");
    let selected = problem.declare_metavar("T");
    let a_type = problem.types.intern_class(a, Vec::new());
    let lower_parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let escaped = problem.types.intern_callable(vec![lower_parameter], a_type);
    let lower_body = Callable {
        params: vec![lower_parameter],
        ret: escaped,
    };
    let lower = problem.types.intern_generic(1, &lower_body);

    let upper_parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let upper_body = Callable {
        params: vec![upper_parameter],
        ret: problem.types.types().metavar_type(selected),
    };
    let upper = problem.types.intern_generic(1, &upper_body);
    let atom = problem.atoms.intern_atom(lower, upper);
    let TheoryResult::Satisfiable(solution) = solve(&Input::fixture(&problem), atom) else {
        panic!("contravariant rigid escape must be satisfiable");
    };
    let model = build_model(&problem.declarations, solution);
    assert_eq!(model.entries()[0].value().render(), "(never) -> A");
}
