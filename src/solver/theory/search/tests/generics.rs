//! Generic selection, normalization, and deferred instance tests.

use std::num::NonZeroU32;

use crate::frontend::problem::{BoundRef, Callable, ClassId};
use crate::frontend::test_support::{RawProblem, generic_identity, lookup_class};
use crate::solver::build_model;
use crate::solver::input::Input;

use super::super::super::TheoryResult;
use super::super::generics::normalize_generic;
use super::super::graph::{FactorNode, Graph};
use super::super::solve_conjunction;
use super::solve;

#[test]
fn sparse_live_parameters_match_a_renamed_dense_binder() {
    let problem = RawProblem::new("");
    let graph = Graph::new(&problem.declarations);
    let Some(six) = NonZeroU32::new(6) else {
        panic!("fixture binder has six parameter positions");
    };
    let Some(two) = NonZeroU32::new(2) else {
        panic!("fixture binder has two parameters");
    };
    let sparse_first = graph.factor(FactorNode::Bound(BoundRef::new(0, 2)));
    let sparse_second = graph.factor(FactorNode::Bound(BoundRef::new(0, 5)));
    let sparse = normalize_generic(
        &graph,
        six,
        &Callable {
            params: vec![graph.union([sparse_first.clone(), sparse_second.clone()])],
            ret: graph.factor(FactorNode::Tuple(vec![sparse_first, sparse_second])),
        },
    );
    let first = graph.factor(FactorNode::Bound(BoundRef::new(0, 0)));
    let second = graph.factor(FactorNode::Bound(BoundRef::new(0, 1)));
    let dense = normalize_generic(
        &graph,
        two,
        &Callable {
            params: vec![graph.union([first.clone(), second.clone()])],
            ret: graph.factor(FactorNode::Tuple(vec![first.clone(), second.clone()])),
        },
    );
    assert_eq!(sparse, dense);

    let role_changed = normalize_generic(
        &graph,
        two,
        &Callable {
            params: vec![graph.union([first.clone(), second.clone()])],
            ret: graph.factor(FactorNode::Tuple(vec![second.clone(), first.clone()])),
        },
    );
    assert_ne!(sparse, role_changed);

    let FactorNode::Generic(generic) = sparse.node() else {
        panic!("two live parameters must retain the binder");
    };
    assert_eq!(generic.parameters.get(), 2);
    assert_eq!(
        generic.body.ret,
        graph.factor(FactorNode::Tuple(vec![first, second]))
    );
}

#[test]
fn fixed_generic_subtype_laws_hold() {
    let mut problem = RawProblem::new("class A;");
    let a = lookup_class(&problem.declarations, "A");
    let a_type = problem.types.intern_class(a, Vec::new());
    let object = problem.types.intern_class(ClassId::OBJECT, Vec::new());
    let never = problem.types.intern_class(ClassId::NEVER, Vec::new());
    let generic = generic_identity(&mut problem);
    let a_identity = problem.types.intern_callable(vec![a_type], a_type);
    let bottom_function = problem.types.intern_callable(vec![object], never);
    let top_function = problem.types.intern_callable(vec![never], object);
    let constant_parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let constant_body = Callable {
        params: vec![constant_parameter],
        ret: a_type,
    };
    let constant = problem.types.intern_generic(1, &constant_body);
    let generic_argument_constant = problem.types.intern_callable(vec![generic], a_type);
    let generic_argument_top = problem.types.intern_callable(vec![generic], top_function);

    for (lower, upper, expected) in [
        (generic, a_identity, true),
        (bottom_function, generic, true),
        (a_identity, generic, false),
        (generic, generic, true),
        (constant, generic_argument_constant, true),
        (generic, generic_argument_top, true),
    ] {
        let atom = problem.atoms.intern_atom(lower, upper);
        assert_eq!(
            matches!(
                solve(&Input::fixture(&problem), atom),
                TheoryResult::Satisfiable(_)
            ),
            expected,
            "unexpected verdict for {lower:?} <: {upper:?}"
        );
    }
}

#[test]
fn generic_callable_disjointness_uses_callable_shape_and_arity() {
    let mut problem = RawProblem::new("class A;");
    let a = lookup_class(&problem.declarations, "A");
    let a_type = problem.types.intern_class(a, Vec::new());
    let never = problem.types.intern_class(ClassId::NEVER, Vec::new());
    let generic = generic_identity(&mut problem);
    let tuple = problem.types.intern_tuple(vec![a_type]);
    let tuple_intersection = problem.types.intern_intersection(vec![generic, tuple]);
    let tuple_bottom = problem.atoms.intern_atom(tuple_intersection, never);
    assert!(matches!(
        solve(&Input::fixture(&problem), tuple_bottom),
        TheoryResult::Satisfiable(_)
    ));

    let same_arity = problem.types.intern_callable(vec![a_type], a_type);
    let overlapping = problem.types.intern_intersection(vec![generic, same_arity]);
    let not_bottom = problem.atoms.intern_atom(overlapping, never);
    assert!(matches!(
        solve(&Input::fixture(&problem), not_bottom),
        TheoryResult::Unsatisfiable
    ));

    let different_arity = problem.types.intern_callable(vec![a_type, a_type], a_type);
    let disjoint = problem
        .types
        .intern_intersection(vec![generic, different_arity]);
    let arity_bottom = problem.atoms.intern_atom(disjoint, never);
    assert!(matches!(
        solve(&Input::fixture(&problem), arity_bottom),
        TheoryResult::Satisfiable(_)
    ));
}

#[test]
fn a_bound_parameter_cannot_select_a_generic() {
    let mut problem = RawProblem::new("");
    let generic = generic_identity(&mut problem);
    let generic_function = problem.types.intern_callable(vec![generic], generic);
    let atom = problem.atoms.intern_atom(generic, generic_function);
    assert!(matches!(
        solve(&Input::fixture(&problem), atom),
        TheoryResult::Unsatisfiable
    ));
}

#[test]
fn declared_assignment_keeps_a_generic_callable() {
    let mut problem = RawProblem::new("");
    let selected = problem.declare_metavar("T");
    let generic = generic_identity(&mut problem);
    let atom = problem
        .atoms
        .intern_atom(generic, problem.types.types().metavar_type(selected));
    let TheoryResult::Satisfiable(solution) = solve(&Input::fixture(&problem), atom) else {
        panic!("generic lower bound must be satisfiable");
    };
    let model = build_model(&problem.declarations, solution);
    assert_eq!(model.entries()[0].value().render(), "forall T0. (T0) -> T0");
}

#[test]
fn generic_model_names_do_not_collide_with_classes() {
    let mut problem = RawProblem::new("class T0;");
    let selected = problem.declare_metavar("T");
    let generic = generic_identity(&mut problem);
    let atom = problem
        .atoms
        .intern_atom(generic, problem.types.types().metavar_type(selected));
    let TheoryResult::Satisfiable(solution) = solve(&Input::fixture(&problem), atom) else {
        panic!("generic lower bound must be satisfiable");
    };
    let model = build_model(&problem.declarations, solution);
    assert_eq!(model.entries()[0].value().render(), "forall T1. (T1) -> T1");
}

#[test]
fn nested_generic_model_names_follow_relative_binders() {
    let mut problem = RawProblem::new("");
    let selected = problem.declare_metavar("T");
    let inner_parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let outer_from_inner = problem.types.intern_bound(BoundRef::new(1, 0));
    let inner_return = problem
        .types
        .intern_union(vec![inner_parameter, outer_from_inner]);
    let inner_body = Callable {
        params: Vec::new(),
        ret: inner_return,
    };
    let inner = problem.types.intern_generic(1, &inner_body);
    let outer_parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let outer_body = Callable {
        params: vec![outer_parameter],
        ret: inner,
    };
    let outer = problem.types.intern_generic(1, &outer_body);
    let atom = problem
        .atoms
        .intern_atom(outer, problem.types.types().metavar_type(selected));
    let TheoryResult::Satisfiable(solution) = solve(&Input::fixture(&problem), atom) else {
        panic!("nested generic lower bound must be satisfiable");
    };
    let model = build_model(&problem.declarations, solution);
    assert_eq!(
        model.entries()[0].value().render(),
        "forall T0. (T0) -> forall T1. () -> T0 | T1"
    );
}

#[test]
fn final_normalization_keeps_generic_and_monomorphic_factors() {
    let mut problem = RawProblem::new("");
    let selected = problem.declare_metavar("T");
    let object = problem.types.intern_class(ClassId::OBJECT, Vec::new());
    let parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let generic_body = Callable {
        params: vec![parameter],
        ret: object,
    };
    let generic = problem.types.intern_generic(1, &generic_body);
    let monomorphic = problem.types.intern_callable(vec![object], object);
    let selected_type = problem.types.types().metavar_type(selected);
    let first = problem.atoms.intern_atom(generic, selected_type);
    let second = problem.atoms.intern_atom(monomorphic, selected_type);
    let result = solve_conjunction(&[first, second], &Input::fixture(&problem));
    let TheoryResult::Satisfiable(solution) = result else {
        panic!("mixed generic and monomorphic lower bounds must be satisfiable");
    };
    let model = build_model(&problem.declarations, solution);
    assert_eq!(
        model.entries()[0].value().render(),
        "((object) -> object) | (forall T0. (T0) -> object)"
    );
}

#[test]
fn upper_generic_introduction_precedes_lower_instantiation() {
    let mut problem = RawProblem::new("");
    let lower_parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let object = problem.types.intern_class(ClassId::OBJECT, Vec::new());
    let lower_body = Callable {
        params: vec![lower_parameter],
        ret: lower_parameter,
    };
    let lower = problem.types.intern_generic(1, &lower_body);
    let upper_parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let upper_body = Callable {
        params: vec![upper_parameter],
        ret: object,
    };
    let upper = problem.types.intern_generic(1, &upper_body);
    let forward = problem.atoms.intern_atom(lower, upper);
    let reverse = problem.atoms.intern_atom(upper, lower);
    assert!(matches!(
        solve(&Input::fixture(&problem), forward),
        TheoryResult::Satisfiable(_)
    ));
    assert!(matches!(
        solve(&Input::fixture(&problem), reverse),
        TheoryResult::Unsatisfiable
    ));
}

#[test]
fn one_deferred_choice_collects_two_required_instances() {
    let mut problem = RawProblem::new("class A; class B;");
    let a = lookup_class(&problem.declarations, "A");
    let b = lookup_class(&problem.declarations, "B");
    let a_type = problem.types.intern_class(a, Vec::new());
    let b_type = problem.types.intern_class(b, Vec::new());
    let generic = generic_identity(&mut problem);
    let a_identity = problem.types.intern_callable(vec![a_type], a_type);
    let b_identity = problem.types.intern_callable(vec![b_type], b_type);
    let required = problem
        .types
        .intern_intersection(vec![a_identity, b_identity]);
    let upper = problem.types.intern_callable(vec![generic], required);
    let atom = problem.atoms.intern_atom(generic, upper);
    assert!(matches!(
        solve(&Input::fixture(&problem), atom),
        TheoryResult::Satisfiable(_)
    ));
}

#[test]
fn an_unused_deferred_choice_closes_as_object() {
    let mut problem = RawProblem::new("");
    let selected = problem.declare_metavar("T");
    let generic = generic_identity(&mut problem);
    let upper = problem
        .types
        .intern_callable(vec![generic], problem.types.types().metavar_type(selected));
    let atom = problem.atoms.intern_atom(generic, upper);
    let TheoryResult::Satisfiable(solution) = solve(&Input::fixture(&problem), atom) else {
        panic!("unused deferred choice must be satisfiable");
    };
    let model = build_model(&problem.declarations, solution);
    assert_eq!(model.entries()[0].value().render(), "object");
}

#[test]
fn nested_deferred_choice_keeps_its_instances_inside_the_tuple() {
    let mut problem = RawProblem::new("class A; class B;");
    let a = lookup_class(&problem.declarations, "A");
    let b = lookup_class(&problem.declarations, "B");
    let a_type = problem.types.intern_class(a, Vec::new());
    let b_type = problem.types.intern_class(b, Vec::new());
    let generic = generic_identity(&mut problem);
    let tuple_generic = problem.types.intern_tuple(vec![generic]);
    let a_identity = problem.types.intern_callable(vec![a_type], a_type);
    let b_identity = problem.types.intern_callable(vec![b_type], b_type);
    let required = problem
        .types
        .intern_intersection(vec![a_identity, b_identity]);
    let tuple_required = problem.types.intern_tuple(vec![required]);
    let upper = problem
        .types
        .intern_callable(vec![tuple_generic], tuple_required);
    let atom = problem.atoms.intern_atom(generic, upper);
    assert!(matches!(
        solve(&Input::fixture(&problem), atom),
        TheoryResult::Satisfiable(_)
    ));
}

#[test]
fn deferred_instances_cannot_remove_a_guard_requirement() {
    let mut problem = RawProblem::new("class A; class C; class D;");
    let a = lookup_class(&problem.declarations, "A");
    let c = lookup_class(&problem.declarations, "C");
    let d = lookup_class(&problem.declarations, "D");
    let selected = problem.declare_metavar("Z");
    let a_type = problem.types.intern_class(a, Vec::new());
    let c_type = problem.types.intern_class(c, Vec::new());
    let d_type = problem.types.intern_class(d, Vec::new());
    let parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let overlap = problem.types.intern_intersection(vec![parameter, c_type]);
    let lower_return = problem.types.intern_tuple(vec![overlap, parameter]);
    let lower_body = Callable {
        params: vec![parameter],
        ret: lower_return,
    };
    let lower = problem.types.intern_generic(1, &lower_body);

    let generic = generic_identity(&mut problem);
    let a_identity = problem.types.intern_callable(vec![a_type], a_type);
    let upper_return = problem.types.intern_tuple(vec![
        problem.types.types().metavar_type(selected),
        a_identity,
    ]);
    let upper = problem.types.intern_callable(vec![generic], upper_return);
    let first = problem.atoms.intern_atom(lower, upper);
    let second = problem
        .atoms
        .intern_atom(problem.types.types().metavar_type(selected), d_type);
    assert!(matches!(
        solve_conjunction(&[first, second], &Input::fixture(&problem)),
        TheoryResult::Unsatisfiable
    ));
}

#[test]
fn empty_deferred_choice_has_object_shape() {
    let mut problem = RawProblem::new("class C; class D;");
    let c = lookup_class(&problem.declarations, "C");
    let d = lookup_class(&problem.declarations, "D");
    let c_type = problem.types.intern_class(c, Vec::new());
    let d_type = problem.types.intern_class(d, Vec::new());
    let parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let result = problem.types.intern_intersection(vec![parameter, c_type]);
    let body = Callable {
        params: vec![parameter, parameter],
        ret: result,
    };
    let lower = problem.types.intern_generic(1, &body);
    let generic = generic_identity(&mut problem);
    let upper = problem.types.intern_callable(vec![generic, c_type], d_type);
    let atom = problem.atoms.intern_atom(lower, upper);
    assert!(matches!(
        solve(&Input::fixture(&problem), atom),
        TheoryResult::Unsatisfiable
    ));
}

#[test]
fn conversion_that_removes_every_binder_stores_a_monomorphic_callable() {
    let mut problem = RawProblem::new("class A;");
    let a = lookup_class(&problem.declarations, "A");
    let selected = problem.declare_metavar("T");
    let a_type = problem.types.intern_class(a, Vec::new());

    let inner_parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let outer_from_inner = problem.types.intern_bound(BoundRef::new(1, 0));
    let inner_return = problem
        .types
        .intern_union(vec![inner_parameter, outer_from_inner]);
    let inner_body = Callable {
        params: Vec::new(),
        ret: inner_return,
    };
    let inner = problem.types.intern_generic(1, &inner_body);
    let outer_parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let outer_body = Callable {
        params: vec![inner],
        ret: outer_parameter,
    };
    let outer = problem.types.intern_generic(1, &outer_body);
    let incoming = problem.types.intern_callable(vec![outer], a_type);

    let lower = generic_identity(&mut problem);
    let upper = problem
        .types
        .intern_callable(vec![incoming], problem.types.types().metavar_type(selected));
    let atom = problem.atoms.intern_atom(lower, upper);
    let TheoryResult::Satisfiable(solution) = solve(&Input::fixture(&problem), atom) else {
        panic!("binder-removing conversion must be satisfiable");
    };
    let model = build_model(&problem.declarations, solution);
    assert_eq!(
        model.entries()[0].value().render(),
        "((() -> object) -> never) -> A"
    );
}

#[test]
fn conversion_reindexes_the_binders_that_remain() {
    let mut problem = RawProblem::new("class A;");
    let a = lookup_class(&problem.declarations, "A");
    let selected = problem.declare_metavar("T");
    let a_type = problem.types.intern_class(a, Vec::new());

    let removed = problem.types.intern_bound(BoundRef::new(0, 0));
    let retained = problem.types.intern_bound(BoundRef::new(0, 1));
    let outer_from_inner = problem.types.intern_bound(BoundRef::new(1, 0));
    let first = problem.types.intern_union(vec![removed, outer_from_inner]);
    let inner_return = problem.types.intern_tuple(vec![first, retained]);
    let inner_body = Callable {
        params: Vec::new(),
        ret: inner_return,
    };
    let inner = problem.types.intern_generic(2, &inner_body);
    let outer_parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let outer_body = Callable {
        params: vec![inner],
        ret: outer_parameter,
    };
    let outer = problem.types.intern_generic(1, &outer_body);
    let incoming = problem.types.intern_callable(vec![outer], a_type);

    let lower = generic_identity(&mut problem);
    let object = problem.types.intern_class(ClassId::OBJECT, Vec::new());
    let never = problem.types.intern_class(ClassId::NEVER, Vec::new());
    let selected_return = problem.types.intern_tuple(vec![object, a_type]);
    let selected_inner = problem.types.intern_callable(Vec::new(), selected_return);
    let required_outer = problem.types.intern_callable(vec![selected_inner], never);
    let required = problem.types.intern_callable(vec![required_outer], a_type);
    let upper_return = problem
        .types
        .intern_intersection(vec![problem.types.types().metavar_type(selected), required]);
    let upper = problem.types.intern_callable(vec![incoming], upper_return);
    let atom = problem.atoms.intern_atom(lower, upper);
    let TheoryResult::Satisfiable(solution) = solve(&Input::fixture(&problem), atom) else {
        panic!("partial binder-removing conversion must be satisfiable");
    };
    let model = build_model(&problem.declarations, solution);
    assert_eq!(
        model.entries()[0].value().render(),
        "((() -> tuple[object, never]) -> never) -> A"
    );
}

#[test]
fn model_closure_removes_a_binder_hidden_by_an_assignment() {
    let mut problem = RawProblem::new("class A;");
    let a = lookup_class(&problem.declarations, "A");
    let source = problem.declare_metavar("V");
    let selected = problem.declare_metavar("T");
    let a_type = problem.types.intern_class(a, Vec::new());
    let parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let input = problem
        .types
        .intern_union(vec![parameter, problem.types.types().metavar_type(source)]);
    let body = Callable {
        params: vec![input],
        ret: a_type,
    };
    let generic = problem.types.intern_generic(1, &body);
    let first = problem
        .atoms
        .intern_atom(generic, problem.types.types().metavar_type(selected));
    let object = problem.types.intern_class(ClassId::OBJECT, Vec::new());
    let second = problem
        .atoms
        .intern_atom(object, problem.types.types().metavar_type(source));
    let result = solve_conjunction(&[first, second], &Input::fixture(&problem));
    let TheoryResult::Satisfiable(solution) = result else {
        panic!("model-closing binder removal must be satisfiable");
    };
    let model = build_model(&problem.declarations, solution);
    assert_eq!(model.entries()[0].value().render(), "object");
    assert_eq!(model.entries()[1].value().render(), "(object) -> A");
}

#[test]
fn upper_union_backtracks_between_independent_generic_comparisons() {
    let mut problem = RawProblem::new("class B; class A;");
    let b = lookup_class(&problem.declarations, "B");
    let a = lookup_class(&problem.declarations, "A");
    let a_type = problem.types.intern_class(a, Vec::new());
    let b_type = problem.types.intern_class(b, Vec::new());
    let generic = generic_identity(&mut problem);
    let failing = problem.types.intern_callable(vec![a_type], b_type);
    let succeeding = problem.types.intern_callable(vec![a_type], a_type);
    let upper = problem.types.intern_union(vec![failing, succeeding]);
    let atom = problem.atoms.intern_atom(generic, upper);
    assert!(matches!(
        solve(&Input::fixture(&problem), atom),
        TheoryResult::Satisfiable(_)
    ));
}

#[test]
fn existing_instance_variables_grow_after_a_declared_variable_changes() {
    let mut problem = RawProblem::new("class A; class B extends A;");
    let a = lookup_class(&problem.declarations, "A");
    let b = lookup_class(&problem.declarations, "B");
    let selected = problem.declare_metavar("V");
    let a_type = problem.types.intern_class(a, Vec::new());
    let b_type = problem.types.intern_class(b, Vec::new());
    let generic = generic_identity(&mut problem);
    let required = problem
        .types
        .intern_callable(vec![problem.types.types().metavar_type(selected)], a_type);
    let upper = problem.types.intern_callable(vec![generic], required);
    let first = problem.atoms.intern_atom(generic, upper);
    let second = problem
        .atoms
        .intern_atom(b_type, problem.types.types().metavar_type(selected));
    let result = solve_conjunction(&[first, second], &Input::fixture(&problem));
    let TheoryResult::Satisfiable(solution) = result else {
        panic!("existing instance must grow to accept the later lower bound");
    };
    let model = build_model(&problem.declarations, solution);
    assert_eq!(model.entries()[0].value().render(), "B");
}

#[test]
fn deferred_source_converts_declared_references_only_when_instantiated() {
    let mut problem = RawProblem::new("class A; class B; class C extends B;");
    let a = lookup_class(&problem.declarations, "A");
    let b = lookup_class(&problem.declarations, "B");
    let c = lookup_class(&problem.declarations, "C");
    let selected_return = problem.declare_metavar("K");
    let stored_generic = problem.declare_metavar("G");
    let a_type = problem.types.intern_class(a, Vec::new());
    let b_type = problem.types.intern_class(b, Vec::new());
    let c_type = problem.types.intern_class(c, Vec::new());

    let parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let body = Callable {
        params: vec![parameter],
        ret: problem.types.types().metavar_type(selected_return),
    };
    let generic_with_declared_return = problem.types.intern_generic(1, &body);
    let store = problem.atoms.intern_atom(
        generic_with_declared_return,
        problem.types.types().metavar_type(stored_generic),
    );

    let lower = generic_identity(&mut problem);
    let required = problem.types.intern_callable(vec![a_type], b_type);
    let upper = problem.types.intern_callable(
        vec![problem.types.types().metavar_type(stored_generic)],
        required,
    );
    let instantiate = problem.atoms.intern_atom(lower, upper);
    let grow = problem
        .atoms
        .intern_atom(c_type, problem.types.types().metavar_type(selected_return));
    let solved = solve_conjunction(&[store, instantiate, grow], &Input::fixture(&problem));
    let TheoryResult::Satisfiable(solution) = solved else {
        panic!("deferred proxy of a declared reference must track later growth");
    };
    let model = build_model(&problem.declarations, solution);
    assert_eq!(model.entries()[0].value().render(), "C");
    assert_eq!(model.entries()[1].value().render(), "forall T0. (T0) -> C");
}

#[test]
fn deferred_source_outward_proxy_tracks_its_instance_selection() {
    let mut problem = RawProblem::new("class A; class B;");
    let a_class = lookup_class(&problem.declarations, "A");
    let b_class = lookup_class(&problem.declarations, "B");
    let a_type = problem.types.intern_class(a_class, Vec::new());
    let b_type = problem.types.intern_class(b_class, Vec::new());
    let never = problem.types.intern_class(ClassId::NEVER, Vec::new());

    let lower_bound = problem.types.intern_bound(BoundRef::new(0, 0));
    let lower_parameter = problem.types.intern_callable(vec![a_type], lower_bound);
    let lower_body = Callable {
        params: vec![lower_parameter],
        ret: lower_bound,
    };
    let lower = problem.types.intern_generic(1, &lower_body);

    let inner_bound = problem.types.intern_bound(BoundRef::new(0, 0));
    let x_from_inner = problem.types.intern_bound(BoundRef::new(1, 0));
    let inner_body = Callable {
        params: vec![inner_bound],
        ret: x_from_inner,
    };
    let inner = problem.types.intern_generic(1, &inner_body);
    let outer_bound = problem.types.intern_bound(BoundRef::new(0, 0));
    let outer_return = problem.types.intern_tuple(vec![inner]);
    let outer_body = Callable {
        params: vec![outer_bound],
        ret: outer_return,
    };
    let outer = problem.types.intern_generic(1, &outer_body);

    let satisfiable_use = problem.types.intern_callable(vec![b_type], a_type);
    let satisfiable_return = problem.types.intern_tuple(vec![satisfiable_use]);
    let satisfiable_upper = problem
        .types
        .intern_callable(vec![outer], satisfiable_return);
    let satisfiable = problem.atoms.intern_atom(lower, satisfiable_upper);
    assert!(matches!(
        solve(&Input::fixture(&problem), satisfiable),
        TheoryResult::Satisfiable(_)
    ));

    let conflicting_use = problem.types.intern_callable(vec![b_type], never);
    let conflicting_return = problem.types.intern_tuple(vec![conflicting_use]);
    let conflicting_upper = problem
        .types
        .intern_callable(vec![outer], conflicting_return);
    let conflicting = problem.atoms.intern_atom(lower, conflicting_upper);
    assert!(matches!(
        solve(&Input::fixture(&problem), conflicting),
        TheoryResult::Unsatisfiable
    ));
}

#[test]
fn ordinary_factor_can_cover_without_creating_a_generic_instance() {
    let mut problem = RawProblem::new("class A; class B;");
    let a = lookup_class(&problem.declarations, "A");
    let b = lookup_class(&problem.declarations, "B");
    let a_type = problem.types.intern_class(a, Vec::new());
    let b_type = problem.types.intern_class(b, Vec::new());
    let object = problem.types.intern_class(ClassId::OBJECT, Vec::new());
    let generic = generic_identity(&mut problem);
    let ordinary = problem.types.intern_callable(vec![object], a_type);
    let upper_parameter = problem.types.intern_intersection(vec![generic, ordinary]);
    let upper_return = problem.types.intern_callable(vec![b_type], a_type);
    let upper = problem
        .types
        .intern_callable(vec![upper_parameter], upper_return);
    let atom = problem.atoms.intern_atom(generic, upper);
    assert!(matches!(
        solve(&Input::fixture(&problem), atom),
        TheoryResult::Satisfiable(_)
    ));
}

#[test]
fn bound_reference_has_unknown_shape_during_model_normalization() {
    let mut problem = RawProblem::new("class A;");
    let a = lookup_class(&problem.declarations, "A");
    let selected = problem.declare_metavar("T");
    let a_type = problem.types.intern_class(a, Vec::new());
    let parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let tuple_a = problem.types.intern_tuple(vec![a_type]);
    let input = problem.types.intern_intersection(vec![parameter, tuple_a]);
    let body = Callable {
        params: vec![input],
        ret: parameter,
    };
    let generic = problem.types.intern_generic(1, &body);
    let atom = problem
        .atoms
        .intern_atom(generic, problem.types.types().metavar_type(selected));
    let TheoryResult::Satisfiable(solution) = solve(&Input::fixture(&problem), atom) else {
        panic!("unknown-shape bound reference must overlap a tuple");
    };
    let model = build_model(&problem.declarations, solution);
    assert_eq!(
        model.entries()[0].value().render(),
        "forall T0. (T0 & tuple[A]) -> T0"
    );
}
