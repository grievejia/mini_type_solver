//! Closed-value rules and the conjunction result contract.

use crate::frontend::problem::{AtomFormula, ClassType, TypeId, TypeNode};
use crate::frontend::test_support::{RawProblem, lookup_class};
use crate::solver::input::Input;
use crate::solver::test_support::{atom_id, validate_ok};

use super::closed::Value;
use super::test_support::DnfValue;

use super::{ClassId, MetaVarId, TheoryResult, solve_conjunction};
use std::collections::BTreeMap;

#[derive(Debug)]
struct Fixture {
    problem: RawProblem,
    a: ClassId,
    b: ClassId,
    t: MetaVarId,
    u: MetaVarId,
}

fn fixture(declarations: &str) -> Fixture {
    let mut problem = RawProblem::new(declarations);
    let t = problem.declare_metavar("T");
    let u = problem.declare_metavar("U");
    let a = lookup_class(&problem.declarations, "a");
    let b = lookup_class(&problem.declarations, "b");
    Fixture {
        problem,
        a,
        b,
        t,
        u,
    }
}

fn tuple_type(problem: &mut RawProblem, elements: &[TypeId]) -> TypeId {
    problem.types.intern_tuple(elements.to_vec())
}

fn assignment_value(assignments: &BTreeMap<MetaVarId, Value>, metavar: MetaVarId) -> DnfValue {
    let Some(value) = assignments.get(&metavar) else {
        panic!("expected an assignment for {metavar:?}");
    };
    DnfValue::from_closed(value)
}

fn assignment_arms(
    assignments: &BTreeMap<MetaVarId, Value>,
    metavar: MetaVarId,
) -> Vec<Vec<ClassId>> {
    assignment_value(assignments, metavar).class_arms()
}

#[test]
fn closed_classes_follow_builtin_edges_and_linearizations() {
    let mut problem = RawProblem::new("class animal;\nclass dog extends animal;");
    let dog = lookup_class(&problem.declarations, "dog");
    let animal = lookup_class(&problem.declarations, "animal");
    let object = ClassId::OBJECT;
    let never = ClassId::NEVER;
    for (lower, upper, expected) in [
        (dog, dog, true),
        (never, dog, true),
        (never, never, true),
        (never, object, true),
        (dog, object, true),
        (object, object, true),
        (animal, object, true),
        (dog, animal, true),
        (animal, dog, false),
        (dog, never, false),
        (object, dog, false),
        (animal, never, false),
    ] {
        let atom = atom_id(
            &mut problem,
            TypeNode::Class(ClassType::plain(lower)),
            TypeNode::Class(ClassType::plain(upper)),
        );
        assert_eq!(
            matches!(
                solve_conjunction(&[atom], &Input::fixture(&problem)),
                TheoryResult::Satisfiable(_)
            ),
            expected,
            "{lower:?} <: {upper:?}"
        );
    }
}

#[test]
fn ground_tuple_relations_follow_covariance_and_disjointness() {
    let Fixture {
        mut problem, a, b, ..
    } = fixture("class a extends b; class b;");
    let a_type = problem.types.intern_class(a, Vec::new());
    let b_type = problem.types.intern_class(b, Vec::new());
    let never = problem.types.intern_class(ClassId::NEVER, Vec::new());
    let object = problem.types.intern_class(ClassId::OBJECT, Vec::new());
    let tuple_a = tuple_type(&mut problem, &[a_type]);
    let tuple_b = tuple_type(&mut problem, &[b_type]);
    let tuple_aa = tuple_type(&mut problem, &[a_type, a_type]);
    let tuple_never = tuple_type(&mut problem, &[never]);
    let empty = tuple_type(&mut problem, &[]);

    for (lower, upper, expected) in [
        (tuple_a, tuple_b, true),
        (tuple_b, tuple_a, false),
        (tuple_a, tuple_aa, false),
        (tuple_aa, tuple_a, false),
        (tuple_a, a_type, false),
        (a_type, tuple_a, false),
        (never, tuple_a, true),
        (tuple_a, object, true),
        (tuple_never, never, false),
        (empty, empty, true),
    ] {
        let atom = problem.atoms.intern_atom(lower, upper);
        assert_eq!(
            matches!(
                solve_conjunction(&[atom], &Input::fixture(&problem)),
                TheoryResult::Satisfiable(_)
            ),
            expected,
            "unexpected tuple relation for {lower:?} <: {upper:?}"
        );
    }
}

#[test]
fn tuple_bounds_assign_and_check_a_complete_metavariable() {
    let Fixture {
        mut problem,
        a,
        b,
        t,
        ..
    } = fixture("class a extends b; class b;");
    let a_type = problem.types.intern_class(a, Vec::new());
    let b_type = problem.types.intern_class(b, Vec::new());
    let tuple_a = tuple_type(&mut problem, &[a_type]);
    let tuple_b = tuple_type(&mut problem, &[b_type]);
    let t_type = problem.types.types().metavar_type(t);
    let atoms = [
        problem.atoms.intern_atom(tuple_a, t_type),
        problem.atoms.intern_atom(t_type, tuple_b),
    ];
    let TheoryResult::Satisfiable(solution) = solve_conjunction(&atoms, &Input::fixture(&problem))
    else {
        panic!("expected covariant tuple bounds to satisfy");
    };
    let assignments = solution.into_assignments();

    assert_eq!(
        assignment_value(&assignments, t),
        DnfValue::tuple(vec![DnfValue::class(a)])
    );
}

#[test]
fn nested_tuple_lower_is_rechecked_after_element_assignment_growth() {
    let Fixture {
        mut problem,
        a,
        b,
        t,
        u,
    } = fixture("class a; class b;");
    let a_type = problem.types.intern_class(a, Vec::new());
    let b_type = problem.types.intern_class(b, Vec::new());
    let t_type = problem.types.types().metavar_type(t);
    let u_type = problem.types.types().metavar_type(u);
    let lower_tuple = tuple_type(&mut problem, &[a_type, u_type]);
    let upper_tuple = tuple_type(&mut problem, &[a_type, b_type]);
    let atoms = [
        problem.atoms.intern_atom(lower_tuple, t_type),
        problem.atoms.intern_atom(b_type, u_type),
        problem.atoms.intern_atom(t_type, upper_tuple),
    ];
    let TheoryResult::Satisfiable(solution) = solve_conjunction(&atoms, &Input::fixture(&problem))
    else {
        panic!("expected nested tuple assignments to satisfy");
    };
    let assignments = solution.into_assignments();

    assert_eq!(assignment_arms(&assignments, u), [[b]]);
    assert_eq!(
        assignment_value(&assignments, t),
        DnfValue::tuple(vec![DnfValue::class(a), DnfValue::class(b)])
    );
}

#[test]
fn preserved_tuple_reference_rechecks_an_indirect_lower_dependency() {
    let Fixture {
        mut problem,
        a,
        b,
        t,
        u,
    } = fixture("class a; class b;");
    let a_type = problem.types.intern_class(a, Vec::new());
    let b_type = problem.types.intern_class(b, Vec::new());
    let t_type = problem.types.types().metavar_type(t);
    let u_type = problem.types.types().metavar_type(u);
    let tuple_u = tuple_type(&mut problem, &[u_type]);
    let tuple_a = tuple_type(&mut problem, &[a_type]);
    let atoms = [
        problem.atoms.intern_atom(tuple_u, t_type),
        problem.atoms.intern_atom(t_type, tuple_a),
        problem.atoms.intern_atom(b_type, u_type),
    ];

    assert_eq!(
        solve_conjunction(&atoms, &Input::fixture(&problem)),
        TheoryResult::Unsatisfiable
    );
}

#[test]
fn final_closing_preserves_a_recursive_programmatic_assignment() {
    let Fixture {
        mut problem,
        t,
        u: s,
        ..
    } = fixture("class a; class b;");
    let t_type = problem.types.types().metavar_type(t);
    let s_type = problem.types.types().metavar_type(s);
    let tuple_t = tuple_type(&mut problem, &[t_type]);
    let tuple_s = tuple_type(&mut problem, &[s_type]);
    let atoms = [
        problem.atoms.intern_atom(tuple_t, s_type),
        problem.atoms.intern_atom(tuple_s, t_type),
    ];

    let TheoryResult::Satisfiable(solution) = solve_conjunction(&atoms, &Input::fixture(&problem))
    else {
        panic!("both equations describe a guarded tuple cycle");
    };
    assert_eq!(solution.witness(t), solution.witness(s));
    assert!(solution.witness(t).is_some_and(Value::is_recursive));
}

#[test]
fn non_ground_always_disjoint_intersections_are_bottom() {
    let Fixture {
        mut problem,
        a,
        b,
        u,
        ..
    } = fixture("class a; class b;");
    let a_type = problem.types.intern_class(a, Vec::new());
    let b_type = problem.types.intern_class(b, Vec::new());
    let u_type = problem.types.types().metavar_type(u);
    let tuple_u = tuple_type(&mut problem, &[u_type]);
    let empty_tuple = tuple_type(&mut problem, &[]);
    let class_and_tuple = problem.types.intern_intersection(vec![a_type, tuple_u]);
    let different_tuple_lengths = problem
        .types
        .intern_intersection(vec![tuple_u, empty_tuple]);

    for lower in [class_and_tuple, different_tuple_lengths] {
        let atom = problem.atoms.intern_atom(lower, b_type);
        assert!(matches!(
            solve_conjunction(&[atom], &Input::fixture(&problem)),
            TheoryResult::Satisfiable(_)
        ));
    }
}

#[test]
fn tuple_elements_add_different_arms_to_one_metavariable() {
    let Fixture {
        mut problem,
        a,
        b,
        t,
        ..
    } = fixture("class a; class b;");
    let holder = problem.declare_metavar("Holder");
    let a_type = problem.types.intern_class(a, Vec::new());
    let b_type = problem.types.intern_class(b, Vec::new());
    let t_type = problem.types.types().metavar_type(t);
    let holder_type = problem.types.types().metavar_type(holder);
    let lower_tuple = tuple_type(&mut problem, &[a_type, b_type]);
    let upper_tuple = tuple_type(&mut problem, &[t_type, t_type]);
    let atoms = [
        problem.atoms.intern_atom(lower_tuple, holder_type),
        problem.atoms.intern_atom(holder_type, upper_tuple),
    ];
    let TheoryResult::Satisfiable(solution) = solve_conjunction(&atoms, &Input::fixture(&problem))
    else {
        panic!("expected tuple element updates to satisfy");
    };
    let assignments = solution.into_assignments();

    assert_eq!(assignment_arms(&assignments, t), [vec![a], vec![b]]);
}

#[test]
fn tuple_element_search_rolls_back_to_an_alternative_update() {
    let Fixture {
        mut problem,
        a,
        b,
        t,
        u,
    } = fixture("class a; class b;");
    let holder = problem.declare_metavar("Holder");
    let a_type = problem.types.intern_class(a, Vec::new());
    let b_type = problem.types.intern_class(b, Vec::new());
    let t_type = problem.types.types().metavar_type(t);
    let u_type = problem.types.types().metavar_type(u);
    let holder_type = problem.types.types().metavar_type(holder);
    let lower_tuple = tuple_type(&mut problem, &[a_type, a_type]);
    let element_union = problem.types.intern_union(vec![t_type, u_type]);
    let upper_tuple = tuple_type(&mut problem, &[element_union, element_union]);
    let atoms = [
        problem.atoms.intern_atom(lower_tuple, holder_type),
        problem.atoms.intern_atom(holder_type, upper_tuple),
        problem.atoms.intern_atom(t_type, b_type),
    ];
    let TheoryResult::Satisfiable(solution) = solve_conjunction(&atoms, &Input::fixture(&problem))
    else {
        panic!("expected tuple search to retry an alternative update");
    };
    let assignments = solution.into_assignments();

    assert!(assignment_arms(&assignments, t).is_empty());
    assert_eq!(assignment_arms(&assignments, u), [[a]]);
}

#[test]
fn tuple_constructor_does_not_distribute_over_boolean_types() {
    let Fixture {
        mut problem, a, b, ..
    } = fixture("class a; class b;");
    let a_type = problem.types.intern_class(a, Vec::new());
    let b_type = problem.types.intern_class(b, Vec::new());
    let tuple_a = tuple_type(&mut problem, &[a_type]);
    let tuple_b = tuple_type(&mut problem, &[b_type]);
    let element_union = problem.types.intern_union(vec![a_type, b_type]);
    let tuple_element_union = tuple_type(&mut problem, &[element_union]);
    let outer_union = problem.types.intern_union(vec![tuple_a, tuple_b]);
    let element_intersection = problem.types.intern_intersection(vec![a_type, b_type]);
    let tuple_element_intersection = tuple_type(&mut problem, &[element_intersection]);
    let outer_intersection = problem.types.intern_intersection(vec![tuple_a, tuple_b]);

    for (lower, upper, expected) in [
        (outer_union, tuple_element_union, true),
        (tuple_element_union, outer_union, false),
        (tuple_element_intersection, outer_intersection, true),
        (outer_intersection, tuple_element_intersection, false),
    ] {
        let atom = problem.atoms.intern_atom(lower, upper);
        assert_eq!(
            matches!(
                solve_conjunction(&[atom], &Input::fixture(&problem)),
                TheoryResult::Satisfiable(_)
            ),
            expected,
            "unexpected structural relation for {lower:?} <: {upper:?}"
        );
    }
}

#[test]
fn assignment_growth_rechecks_metavar_edge() {
    let Fixture {
        mut problem,
        a,
        b,
        t,
        u,
    } = fixture("class a extends b; class b;");
    let atoms = [
        atom_id(
            &mut problem,
            TypeNode::Class(ClassType::plain(a)),
            TypeNode::Flexible(t),
        ),
        atom_id(&mut problem, TypeNode::Flexible(t), TypeNode::Flexible(u)),
        atom_id(
            &mut problem,
            TypeNode::Flexible(u),
            TypeNode::Class(ClassType::plain(b)),
        ),
    ];
    let TheoryResult::Satisfiable(solution) = solve_conjunction(&atoms, &Input::fixture(&problem))
    else {
        panic!("expected dependent assignments to stay satisfiable");
    };
    let assignments = solution.into_assignments();

    assert_eq!(assignment_arms(&assignments, t), [[a]]);
    assert_eq!(assignment_arms(&assignments, u), [[a]]);
}

#[test]
fn failing_lower_against_upper_is_unsat() {
    let Fixture {
        mut problem,
        a,
        b,
        t,
        ..
    } = fixture("class a; class b;");
    let atoms = [
        atom_id(
            &mut problem,
            TypeNode::Class(ClassType::plain(a)),
            TypeNode::Flexible(t),
        ),
        atom_id(
            &mut problem,
            TypeNode::Flexible(t),
            TypeNode::Class(ClassType::plain(b)),
        ),
    ];
    assert_eq!(
        solve_conjunction(&atoms, &Input::fixture(&problem)),
        TheoryResult::Unsatisfiable
    );
}

#[test]
fn unrelated_uppers_stay_sat_through_never() {
    let Fixture {
        mut problem,
        a,
        b,
        t,
        ..
    } = fixture("class a; class b;");
    let atoms = [
        atom_id(
            &mut problem,
            TypeNode::Flexible(t),
            TypeNode::Class(ClassType::plain(a)),
        ),
        atom_id(
            &mut problem,
            TypeNode::Flexible(t),
            TypeNode::Class(ClassType::plain(b)),
        ),
    ];
    let TheoryResult::Satisfiable(solution) = solve_conjunction(&atoms, &Input::fixture(&problem))
    else {
        panic!("expected unrelated uppers to stay satisfiable");
    };
    let assignments = solution.into_assignments();

    assert!(assignment_arms(&assignments, t).is_empty());
}

#[test]
fn metavar_cycle_shares_assignments() {
    let Fixture {
        mut problem,
        a,
        t,
        u,
        ..
    } = fixture("class a; class b;");
    let atoms = [
        atom_id(&mut problem, TypeNode::Flexible(t), TypeNode::Flexible(u)),
        atom_id(&mut problem, TypeNode::Flexible(u), TypeNode::Flexible(t)),
        atom_id(
            &mut problem,
            TypeNode::Class(ClassType::plain(a)),
            TypeNode::Flexible(t),
        ),
    ];
    let TheoryResult::Satisfiable(solution) = solve_conjunction(&atoms, &Input::fixture(&problem))
    else {
        panic!("expected the cycle to stay satisfiable");
    };
    let assignments = solution.into_assignments();

    assert_eq!(assignment_arms(&assignments, t), [[a]]);
    assert_eq!(assignment_arms(&assignments, u), [[a]]);
}

#[test]
fn primitive_contradiction_is_unsat() {
    for (declarations, expected) in [
        ("class a; class b;", false),
        ("class a extends b; class b;", true),
    ] {
        let Fixture {
            mut problem, a, b, ..
        } = fixture(declarations);
        let atom = atom_id(
            &mut problem,
            TypeNode::Class(ClassType::plain(a)),
            TypeNode::Class(ClassType::plain(b)),
        );
        assert_eq!(
            matches!(
                solve_conjunction(&[atom], &Input::fixture(&problem)),
                TheoryResult::Satisfiable(_)
            ),
            expected
        );
    }
}

#[test]
fn selected_assignment_uses_the_required_lower() {
    let Fixture {
        mut problem,
        a,
        b,
        t,
        ..
    } = fixture("class a extends b; class b;");
    let atoms = [
        atom_id(
            &mut problem,
            TypeNode::Class(ClassType::plain(a)),
            TypeNode::Flexible(t),
        ),
        atom_id(
            &mut problem,
            TypeNode::Flexible(t),
            TypeNode::Class(ClassType::plain(b)),
        ),
    ];
    let TheoryResult::Satisfiable(solution) = solve_conjunction(&atoms, &Input::fixture(&problem))
    else {
        panic!("expected related bounds to stay satisfiable");
    };
    let assignments = solution.into_assignments();

    assert_eq!(assignment_arms(&assignments, t), [[a]]);
}

#[test]
fn lower_union_decomposes_into_one_dnf_solver() {
    let Fixture {
        mut problem,
        a,
        b,
        t,
        ..
    } = fixture("class a; class b;");
    let a_type = problem
        .types
        .intern_type(TypeNode::Class(ClassType::plain(a)));
    let b_type = problem
        .types
        .intern_type(TypeNode::Class(ClassType::plain(b)));
    let lower = problem.types.intern_union(vec![b_type, a_type]);
    let upper = problem.types.intern_type(TypeNode::Flexible(t));
    let atoms = [problem.atoms.intern_atom(lower, upper)];
    let TheoryResult::Satisfiable(solution) = solve_conjunction(&atoms, &Input::fixture(&problem))
    else {
        panic!("expected the decomposed union to satisfy");
    };
    let assignments = solution.into_assignments();

    assert_eq!(assignment_arms(&assignments, t), [vec![a], vec![b]]);
}

#[test]
fn upper_union_uses_deterministic_assignment_updates() {
    let Fixture {
        mut problem,
        a,
        t,
        u,
        ..
    } = fixture("class a; class b;");
    let lower = problem
        .types
        .intern_type(TypeNode::Class(ClassType::plain(a)));
    let t_type = problem.types.intern_type(TypeNode::Flexible(t));
    let u_type = problem.types.intern_type(TypeNode::Flexible(u));
    let upper = problem.types.intern_union(vec![u_type, t_type]);
    let atoms = [problem.atoms.intern_atom(lower, upper)];
    let TheoryResult::Satisfiable(solution) = solve_conjunction(&atoms, &Input::fixture(&problem))
    else {
        panic!("expected one union assignment update to satisfy");
    };
    let assignments = solution.into_assignments();

    assert_eq!(assignment_arms(&assignments, t), [[a]]);
    assert!(assignment_arms(&assignments, u).is_empty());
}

#[test]
fn upper_intersection_decomposes_before_dnf_search() {
    let Fixture {
        mut problem,
        a,
        t,
        u,
        ..
    } = fixture("class a; class b;");
    let lower = problem
        .types
        .intern_type(TypeNode::Class(ClassType::plain(a)));
    let t_type = problem.types.intern_type(TypeNode::Flexible(t));
    let u_type = problem.types.intern_type(TypeNode::Flexible(u));
    let upper = problem.types.intern_intersection(vec![t_type, u_type]);
    let atoms = [problem.atoms.intern_atom(lower, upper)];
    let TheoryResult::Satisfiable(solution) = solve_conjunction(&atoms, &Input::fixture(&problem))
    else {
        panic!("expected upper intersection decomposition to satisfy");
    };
    let assignments = solution.into_assignments();

    assert_eq!(assignment_arms(&assignments, t), [[a]]);
    assert_eq!(assignment_arms(&assignments, u), [[a]]);
}

#[test]
fn union_search_retries_an_alternative_assignment_update() {
    let Fixture {
        mut problem,
        a,
        b,
        t,
        u,
    } = fixture("class a; class b;");
    let a_type = problem
        .types
        .intern_type(TypeNode::Class(ClassType::plain(a)));
    let b_type = problem
        .types
        .intern_type(TypeNode::Class(ClassType::plain(b)));
    let t_type = problem.types.intern_type(TypeNode::Flexible(t));
    let u_type = problem.types.intern_type(TypeNode::Flexible(u));
    let union = problem.types.intern_union(vec![t_type, u_type]);
    let atoms = [
        problem.atoms.intern_atom(a_type, union),
        problem.atoms.intern_atom(t_type, b_type),
    ];
    let TheoryResult::Satisfiable(solution) = solve_conjunction(&atoms, &Input::fixture(&problem))
    else {
        panic!("expected search to retry the second update");
    };
    let assignments = solution.into_assignments();

    assert!(assignment_arms(&assignments, t).is_empty());
    assert_eq!(assignment_arms(&assignments, u), [[a]]);
}

#[test]
fn union_search_exhausts_invalid_assignment_updates() {
    let Fixture {
        mut problem,
        a,
        b,
        t,
        u,
    } = fixture("class a; class b;");
    let a_type = problem
        .types
        .intern_type(TypeNode::Class(ClassType::plain(a)));
    let b_type = problem
        .types
        .intern_type(TypeNode::Class(ClassType::plain(b)));
    let t_type = problem.types.intern_type(TypeNode::Flexible(t));
    let u_type = problem.types.intern_type(TypeNode::Flexible(u));
    let union = problem.types.intern_union(vec![t_type, u_type]);
    let atoms = [
        problem.atoms.intern_atom(a_type, union),
        problem.atoms.intern_atom(t_type, b_type),
        problem.atoms.intern_atom(u_type, b_type),
    ];

    assert_eq!(
        solve_conjunction(&atoms, &Input::fixture(&problem)),
        TheoryResult::Unsatisfiable
    );
}

#[test]
fn search_backtracks_after_a_lower_intersection_failure() {
    let Fixture {
        mut problem,
        a,
        b,
        t,
        u,
    } = fixture("class a; class b;");
    let a_type = problem
        .types
        .intern_type(TypeNode::Class(ClassType::plain(a)));
    let b_type = problem
        .types
        .intern_type(TypeNode::Class(ClassType::plain(b)));
    let t_type = problem.types.intern_type(TypeNode::Flexible(t));
    let u_type = problem.types.intern_type(TypeNode::Flexible(u));
    let upper_union = problem.types.intern_union(vec![t_type, u_type]);
    let lower_intersection = problem.types.intern_intersection(vec![t_type, a_type]);
    let atoms = [
        problem.atoms.intern_atom(a_type, upper_union),
        problem.atoms.intern_atom(lower_intersection, b_type),
    ];
    let TheoryResult::Satisfiable(solution) = solve_conjunction(&atoms, &Input::fixture(&problem))
    else {
        panic!("expected search to move the update to U");
    };
    let assignments = solution.into_assignments();

    assert!(assignment_arms(&assignments, t).is_empty());
    assert_eq!(assignment_arms(&assignments, u), [[a]]);
}

#[test]
fn false_upper_intersection_combines_child_updates() {
    let Fixture {
        mut problem,
        a,
        t,
        u,
        ..
    } = fixture("class a; class b;");
    let v = problem.declare_metavar("V");
    let a_type = problem
        .types
        .intern_type(TypeNode::Class(ClassType::plain(a)));
    let t_type = problem.types.intern_type(TypeNode::Flexible(t));
    let u_type = problem.types.intern_type(TypeNode::Flexible(u));
    let v_type = problem.types.intern_type(TypeNode::Flexible(v));
    let intersection = problem.types.intern_intersection(vec![t_type, u_type]);
    let upper = problem.types.intern_union(vec![intersection, v_type]);
    let atoms = [problem.atoms.intern_atom(a_type, upper)];
    let TheoryResult::Satisfiable(solution) = solve_conjunction(&atoms, &Input::fixture(&problem))
    else {
        panic!("expected combined intersection update to satisfy");
    };
    let assignments = solution.into_assignments();

    assert_eq!(assignment_arms(&assignments, t), [[a]]);
    assert_eq!(assignment_arms(&assignments, u), [[a]]);
    assert!(assignment_arms(&assignments, v).is_empty());
}

#[test]
fn ground_union_uses_open_world_dnf_semantics() {
    let Fixture {
        mut problem, a, b, ..
    } = fixture("class a; class b;");
    let a_type = problem
        .types
        .intern_type(TypeNode::Class(ClassType::plain(a)));
    let b_type = problem
        .types
        .intern_type(TypeNode::Class(ClassType::plain(b)));
    let union = problem.types.intern_union(vec![a_type, b_type]);
    let object = problem.types.intern_class(ClassId::OBJECT, Vec::new());
    let sat = [problem.atoms.intern_atom(a_type, union)];
    let unsat = [problem.atoms.intern_atom(object, union)];

    assert!(matches!(
        solve_conjunction(&sat, &Input::fixture(&problem)),
        TheoryResult::Satisfiable(_)
    ));
    assert_eq!(
        solve_conjunction(&unsat, &Input::fixture(&problem)),
        TheoryResult::Unsatisfiable
    );
}

#[test]
fn independent_components_use_one_assignment_shape() {
    let Fixture {
        mut problem,
        a,
        b,
        t,
        u,
    } = fixture("class a; class b;");
    let v = problem.declare_metavar("V");
    let a_type = problem
        .types
        .intern_type(TypeNode::Class(ClassType::plain(a)));
    let b_type = problem
        .types
        .intern_type(TypeNode::Class(ClassType::plain(b)));
    let t_type = problem.types.intern_type(TypeNode::Flexible(t));
    let u_type = problem.types.intern_type(TypeNode::Flexible(u));
    let v_type = problem.types.intern_type(TypeNode::Flexible(v));
    let union = problem.types.intern_union(vec![t_type, u_type]);
    let atoms = [
        problem.atoms.intern_atom(a_type, union),
        problem.atoms.intern_atom(b_type, v_type),
    ];
    let TheoryResult::Satisfiable(solution) = solve_conjunction(&atoms, &Input::fixture(&problem))
    else {
        panic!("expected independent components to satisfy");
    };
    let assignments = solution.into_assignments();

    assert_eq!(assignment_arms(&assignments, t), [[a]]);
    assert!(assignment_arms(&assignments, u).is_empty());
    assert_eq!(assignment_arms(&assignments, v), [[b]]);
}

#[test]
fn lower_arms_can_choose_different_upper_union_members() {
    let Fixture {
        mut problem,
        a,
        b,
        t,
        ..
    } = fixture("class a; class b;");
    let a_type = problem
        .types
        .intern_type(TypeNode::Class(ClassType::plain(a)));
    let b_type = problem
        .types
        .intern_type(TypeNode::Class(ClassType::plain(b)));
    let t_type = problem.types.intern_type(TypeNode::Flexible(t));
    let upper = problem.types.intern_union(vec![a_type, b_type]);
    let atoms = [
        problem.atoms.intern_atom(a_type, t_type),
        problem.atoms.intern_atom(b_type, t_type),
        problem.atoms.intern_atom(t_type, upper),
    ];
    let TheoryResult::Satisfiable(solution) = solve_conjunction(&atoms, &Input::fixture(&problem))
    else {
        panic!("expected separate lower arms to use separate union members");
    };
    let assignments = solution.into_assignments();

    assert_eq!(assignment_arms(&assignments, t), [vec![a], vec![b]]);
}

#[test]
fn active_never_is_distinct_from_inactive_unconstrained() {
    let Fixture {
        mut problem,
        a,
        t,
        u,
        ..
    } = fixture("class a; class b;");
    let atoms = [atom_id(
        &mut problem,
        TypeNode::Flexible(t),
        TypeNode::Class(ClassType::plain(a)),
    )];
    let TheoryResult::Satisfiable(solution) = solve_conjunction(&atoms, &Input::fixture(&problem))
    else {
        panic!("expected an upper-only assignment to satisfy through never");
    };
    let assignments = solution.into_assignments();

    assert!(assignment_arms(&assignments, t).is_empty());
    assert!(!assignments.contains_key(&u));
}

#[test]
fn class_transfers_use_canonical_atom_submission() {
    let file = validate_ok(include_str!(
        "../../../tests/data/solve/sat/generic_class_shared.input"
    ));
    let atoms = file
        .assertions()
        .iter()
        .flat_map(|assertion| &assertion.units)
        .map(|unit| {
            let AtomFormula::Atom(atom) = &unit.formula else {
                panic!("the fixture contains only atomic assertions");
            };
            *atom
        })
        .collect::<Vec<_>>();
    let expected = solve_conjunction(&atoms, &Input::new(&file));
    assert!(matches!(&expected, TheoryResult::Satisfiable(_)));
    let submitted = [atoms[2], atoms[0], atoms[1], atoms[0], atoms[2]];
    assert_eq!(solve_conjunction(&submitted, &Input::new(&file)), expected);
}
