//! Tests for type interning, structural order, and generic binder rewriting.

use std::num::NonZeroU32;

use crate::frontend::problem::{Callable, ClassType, Generic};

use std::cmp::Ordering;

use super::normalize::compare_types;
use super::{BoundRef, ClassId, TypeNode};
use crate::frontend::test_support::{RawProblem, lookup_class, lookup_metavar};

#[test]
fn leaf_types_are_interned() {
    let mut problem = RawProblem::new("class a; metavar ?T;");
    let class = lookup_class(&problem.declarations, "a");
    let metavar = lookup_metavar(&problem.declarations, "T");

    let class_type = problem.types.intern_class(class, Vec::new());
    let metavar_type = problem.types.types().metavar_type(metavar);
    assert_eq!(
        problem.types.types().type_node(class_type),
        &TypeNode::Class(ClassType::plain(class))
    );
    assert_eq!(
        problem.types.types().type_node(metavar_type),
        &TypeNode::Flexible(metavar)
    );
    assert_eq!(
        problem
            .types
            .intern_type(TypeNode::Class(ClassType::plain(class))),
        class_type
    );
    assert_eq!(
        problem.types.intern_type(TypeNode::Flexible(metavar)),
        metavar_type
    );
    assert_ne!(class_type, metavar_type);
}

#[test]
fn tuples_intern_exact_elements_and_order() {
    let mut problem = RawProblem::new("class a; metavar ?T;");
    let class = lookup_class(&problem.declarations, "a");
    let metavar = lookup_metavar(&problem.declarations, "T");
    let class_type = problem.types.intern_class(class, Vec::new());
    let metavar_type = problem.types.types().metavar_type(metavar);

    let tuple = problem.types.intern_tuple(vec![metavar_type, class_type]);
    assert_eq!(
        problem.types.types().type_node(tuple),
        &TypeNode::Tuple(vec![metavar_type, class_type])
    );
    assert_eq!(
        problem.types.intern_tuple(vec![metavar_type, class_type]),
        tuple,
        "equal tuples share one type identifier"
    );
    assert_ne!(
        problem.types.intern_tuple(vec![class_type, metavar_type]),
        tuple
    );
    assert_ne!(problem.types.intern_tuple(Vec::new()), tuple);
}

#[test]
fn callables_intern_exact_parameters_and_return() {
    let mut problem = RawProblem::new("class a; metavar ?T;");
    let class = lookup_class(&problem.declarations, "a");
    let metavar = lookup_metavar(&problem.declarations, "T");
    let class_type = problem.types.intern_class(class, Vec::new());
    let metavar_type = problem.types.types().metavar_type(metavar);

    let callable = problem
        .types
        .intern_callable(vec![metavar_type, class_type], class_type);
    assert_eq!(
        problem.types.types().type_node(callable),
        &TypeNode::Callable(Callable {
            params: vec![metavar_type, class_type],
            ret: class_type,
        })
    );
    assert_eq!(
        problem
            .types
            .intern_callable(vec![metavar_type, class_type], class_type),
        callable,
        "equal callables share one type identifier"
    );
    assert_ne!(
        problem
            .types
            .intern_callable(vec![class_type, metavar_type], class_type),
        callable
    );
    assert_ne!(
        problem
            .types
            .intern_callable(vec![metavar_type, class_type], metavar_type),
        callable
    );
}

#[test]
fn type_order_places_callables_between_tuples_and_unions() {
    let mut problem = RawProblem::new("class a; metavar ?T;");
    let class = lookup_class(&problem.declarations, "a");
    let metavar = lookup_metavar(&problem.declarations, "T");
    let class_type = problem.types.intern_class(class, Vec::new());
    let metavar_type = problem.types.types().metavar_type(metavar);
    let tuple = problem.types.intern_tuple(vec![class_type]);
    let tuple_metavar = problem.types.intern_tuple(vec![metavar_type]);
    let tuple_longer = problem.types.intern_tuple(vec![class_type, metavar_type]);
    let callable = problem.types.intern_callable(vec![class_type], class_type);
    let callable_param = problem
        .types
        .intern_callable(vec![metavar_type], class_type);
    let callable_longer = problem
        .types
        .intern_callable(vec![class_type, metavar_type], class_type);
    let callable_return = problem
        .types
        .intern_callable(vec![class_type], metavar_type);
    let union = problem.types.intern_union(vec![class_type, metavar_type]);
    let intersection = problem
        .types
        .intern_intersection(vec![class_type, metavar_type]);

    for (lower, upper) in [
        (class_type, metavar_type),
        (metavar_type, tuple),
        (tuple, callable),
        (callable, union),
        (union, intersection),
    ] {
        assert_eq!(
            compare_types(problem.types.types(), lower, upper),
            Ordering::Less
        );
        assert_eq!(
            compare_types(problem.types.types(), upper, lower),
            Ordering::Greater
        );
    }
    assert_eq!(
        compare_types(problem.types.types(), tuple, tuple_metavar),
        Ordering::Less
    );
    assert_eq!(
        compare_types(problem.types.types(), tuple, tuple_longer),
        Ordering::Less
    );
    assert_eq!(
        compare_types(problem.types.types(), callable, callable_param),
        Ordering::Less
    );
    assert_eq!(
        compare_types(problem.types.types(), callable, callable_longer),
        Ordering::Less
    );
    assert_eq!(
        compare_types(problem.types.types(), callable, callable_return),
        Ordering::Less
    );
}

#[test]
fn unions_flatten_sort_deduplicate_and_apply_bounds() {
    let mut problem = RawProblem::new("class a; metavar ?T;");
    let metavar = lookup_metavar(&problem.declarations, "T");
    let class = lookup_class(&problem.declarations, "a");
    let class_type = problem.types.intern_class(class, Vec::new());
    let metavar_type = problem.types.types().metavar_type(metavar);
    let never = problem.types.intern_class(ClassId::NEVER, Vec::new());
    let object = problem.types.intern_class(ClassId::OBJECT, Vec::new());

    let union = problem
        .types
        .intern_union(vec![metavar_type, never, class_type, class_type]);
    assert_eq!(
        problem.types.types().type_node(union),
        &TypeNode::Union(vec![class_type, metavar_type])
    );
    assert_eq!(
        problem.types.intern_union(vec![union, class_type]),
        union,
        "nested unions flatten before interning"
    );
    assert_eq!(
        problem.types.intern_union(vec![never, class_type]),
        class_type
    );
    assert_eq!(problem.types.intern_union(vec![union, object]), object);
    assert_eq!(problem.types.intern_union(Vec::new()), never);
}

#[test]
fn intersections_flatten_sort_deduplicate_and_apply_bounds() {
    let mut problem = RawProblem::new("class a; metavar ?T;");
    let metavar = lookup_metavar(&problem.declarations, "T");
    let class = lookup_class(&problem.declarations, "a");
    let class_type = problem.types.intern_class(class, Vec::new());
    let metavar_type = problem.types.types().metavar_type(metavar);
    let never = problem.types.intern_class(ClassId::NEVER, Vec::new());
    let object = problem.types.intern_class(ClassId::OBJECT, Vec::new());

    let intersection =
        problem
            .types
            .intern_intersection(vec![metavar_type, object, class_type, class_type]);
    assert_eq!(
        problem.types.types().type_node(intersection),
        &TypeNode::Intersection(vec![class_type, metavar_type])
    );
    assert_eq!(
        problem
            .types
            .intern_intersection(vec![intersection, class_type]),
        intersection,
        "nested intersections flatten before interning"
    );
    assert_eq!(
        problem.types.intern_intersection(vec![object, class_type]),
        class_type
    );
    assert_eq!(
        problem.types.intern_intersection(vec![intersection, never]),
        never
    );
    assert_eq!(problem.types.intern_intersection(Vec::new()), object);
}

#[test]
fn generic_parameters_use_relative_ordered_positions() {
    let Some(parameters) = NonZeroU32::new(2) else {
        panic!("fixture binder has two parameters");
    };
    let mut problem = RawProblem::new("class a; metavar ?T;");
    let first = problem.types.intern_bound(BoundRef::new(0, 0));
    let second = problem.types.intern_bound(BoundRef::new(0, 1));
    let body = Callable {
        params: vec![first, second],
        ret: first,
    };
    let generic = problem.types.intern_generic(2, &body);

    let role_changed_body = Callable {
        params: vec![second, first],
        ret: second,
    };
    assert_ne!(problem.types.intern_generic(2, &role_changed_body), generic);
    assert_eq!(
        problem.types.types().type_node(generic),
        &TypeNode::Generic(Generic { parameters, body })
    );
}

#[test]
fn sparse_live_parameters_match_a_renamed_dense_binder() {
    let mut problem = RawProblem::new("class a; metavar ?T;");
    let sparse_first = problem.types.intern_bound(BoundRef::new(0, 2));
    let sparse_second = problem.types.intern_bound(BoundRef::new(0, 5));
    let sparse_union = problem
        .types
        .intern_union(vec![sparse_first, sparse_second]);
    let sparse_return = problem
        .types
        .intern_tuple(vec![sparse_first, sparse_second]);
    let sparse = problem.types.intern_generic(
        6,
        &Callable {
            params: vec![sparse_union],
            ret: sparse_return,
        },
    );

    let first = problem.types.intern_bound(BoundRef::new(0, 0));
    let second = problem.types.intern_bound(BoundRef::new(0, 1));
    let dense_union = problem.types.intern_union(vec![first, second]);
    let dense_return = problem.types.intern_tuple(vec![first, second]);
    let dense = problem.types.intern_generic(
        2,
        &Callable {
            params: vec![dense_union],
            ret: dense_return,
        },
    );
    assert_eq!(sparse, dense);

    let reversed_return = problem.types.intern_tuple(vec![second, first]);
    let role_changed = problem.types.intern_generic(
        2,
        &Callable {
            params: vec![dense_union],
            ret: reversed_return,
        },
    );
    assert_ne!(sparse, role_changed);

    let TypeNode::Generic(generic) = problem.types.types().type_node(sparse) else {
        panic!("two live parameters must retain the binder");
    };
    assert_eq!(generic.parameters.get(), 2);
    assert_eq!(
        problem.types.types().type_node(generic.body.ret),
        &TypeNode::Tuple(vec![first, second])
    );
}

#[test]
fn generic_normalization_removes_dead_binders() {
    let mut problem = RawProblem::new("class a; metavar ?T;");
    let object = problem.types.intern_class(ClassId::OBJECT, Vec::new());
    let live = problem.types.intern_bound(BoundRef::new(0, 1));
    let body = Callable {
        params: vec![object],
        ret: live,
    };
    let generic = problem.types.intern_generic(2, &body);
    let canonical = problem.types.intern_bound(BoundRef::new(0, 0));
    let canonical_body = Callable {
        params: vec![object],
        ret: canonical,
    };
    assert_eq!(
        problem.types.types().type_node(generic),
        &TypeNode::Generic(Generic {
            parameters: NonZeroU32::MIN,
            body: canonical_body,
        })
    );

    let monomorphic = Callable {
        params: vec![object],
        ret: object,
    };
    let expected = problem.types.intern_callable(vec![object], object);
    assert_eq!(problem.types.intern_generic(1, &monomorphic), expected);
}

#[test]
fn removing_a_binder_shifts_outer_references() {
    let mut problem = RawProblem::new("class a; metavar ?T;");
    let outer = problem.types.intern_bound(BoundRef::new(1, 0));
    let body = Callable {
        params: Vec::new(),
        ret: outer,
    };
    let normalized = problem.types.intern_generic(1, &body);
    let shifted = problem.types.intern_bound(BoundRef::new(0, 0));
    assert_eq!(
        normalized,
        problem.types.intern_callable(Vec::new(), shifted)
    );
}
