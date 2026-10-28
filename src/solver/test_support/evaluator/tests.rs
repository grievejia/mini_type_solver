//! Invalid cycles and bindings cannot enter the independent comparison.

use crate::frontend::problem::Callable;

use super::{Graph, Type};

#[test]
fn independent_graph_rejects_missing_nodes_unguarded_cycles_and_free_parameters() {
    for kind in [
        Type::Reference(1),
        Type::Reference(0),
        Type::Bound {
            owner: 0,
            position: 0,
        },
    ] {
        assert!(Graph::checked("class A; class B;", &[(kind, Vec::new())], &[0]).is_none());
    }
}

#[test]
fn independent_comparison_accepts_guarded_tuples_and_rejects_wrong_lengths() {
    let mut graph = Graph::checked(
        "class A; class B;",
        &[
            (Type::Tuple(vec![0]), vec![]),
            (Type::Tuple(vec![2]), vec![]),
            (Type::Tuple(vec![1]), vec![]),
            (Type::Tuple(vec![3, 3]), vec![]),
        ],
        &[0, 1, 3],
    )
    .expect("every type cycle contains a tuple");
    assert!(graph.is_subtype(0, 1));
    assert!(graph.is_subtype(1, 0));
    assert!(!graph.is_subtype(0, 3));
}

#[test]
fn superclass_templates_preserve_scope_when_the_first_argument_is_closed() {
    let nodes = [
        (
            Type::Generic {
                parameters: 1,
                body: Callable {
                    params: vec![1],
                    ret: 2,
                },
            },
            vec![],
        ),
        (
            Type::Class {
                class: 4,
                arguments: vec![3, 4],
            },
            vec![0],
        ),
        (
            Type::Class {
                class: 3,
                arguments: vec![5],
            },
            vec![0],
        ),
        (
            Type::Class {
                class: 2,
                arguments: vec![],
            },
            vec![],
        ),
        (
            Type::Bound {
                owner: 0,
                position: 0,
            },
            vec![0],
        ),
        (Type::Tuple(vec![3, 4]), vec![0]),
    ];
    let mut graph = Graph::checked(
        "class A; class Parent[T]; class Child[First, Second] extends Parent[tuple[First, Second]];",
        &nodes,
        &[0],
    )
    .expect("the generic body owns the second class argument");
    assert!(graph.is_subtype(1, 2));
    assert!(graph.valid(&[0]));
}

#[test]
fn independent_comparison_reverses_recursive_function_parameters() {
    let mut graph = Graph::checked(
        "class A; class B extends A;",
        &[
            (
                Type::Callable(Callable {
                    params: vec![1],
                    ret: 2,
                }),
                vec![],
            ),
            (
                Type::Callable(Callable {
                    params: vec![0],
                    ret: 3,
                }),
                vec![],
            ),
            (
                Type::Class {
                    class: 3,
                    arguments: Vec::new(),
                },
                vec![],
            ),
            (
                Type::Class {
                    class: 2,
                    arguments: Vec::new(),
                },
                vec![],
            ),
        ],
        &[0, 1],
    )
    .expect("the alternating functions have guarded cycles");
    assert!(graph.is_subtype(0, 1));
    assert!(!graph.is_subtype(1, 0));
}

#[test]
fn unused_binder_positions_do_not_leave_invalid_unreachable_references() {
    let nodes = [
        (
            Type::Generic {
                parameters: 2,
                body: Callable {
                    params: vec![1],
                    ret: 2,
                },
            },
            vec![],
        ),
        (
            Type::Bound {
                owner: 0,
                position: 1,
            },
            vec![0],
        ),
        (Type::Tuple(vec![2]), vec![0]),
        (
            Type::Bound {
                owner: 0,
                position: 0,
            },
            vec![0],
        ),
    ];
    let graph = Graph::checked("class A; class B;", &nodes, &[0])
        .expect("the unused position has no type edge from the root");
    assert!(graph.valid(&[0]));
}

#[test]
fn independent_comparison_rejects_a_mismatch_outside_a_constructor_loop() {
    let mut graph = Graph::checked(
        "class A; class B;",
        &[
            (Type::Tuple(vec![0, 1]), vec![]),
            (
                Type::Class {
                    class: 2,
                    arguments: Vec::new(),
                },
                vec![],
            ),
            (Type::Tuple(vec![2, 3]), vec![]),
            (
                Type::Class {
                    class: 3,
                    arguments: Vec::new(),
                },
                vec![],
            ),
        ],
        &[0, 2],
    )
    .expect("the tuple loops are guarded");
    assert!(!graph.is_subtype(0, 2));
    assert!(!graph.is_subtype(2, 0));
}

#[test]
fn independent_generic_comparison_requires_the_same_function_arity() {
    let mut graph = Graph::checked(
        "class A; class B;",
        &[
            (
                Type::Generic {
                    parameters: 1,
                    body: Callable {
                        params: vec![1],
                        ret: 1,
                    },
                },
                vec![],
            ),
            (
                Type::Bound {
                    owner: 0,
                    position: 0,
                },
                vec![0],
            ),
            (
                Type::Generic {
                    parameters: 1,
                    body: Callable {
                        params: vec![3, 3],
                        ret: 3,
                    },
                },
                vec![],
            ),
            (
                Type::Bound {
                    owner: 2,
                    position: 0,
                },
                vec![2],
            ),
        ],
        &[0, 2],
    )
    .expect("each generic owns its parameter");
    assert!(!graph.is_subtype(0, 2));
    assert!(!graph.is_subtype(2, 0));
}

#[test]
fn independent_generic_comparison_keeps_outer_and_inner_parameter_owners() {
    let mut nodes = Vec::new();
    for reverse in [false, true] {
        let owner = nodes.len();
        let nested = owner + 1;
        let outer = owner + 3;
        let inner = owner + 4;
        let (parameter, ret) = if reverse {
            (inner, outer)
        } else {
            (outer, inner)
        };
        nodes.extend([
            (
                Type::Generic {
                    parameters: 1,
                    body: Callable {
                        params: vec![nested],
                        ret: owner + 2,
                    },
                },
                vec![],
            ),
            (
                Type::Generic {
                    parameters: 1,
                    body: Callable {
                        params: vec![parameter],
                        ret,
                    },
                },
                vec![owner],
            ),
            (Type::Bound { owner, position: 0 }, vec![owner]),
            (Type::Bound { owner, position: 0 }, vec![owner, nested]),
            (
                Type::Bound {
                    owner: nested,
                    position: 0,
                },
                vec![owner, nested],
            ),
        ]);
    }
    let mut graph = Graph::checked("class A; class B;", &nodes, &[0, 5])
        .expect("both the outer and inner parameters remain in use");
    // The types are forall X. (forall Y. (X) -> Y) -> X and
    // forall X. (forall Y. (Y) -> X) -> X. Renaming cannot swap their owners.
    assert!(!graph.is_subtype(0, 5));
    assert!(!graph.is_subtype(5, 0));
}
