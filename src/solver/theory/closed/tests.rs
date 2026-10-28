//! Closed definitions must depend on type structure and saved parameter bindings.

use std::cmp::Ordering;

use crate::frontend::problem::{Callable, ClassType};
use crate::frontend::test_support::{RawProblem, lookup_class};
use crate::solver::input::Input;
use crate::solver::test_support::{Type as IndependentType, direct_query};

use super::super::ClassRelation;
use super::{Description, Value, ValueNode, construct, is_subtype};

fn values(description: &[Description], roots: &[usize]) -> Vec<Value> {
    let problem = RawProblem::new("class A; class B; class Box[T];");
    let nodes = description
        .iter()
        .cloned()
        .map(|kind| (kind, Vec::new()))
        .collect::<Vec<_>>();
    construct(&problem.declarations, &nodes, roots)
}

fn independent(description: &[(Description, Vec<usize>)]) -> Vec<(IndependentType, Vec<usize>)> {
    description
        .iter()
        .map(|(kind, scope)| {
            let kind = match kind {
                Description::Never => IndependentType::Never,
                Description::Class(class) => IndependentType::Class {
                    class: class.class.index(),
                    arguments: class.arguments.clone(),
                },
                Description::Tuple(children) => IndependentType::Tuple(children.clone()),
                Description::Callable(body) => IndependentType::Callable(body.clone()),
                Description::Generic { parameters, body } => IndependentType::Generic {
                    parameters: *parameters as usize,
                    body: body.clone(),
                },
                Description::Bound { owner, position } => IndependentType::Bound {
                    owner: *owner,
                    position: *position as usize,
                },
                Description::Reference(target) => IndependentType::Reference(*target),
                Description::Union(children) => IndependentType::Union(children.clone()),
                Description::Intersection(children) => {
                    IndependentType::Intersection(children.clone())
                }
            };
            (kind, scope.clone())
        })
        .collect()
}

fn compare(
    declarations: &str,
    description: &[(Description, Vec<usize>)],
    lower: usize,
    upper: usize,
    expected: bool,
) {
    let problem = RawProblem::new(declarations);
    let values = construct(&problem.declarations, description, &[lower, upper]);
    let input = Input::fixture(&problem);
    let relation = ClassRelation::new(&input);
    assert_eq!(is_subtype(&values[0], &values[1], &relation), expected);
    assert_eq!(
        direct_query(declarations, &independent(description), lower, upper),
        Some(expected)
    );
}

fn offset(
    description: &[(Description, Vec<usize>)],
    offset: usize,
) -> Vec<(Description, Vec<usize>)> {
    description
        .iter()
        .map(|(kind, scope)| {
            let children =
                |children: &[usize]| children.iter().map(|child| child + offset).collect();
            let kind = match kind {
                Description::Never => Description::Never,
                Description::Class(class) => Description::Class(class.map(|child| child + offset)),
                Description::Tuple(nodes) => Description::Tuple(children(nodes)),
                Description::Callable(body) => {
                    Description::Callable(body.map(|child| child + offset))
                }
                Description::Generic { parameters, body } => Description::Generic {
                    parameters: *parameters,
                    body: body.map(|child| child + offset),
                },
                Description::Bound { owner, position } => Description::Bound {
                    owner: owner + offset,
                    position: *position,
                },
                Description::Reference(target) => Description::Reference(target + offset),
                Description::Union(nodes) => Description::Union(children(nodes)),
                Description::Intersection(nodes) => Description::Intersection(children(nodes)),
            };
            (kind, children(scope))
        })
        .collect()
}

fn equivalent(
    declarations: &str,
    left: &[(Description, Vec<usize>)],
    right: &[(Description, Vec<usize>)],
) {
    let problem = RawProblem::new(declarations);
    let first = construct(&problem.declarations, left, &[0]);
    let second = construct(&problem.declarations, right, &[0]);
    assert_eq!(first, second);
    assert_eq!(first[0].cmp(&second[0]), Ordering::Equal);
    let mut both = left.to_vec();
    both.extend(offset(right, left.len()));
    assert_eq!(
        direct_query(declarations, &independent(&both), 0, left.len()),
        Some(true)
    );
    assert_eq!(
        direct_query(declarations, &independent(&both), left.len(), 0),
        Some(true)
    );
}

fn bound_positions(values: &[Value], owner: &Value) -> Vec<u32> {
    values
        .iter()
        .map(|value| {
            let ValueNode::Bound {
                owner: bound_owner,
                position,
                ..
            } = value.node()
            else {
                panic!("the parameter tuple contains only bound references");
            };
            assert!(owner.same_binding(&bound_owner));
            position
        })
        .collect()
}

#[test]
fn recursive_tuple_identity_ignores_unfolding_and_unused_nodes() {
    let one = values(&[Description::Tuple(vec![0])], &[0]);
    let two = values(
        &[
            Description::Never,
            Description::Tuple(vec![2]),
            Description::Tuple(vec![1]),
        ],
        &[1],
    );
    assert_eq!(one[0], two[0]);
    assert_eq!(one[0].cmp(&two[0]), Ordering::Equal);
    assert!(one[0].is_recursive());
}

#[test]
fn merged_recursive_factors_remove_single_child_lattice_nodes() {
    let one = values(&[Description::Tuple(vec![0])], &[0]);
    let union = values(
        &[
            Description::Union(vec![2, 3]),
            Description::Union(vec![2, 3]),
            Description::Tuple(vec![0]),
            Description::Tuple(vec![1]),
        ],
        &[0, 1],
    );
    assert_eq!(one[0], union[0]);
    assert_eq!(union[0], union[1]);
    let intersection = values(
        &[
            Description::Intersection(vec![1, 2]),
            Description::Tuple(vec![0]),
            Description::Intersection(vec![3]),
            Description::Tuple(vec![0]),
        ],
        &[0],
    );
    assert_eq!(one[0], intersection[0]);
}

#[test]
fn lattice_operations_stop_at_whole_recursive_constructors() {
    let problem = RawProblem::new("class A; class B; class Box[T];");
    let a = lookup_class(&problem.declarations, "A");
    let b = lookup_class(&problem.declarations, "B");
    let result = values(
        &[
            Description::Union(vec![1, 2]),
            Description::Class(ClassType::plain(a)),
            Description::Tuple(vec![0]),
            Description::Class(ClassType::plain(b)),
            Description::Union(vec![0, 3]),
            Description::Union(vec![1, 3, 2]),
            Description::Intersection(vec![0, 3]),
            Description::Intersection(vec![1, 3]),
            Description::Intersection(vec![2, 3]),
            Description::Union(vec![7, 8]),
        ],
        &[4, 5, 6, 9],
    );
    assert_eq!(result[0], result[1]);
    assert_eq!(result[2], result[3]);
    assert!(matches!(result[2].node(), ValueNode::Intersection(children) if children.len() == 2));
}

#[test]
#[should_panic(expected = "closed graph references a missing node")]
fn missing_references_are_programming_errors() {
    let problem = RawProblem::new("");
    construct(
        &problem.declarations,
        &[(Description::Reference(1), vec![])],
        &[0],
    );
}

#[test]
#[should_panic(expected = "closed graph contains an unguarded cycle")]
fn unguarded_cycles_are_programming_errors() {
    let problem = RawProblem::new("");
    construct(
        &problem.declarations,
        &[(Description::Reference(0), vec![])],
        &[0],
    );
}

#[test]
#[should_panic(expected = "closed graph parameter has no visible binder")]
fn invalid_parameter_bindings_are_programming_errors() {
    let problem = RawProblem::new("");
    construct(
        &problem.declarations,
        &[(
            Description::Bound {
                owner: 0,
                position: 0,
            },
            vec![],
        )],
        &[0],
    );
}

#[test]
fn recursive_generic_identity_keeps_parameter_positions() {
    let problem = RawProblem::new("");
    let mut nodes = vec![
        (
            Description::Generic {
                parameters: 2,
                body: Callable {
                    params: vec![1],
                    ret: 4,
                },
            },
            vec![],
        ),
        (Description::Tuple(vec![2, 3]), vec![0]),
        (
            Description::Bound {
                owner: 0,
                position: 0,
            },
            vec![0],
        ),
        (
            Description::Bound {
                owner: 0,
                position: 1,
            },
            vec![0],
        ),
        (Description::Reference(0), vec![0]),
    ];
    let first = construct(&problem.declarations, &nodes, &[0]);
    let mut remapped = nodes.clone();
    remapped.swap(2, 3);
    remapped[1].0 = Description::Tuple(vec![3, 2]);
    equivalent("", &nodes, &remapped);
    nodes[2].0 = Description::Bound {
        owner: 0,
        position: 1,
    };
    nodes[3].0 = Description::Bound {
        owner: 0,
        position: 0,
    };
    let second = construct(&problem.declarations, &nodes, &[0]);
    assert_ne!(first, second);
}

#[test]
fn unused_recursive_parameters_are_removed_and_positions_are_dense() {
    let problem = RawProblem::new("");
    let result = construct(
        &problem.declarations,
        &[
            (
                Description::Generic {
                    parameters: 2,
                    body: Callable {
                        params: vec![1, 2],
                        ret: 3,
                    },
                },
                vec![],
            ),
            (Description::Never, vec![0]),
            (
                Description::Bound {
                    owner: 0,
                    position: 1,
                },
                vec![0],
            ),
            (Description::Reference(0), vec![0]),
        ],
        &[0],
    );
    let ValueNode::Generic { parameters, body } = result[0].node() else {
        panic!("one parameter remains");
    };
    assert_eq!(parameters, 1);
    assert!(matches!(
        body.params[1].node(),
        ValueNode::Bound { position: 0, .. }
    ));
    let monomorphic = construct(
        &problem.declarations,
        &[
            (
                Description::Generic {
                    parameters: 1,
                    body: Callable {
                        params: vec![1],
                        ret: 2,
                    },
                },
                vec![],
            ),
            (Description::Never, vec![0]),
            (Description::Reference(0), vec![0]),
        ],
        &[0],
    );
    assert!(matches!(monomorphic[0].node(), ValueNode::Callable(_)));
}

#[test]
fn both_queries_check_guarded_tuple_and_function_comparisons() {
    compare(
        "",
        &[
            (Description::Tuple(vec![0]), vec![]),
            (Description::Tuple(vec![2]), vec![]),
            (Description::Tuple(vec![1]), vec![]),
            (Description::Tuple(vec![3, 3]), vec![]),
        ],
        0,
        1,
        true,
    );
    compare(
        "",
        &[
            (Description::Tuple(vec![0]), vec![]),
            (Description::Tuple(vec![1, 1]), vec![]),
        ],
        0,
        1,
        false,
    );
    let source = "class Animal; class Dog extends Animal;";
    let problem = RawProblem::new(source);
    let dog = lookup_class(&problem.declarations, "Dog");
    let animal = lookup_class(&problem.declarations, "Animal");
    let description = [
        (
            Description::Callable(Callable {
                params: vec![1],
                ret: 2,
            }),
            vec![],
        ),
        (
            Description::Callable(Callable {
                params: vec![0],
                ret: 3,
            }),
            vec![],
        ),
        (Description::Class(ClassType::plain(dog)), vec![]),
        (Description::Class(ClassType::plain(animal)), vec![]),
    ];
    compare(source, &description, 0, 1, true);
    compare(source, &description, 1, 0, false);
}

#[test]
fn superclass_steps_outside_a_tuple_cycle_do_not_reject_it() {
    let source = "class Animal; class Dog extends Animal; class Base[+T]; class Derived[+T] extends Base[T];";
    let problem = RawProblem::new(source);
    let derived = lookup_class(&problem.declarations, "Derived");
    let base = lookup_class(&problem.declarations, "Base");
    let dog = lookup_class(&problem.declarations, "Dog");
    let animal = lookup_class(&problem.declarations, "Animal");
    let nodes = [
        (
            Description::Class(ClassType {
                class: derived,
                arguments: vec![2],
            }),
            vec![],
        ),
        (
            Description::Class(ClassType {
                class: base,
                arguments: vec![3],
            }),
            vec![],
        ),
        (Description::Tuple(vec![2, 4]), vec![]),
        (Description::Tuple(vec![3, 5]), vec![]),
        (Description::Class(ClassType::plain(dog)), vec![]),
        (Description::Class(ClassType::plain(animal)), vec![]),
    ];
    compare(source, &nodes, 0, 1, true);
}

#[test]
fn a_superclass_step_inside_a_repeated_comparison_rejects_it() {
    let source = "class Base[+T]; class Derived[+T] extends Base[T];";
    let problem = RawProblem::new(source);
    let base = lookup_class(&problem.declarations, "Base");
    let derived = lookup_class(&problem.declarations, "Derived");
    compare(
        source,
        &[
            (
                Description::Class(ClassType {
                    class: derived,
                    arguments: vec![0],
                }),
                vec![],
            ),
            (
                Description::Class(ClassType {
                    class: base,
                    arguments: vec![1],
                }),
                vec![],
            ),
        ],
        0,
        1,
        false,
    );
}

#[test]
fn finite_inner_binder_keeps_outer_references_in_a_recursive_type() {
    let problem = RawProblem::new("class A;");
    let a = lookup_class(&problem.declarations, "A");
    let nodes = [
        (
            Description::Generic {
                parameters: 2,
                body: Callable {
                    params: vec![1],
                    ret: 8,
                },
            },
            vec![],
        ),
        (
            Description::Generic {
                parameters: 3,
                body: Callable {
                    params: vec![2],
                    ret: 9,
                },
            },
            vec![0],
        ),
        (Description::Tuple(vec![3, 4, 5, 6, 7]), vec![0, 1]),
        (
            Description::Bound {
                owner: 0,
                position: 0,
            },
            vec![0, 1],
        ),
        (
            Description::Bound {
                owner: 0,
                position: 1,
            },
            vec![0, 1],
        ),
        (
            Description::Bound {
                owner: 1,
                position: 0,
            },
            vec![0, 1],
        ),
        (
            Description::Bound {
                owner: 1,
                position: 1,
            },
            vec![0, 1],
        ),
        (
            Description::Bound {
                owner: 1,
                position: 2,
            },
            vec![0, 1],
        ),
        (Description::Reference(0), vec![0]),
        (Description::Class(ClassType::plain(a)), vec![0, 1]),
    ];
    let values = construct(&problem.declarations, &nodes, &[0]);
    let outer = values[0].clone();
    let ValueNode::Generic {
        body: outer_body, ..
    } = values[0].node()
    else {
        panic!("the recursive outer binder remains");
    };
    let inner = outer_body.params[0].clone();
    let ValueNode::Generic {
        body: inner_body, ..
    } = outer_body.params[0].node()
    else {
        panic!("the finite inner binder remains");
    };
    let ValueNode::Tuple(parts) = inner_body.params[0].node() else {
        panic!("the inner parameter contains both binders' positions");
    };
    assert_eq!(bound_positions(&parts[..2], &outer), [0, 1]);
    assert_eq!(bound_positions(&parts[2..], &inner), [0, 1, 2]);
    assert!(!outer.same_binding(&inner));
    assert!(outer_body.ret.same_binding(&outer));
    assert_eq!(
        direct_query("class A;", &independent(&nodes), 0, 0),
        Some(true)
    );
}

#[test]
fn generic_with_a_recursive_return_keeps_parameter_positions() {
    let problem = RawProblem::new("");
    let nodes = [
        (
            Description::Generic {
                parameters: 2,
                body: Callable {
                    params: vec![1],
                    ret: 4,
                },
            },
            vec![],
        ),
        (Description::Tuple(vec![2, 3]), vec![0]),
        (
            Description::Bound {
                owner: 0,
                position: 0,
            },
            vec![0],
        ),
        (
            Description::Bound {
                owner: 0,
                position: 1,
            },
            vec![0],
        ),
        (Description::Tuple(vec![4]), vec![]),
    ];
    let values = construct(&problem.declarations, &nodes, &[0]);
    assert!(!values[0].is_recursive());
    let owner = values[0].clone();
    let ValueNode::Generic { body, .. } = values[0].node() else {
        panic!("both parameters keep the generic binder");
    };
    let ValueNode::Tuple(parts) = body.params[0].node() else {
        panic!("the parameter is the tuple of both bound positions");
    };
    assert_eq!(bound_positions(&parts, &owner), [0, 1]);
    assert!(matches!(body.ret.node(), ValueNode::Tuple(_)));
    assert!(body.ret.is_recursive());
}

#[test]
fn nested_recursive_binders_keep_ordered_positions_and_separate_owners() {
    let problem = RawProblem::new("");
    let mut nodes = vec![
        (
            Description::Generic {
                parameters: 2,
                body: Callable {
                    params: vec![1],
                    ret: 7,
                },
            },
            vec![],
        ),
        (
            Description::Generic {
                parameters: 2,
                body: Callable {
                    params: vec![2],
                    ret: 8,
                },
            },
            vec![0],
        ),
        (Description::Tuple(vec![3, 4, 5, 6]), vec![0, 1]),
    ];
    nodes.extend(
        [(0, 0), (0, 1), (1, 0), (1, 1)]
            .map(|(owner, position)| (Description::Bound { owner, position }, vec![0, 1])),
    );
    nodes.extend([
        (Description::Reference(0), vec![0]),
        (Description::Reference(0), vec![0, 1]),
    ]);
    let values = construct(&problem.declarations, &nodes, &[0]);
    let outer = values[0].clone();
    let ValueNode::Generic {
        body: outer_body, ..
    } = values[0].node()
    else {
        panic!("the outer recursive binder remains");
    };
    let inner = outer_body.params[0].clone();
    let ValueNode::Generic {
        body: inner_body, ..
    } = outer_body.params[0].node()
    else {
        panic!("the inner recursive binder remains");
    };
    let ValueNode::Tuple(parts) = inner_body.params[0].node() else {
        panic!("the inner parameter contains both binders' positions");
    };
    assert_eq!(bound_positions(&parts[..2], &outer), [0, 1]);
    assert_eq!(bound_positions(&parts[2..], &inner), [0, 1]);
    assert!(!outer.same_binding(&inner));
    assert!(outer_body.ret.same_binding(&outer));
    assert!(inner_body.ret.same_binding(&outer));

    for changed_owner in [0, 1] {
        let mut role_changed = nodes.clone();
        for (kind, _) in &mut role_changed {
            if let Description::Bound { owner, position } = kind
                && *owner == changed_owner
            {
                *position = 1 - *position;
            }
        }
        let changed = construct(&problem.declarations, &role_changed, &[0]);
        assert_ne!(values, changed);
    }
    let mut remapped = nodes.clone();
    remapped.swap(3, 4);
    remapped.swap(5, 6);
    remapped[2].0 = Description::Tuple(vec![4, 3, 6, 5]);
    equivalent("", &nodes, &remapped);
}

#[test]
fn removing_an_unused_inner_binder_keeps_the_outer_parameter() {
    let problem = RawProblem::new("class A;");
    let a = lookup_class(&problem.declarations, "A");
    let generic = [
        (
            Description::Generic {
                parameters: 1,
                body: Callable {
                    params: vec![1],
                    ret: 4,
                },
            },
            vec![],
        ),
        (
            Description::Generic {
                parameters: 1,
                body: Callable {
                    params: vec![2],
                    ret: 3,
                },
            },
            vec![0],
        ),
        (
            Description::Bound {
                owner: 0,
                position: 0,
            },
            vec![0, 1],
        ),
        (Description::Class(ClassType::plain(a)), vec![0, 1]),
        (Description::Reference(0), vec![0]),
    ];
    let monomorphic = [
        (
            Description::Generic {
                parameters: 1,
                body: Callable {
                    params: vec![1],
                    ret: 4,
                },
            },
            vec![],
        ),
        (
            Description::Callable(Callable {
                params: vec![2],
                ret: 3,
            }),
            vec![0],
        ),
        (
            Description::Bound {
                owner: 0,
                position: 0,
            },
            vec![0],
        ),
        (Description::Class(ClassType::plain(a)), vec![0]),
        (Description::Reference(0), vec![0]),
    ];
    equivalent("class A;", &generic, &monomorphic);
    let values = construct(&problem.declarations, &generic, &[0]);
    let owner = values[0].clone();
    let ValueNode::Generic { body, .. } = values[0].node() else {
        panic!("the outer binder remains");
    };
    let ValueNode::Callable(inner) = body.params[0].node() else {
        panic!("the inner binder is unused");
    };
    let ValueNode::Bound { owner: bound, .. } = inner.params[0].node() else {
        panic!("the argument refers to the outer binder");
    };
    assert!(owner.same_occurrence(&bound));
}

#[test]
fn a_finite_generic_child_uses_the_canonical_closed_handle() {
    let problem = RawProblem::new("");
    let values = construct(
        &problem.declarations,
        &[
            (Description::Tuple(vec![1]), vec![]),
            (
                Description::Generic {
                    parameters: 2,
                    body: Callable {
                        params: vec![2],
                        ret: 5,
                    },
                },
                vec![],
            ),
            (Description::Tuple(vec![3, 4]), vec![1]),
            (
                Description::Bound {
                    owner: 1,
                    position: 0,
                },
                vec![1],
            ),
            (
                Description::Bound {
                    owner: 1,
                    position: 1,
                },
                vec![1],
            ),
            (Description::Class(ClassType::OBJECT), vec![1]),
        ],
        &[0, 1],
    );
    let ValueNode::Tuple(children) = values[0].node() else {
        panic!("the first root is a tuple");
    };
    assert_eq!(children[0], values[1]);
    assert!(children[0].same_occurrence(&values[1]));
}

#[test]
fn recursive_class_intersections_keep_both_complete_arms() {
    let declarations = "class A; class B; class Box[+T];";
    let problem = RawProblem::new(declarations);
    let a = lookup_class(&problem.declarations, "A");
    let b = lookup_class(&problem.declarations, "B");
    let box_class = lookup_class(&problem.declarations, "Box");
    let nodes = [
        Description::Intersection(vec![1, 4]),
        Description::Union(vec![2, 3]),
        Description::Class(ClassType::plain(a)),
        Description::Class(ClassType {
            class: box_class,
            arguments: vec![1],
        }),
        Description::Class(ClassType::plain(b)),
        Description::Union(vec![6, 7]),
        Description::Intersection(vec![2, 4]),
        Description::Intersection(vec![3, 4]),
    ]
    .into_iter()
    .map(|kind| (kind, vec![]))
    .collect::<Vec<_>>();
    let values = construct(&problem.declarations, &nodes, &[0, 5]);
    assert_eq!(values[0], values[1]);
    assert!(matches!(values[0].node(), ValueNode::Union(parts) if parts.len() == 2));
    compare(declarations, &nodes, 0, 5, true);
    compare(declarations, &nodes, 5, 0, true);
}

#[test]
fn recursive_keys_ignore_node_creation_order() {
    let problem = RawProblem::new("class A; class Box[+T];");
    let a = lookup_class(&problem.declarations, "A");
    let box_class = lookup_class(&problem.declarations, "Box");
    let first = [
        (Description::Union(vec![1, 2]), vec![]),
        (Description::Class(ClassType::plain(a)), vec![]),
        (
            Description::Class(ClassType {
                class: box_class,
                arguments: vec![0],
            }),
            vec![],
        ),
    ];
    let second = [
        (
            Description::Class(ClassType {
                class: box_class,
                arguments: vec![2],
            }),
            vec![],
        ),
        (Description::Class(ClassType::plain(a)), vec![]),
        (Description::Union(vec![0, 1]), vec![]),
    ];
    let first = construct(&problem.declarations, &first, &[0]);
    let second = construct(&problem.declarations, &second, &[2]);
    assert_eq!(first, second);
    assert_eq!(first[0].cmp(&second[0]), Ordering::Equal);
}

#[test]
fn recursive_values_cannot_use_a_superclass_cycle_as_a_proof() {
    let nominal = "class N[-T]; class C extends N[N[C]];";
    let problem = RawProblem::new(nominal);
    let n = lookup_class(&problem.declarations, "N");
    let c = lookup_class(&problem.declarations, "C");
    let nodes = [
        (Description::Class(ClassType::plain(c)), vec![]),
        (
            Description::Class(ClassType {
                class: n,
                arguments: vec![1],
            }),
            vec![],
        ),
        (
            Description::Class(ClassType {
                class: n,
                arguments: vec![0],
            }),
            vec![],
        ),
    ];
    // Both directions through the recursive N type repeat a comparison that
    // used C's superclass. The ground C <: N[C] comparison does the same.
    for (lower, upper) in [(0, 1), (1, 2), (0, 2)] {
        compare(nominal, &nodes, lower, upper, false);
    }
    let covariant = "class Seq[+T]; class S extends Seq[S];";
    let problem = RawProblem::new(covariant);
    let seq = lookup_class(&problem.declarations, "Seq");
    let s = lookup_class(&problem.declarations, "S");
    compare(
        covariant,
        &[
            (Description::Class(ClassType::plain(s)), vec![]),
            (
                Description::Class(ClassType {
                    class: seq,
                    arguments: vec![1],
                }),
                vec![],
            ),
        ],
        0,
        1,
        false,
    );
}

#[test]
fn recursive_generic_arms_preserve_their_parameter_owners() {
    let declarations = "class A; class B;";
    let problem = RawProblem::new(declarations);
    let a = lookup_class(&problem.declarations, "A");
    let b = lookup_class(&problem.declarations, "B");
    // G = (forall Z. (Z | G) -> A) | (forall V. (V | G) -> B).
    // Z and V have the same position but different owners.
    let nodes = vec![
        (Description::Union(vec![1, 2]), vec![]),
        (
            Description::Generic {
                parameters: 1,
                body: Callable {
                    params: vec![3],
                    ret: 7,
                },
            },
            vec![],
        ),
        (
            Description::Generic {
                parameters: 1,
                body: Callable {
                    params: vec![4],
                    ret: 8,
                },
            },
            vec![],
        ),
        (Description::Union(vec![5, 0]), vec![1]),
        (Description::Union(vec![6, 0]), vec![2]),
        (
            Description::Bound {
                owner: 1,
                position: 0,
            },
            vec![1],
        ),
        (
            Description::Bound {
                owner: 2,
                position: 0,
            },
            vec![2],
        ),
        (Description::Class(ClassType::plain(a)), vec![]),
        (Description::Class(ClassType::plain(b)), vec![]),
    ];
    let values = construct(&problem.declarations, &nodes, &[0]);
    let ValueNode::Union(arms) = values[0].node() else {
        panic!("the two return types differ");
    };
    let parameters = arms
        .iter()
        .map(|arm| {
            let owner = arm.clone();
            let ValueNode::Generic { parameters, body } = arm.node() else {
                panic!("each arm retains its binder");
            };
            assert_eq!(parameters, 1);
            let ValueNode::Union(parts) = body.params[0].node() else {
                panic!("the parameter includes G and the bound type");
            };
            let bound = parts
                .into_iter()
                .find(|part| matches!(part.node(), ValueNode::Bound { .. }))
                .expect("the arm uses its own parameter");
            let ValueNode::Bound {
                owner: bound_owner, ..
            } = bound.node()
            else {
                panic!("the selected part is a parameter");
            };
            assert!(owner.same_binding(&bound_owner));
            bound
        })
        .collect::<Vec<_>>();
    let [first, second] = parameters.as_slice() else {
        panic!("G has two arms");
    };
    assert_ne!(first, second);
    let input = Input::fixture(&problem);
    let relation = ClassRelation::new(&input);
    assert!(!is_subtype(first, second, &relation));
    assert!(!is_subtype(second, first, &relation));
    let mut swapped = nodes.clone();
    swapped.swap(7, 8);
    equivalent(declarations, &nodes, &swapped);
}
