//! Removal records must preserve the type of their containing operation.

use crate::frontend::problem::{Callable, ClassType};
use crate::frontend::test_support::{RawProblem, lookup_class};
use crate::solver::input::Input;

use super::super::super::super::ClassRelation;
use super::super::super::{Description, Type, ValueNode, construct, is_subtype};
use super::{Normalization, Removal, Rewrite, normalize, snapshot};

#[test]
fn a_removal_chain_keeps_the_type_of_the_complete_union() {
    let problem = RawProblem::new("class A extends B; class B extends C; class C;");
    let input = Input::fixture(&problem);
    let relation = ClassRelation::new(&input);
    let classes = ["A", "B", "C"].map(|name| lookup_class(&problem.declarations, name));
    let mut nodes = classes
        .map(|class| (Description::Class(ClassType::plain(class)), Vec::new()))
        .to_vec();
    nodes.push((Description::Union(vec![0, 1, 2]), Vec::new()));
    let values = construct(&problem.declarations, &nodes, &[3]);
    let normalized = normalize(&values[0], &relation);
    normalized.validate(&relation);
    assert!(
        matches!(normalized.result().node(), ValueNode::Class { class, .. } if class == classes[2])
    );
    assert!(is_subtype(&values[0], normalized.result(), &relation));
    assert!(is_subtype(normalized.result(), &values[0], &relation));
}

#[test]
#[should_panic(expected = "normalization removal refers to a removed child")]
fn equivalent_children_cannot_justify_removing_each_other() {
    let problem = RawProblem::new("class A; class B extends A;");
    let input = Input::fixture(&problem);
    let relation = ClassRelation::new(&input);
    let a = lookup_class(&problem.declarations, "A");
    let b = lookup_class(&problem.declarations, "B");
    let nodes = [
        (Description::Class(ClassType::plain(a)), Vec::new()),
        (Description::Class(ClassType::plain(b)), Vec::new()),
        (Description::Union(vec![0, 1]), Vec::new()),
        (
            Description::Callable(Callable {
                params: vec![0],
                ret: 0,
            }),
            Vec::new(),
        ),
        (
            Description::Callable(Callable {
                params: vec![2],
                ret: 0,
            }),
            Vec::new(),
        ),
        (Description::Union(vec![3, 4]), Vec::new()),
    ];
    let mut values = construct(&problem.declarations, &nodes, &[5]);
    let original = values.remove(0);
    let mut nodes = original.definition().nodes.clone();
    let Type::Union(children) = &nodes[original.node].kind else {
        panic!("the two equivalent callables retain distinct structures");
    };
    let [first, second] = children.as_slice() else {
        panic!("the union has two callable children");
    };
    let removals = vec![
        Removal {
            removed: *first,
            other: *second,
        },
        Removal {
            removed: *second,
            other: *first,
        },
    ];
    let children = snapshot(&nodes, &[*first, *second], &relation);
    assert!(is_subtype(&children[0], &children[1], &relation));
    assert!(is_subtype(&children[1], &children[0], &relation));
    nodes[original.node].kind = Type::Never;
    let result = snapshot(&nodes, &[original.node], &relation).remove(0);
    assert!(!is_subtype(&original, &result, &relation));
    let node = original.node;
    Normalization {
        original,
        result,
        passes: vec![vec![Rewrite { node, removals }]],
    }
    .validate(&relation);
}
