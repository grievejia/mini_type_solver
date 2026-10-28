//! Checks for graph identity, ordering, and checked substitution.

use std::cmp::Ordering;
use std::rc::Rc;
use std::slice;

use crate::frontend::problem::{BoundRef, ClassType};
use crate::frontend::test_support::{RawProblem, lookup_class, lookup_metavar};
use crate::solver::input::Input;

use super::super::super::ClassRelation;
use super::super::identities::{Identities, source_value};
use super::{FactorNode, Graph};

#[test]
fn source_conversion_shares_constructor_children_and_keeps_reference_identity() {
    let mut problem = RawProblem::new("class Box[T]; metavar ?X;");
    let input = Input::fixture(&problem);
    let box_class = lookup_class(input.declarations(), "Box");
    let x = lookup_metavar(input.declarations(), "X");
    let x_type = input.types().metavar_type(x);
    let box_type = problem.types.intern_class(box_class, vec![x_type]);
    let tuple = problem.types.intern_tuple(vec![box_type, box_type]);
    let input = Input::fixture(&problem);
    let graph = &Graph::new(input.declarations());
    let identities = &mut Identities::new();
    let value = source_value(graph, tuple, input.types(), identities);
    let FactorNode::Tuple(children) = value.arms()[0].factors()[0].node() else {
        panic!("fixture must retain its tuple");
    };
    assert!(Rc::ptr_eq(&children[0].0.data, &children[1].0.data));
    let count = graph.nodes.borrow().next;
    let repeated = source_value(graph, tuple, input.types(), identities);
    assert!(Rc::ptr_eq(&value.0.data, &repeated.0.data));
    assert_eq!(graph.nodes.borrow().next, count);
    let variable = identities.declared(x);
    assert_eq!(
        source_value(graph, x_type, input.types(), identities),
        graph.factor(FactorNode::Ref(variable))
    );
}

#[test]
fn structural_order_uses_type_structure_and_keeps_lexical_coordinates() {
    let problem = RawProblem::new("class A; class B;");
    let input = Input::fixture(&problem);
    let graph = Graph::new(input.declarations());
    let b_class = lookup_class(input.declarations(), "B");
    let a_class = lookup_class(input.declarations(), "A");
    let b = graph.factor(FactorNode::Class(ClassType::plain(b_class)));
    let a = graph.factor(FactorNode::Class(ClassType::plain(a_class)));
    assert!(b.0.id < a.0.id);
    assert_eq!(a.cmp(&b), Ordering::Less);
    let outer = graph.factor(FactorNode::Bound(BoundRef::new(1, 0)));
    let inner = graph.factor(FactorNode::Bound(BoundRef::new(0, 0)));
    assert_ne!(outer, inner);
    let mut shared = a.clone();
    for _ in 0..128 {
        shared = graph.factor(FactorNode::Tuple(vec![shared.clone(), shared]));
    }
    let left = graph.factor(FactorNode::Tuple(vec![shared.clone(), a]));
    let right = graph.factor(FactorNode::Tuple(vec![shared, b]));
    assert_eq!(left.cmp(&right), Ordering::Less);
}

#[test]
fn unknown_factors_do_not_hide_fixed_shape_conflicts() {
    let problem = RawProblem::new("class A; class B; metavar ?X;");
    let input = Input::fixture(&problem);
    let graph = &Graph::new(input.declarations());
    let identities = &mut Identities::new();
    let a_class = lookup_class(input.declarations(), "A");
    let b_class = lookup_class(input.declarations(), "B");
    let a = graph.intern_factor(FactorNode::Class(ClassType::plain(a_class)));
    let b = graph.intern_factor(FactorNode::Class(ClassType::plain(b_class)));
    let x = lookup_metavar(input.declarations(), "X");
    let variable = graph.intern_factor(FactorNode::Ref(identities.declared(x)));
    let tuple = graph.intern_factor(FactorNode::Tuple(Vec::new()));
    assert!(
        graph
            .arm(vec![tuple, variable.clone(), a.clone()])
            .is_none()
    );
    let Some(overlap) = graph.arm(vec![variable.clone(), b.clone(), a.clone()]) else {
        panic!("a variable and two unrelated class factors can overlap");
    };
    assert_eq!(overlap.factors(), &[a, b, variable]);
}

#[test]
fn ancestor_substitution_reuses_nodes_and_preserves_actual_bound_references() {
    let problem = RawProblem::new("class Root[+T]; class Leaf[+T] extends Root[tuple[T, T]];");
    let input = Input::fixture(&problem);
    let relation = ClassRelation::new(&input);
    let owner = lookup_class(input.declarations(), "Leaf");
    let root = lookup_class(input.declarations(), "Root");
    let Some(template) = relation.ancestor_template(owner, root) else {
        panic!("Leaf must have Root as an ancestor");
    };
    let graph = Graph::new(input.declarations());
    let argument = graph.factor(FactorNode::Bound(BoundRef::new(1, 0)));
    let first = graph.ancestor_arguments(owner, template, slice::from_ref(&argument));
    let count = graph.nodes.borrow().next;
    let second = graph.ancestor_arguments(owner, template, slice::from_ref(&argument));
    assert!(Rc::ptr_eq(&first[0].0.data, &second[0].0.data));
    assert_eq!(graph.nodes.borrow().next, count);
    let FactorNode::Tuple(children) = first[0].arms()[0].factors()[0].node() else {
        panic!("ancestor argument must remain a tuple");
    };
    assert_eq!(children, &[argument.clone(), argument]);
    let different = graph.factor(FactorNode::Bound(BoundRef::new(0, 0)));
    let different = graph.ancestor_arguments(owner, template, &[different]);
    assert_ne!(first, different);
    assert_eq!(graph.nodes.borrow().templates.len(), 2);
}
