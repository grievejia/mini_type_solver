use crate::frontend::problem::{AtomId, BoundRef, Callable, ClassId, ClassType, Generic};
use crate::frontend::test_support::{RawProblem, lookup_class, lookup_metavar};
use crate::solver::input::Input;
use std::num::NonZeroU32;

use super::super::super::ClassRelation;
use super::super::graph::{FactorNode, Graph};
use super::super::identities::{Identities, ROOT_SCOPE, source_value};
use super::cycles::cycles_pass;
use super::scopes::Context;
use super::{
    Comparison, EdgeKind, Rule, State, Step, apply_alternative, bare_variable, propagate,
    run_search,
};

fn test_atom(problem: &mut RawProblem) -> AtomId {
    let object = problem.types.intern_class(ClassId::OBJECT, Vec::new());
    problem.atoms.intern_atom(object, object)
}

impl State {
    fn test_goal(&mut self, comparison: Comparison, check: AtomId) -> usize {
        self.goal(
            comparison,
            Context {
                check,
                path: Vec::new(),
                scope: ROOT_SCOPE,
            },
        )
    }
}

#[test]
fn composition_belongs_to_upper_request_in_both_arrival_orders() {
    let mut problem = RawProblem::new("class A; class B;");
    let metavar = problem.declare_metavar("X");
    let check = test_atom(&mut problem);
    let input = Input::fixture(&problem);
    let relation = ClassRelation::new(&input);
    let a = lookup_class(input.declarations(), "A");
    let graph = &Graph::new(input.declarations());
    let identities = &mut Identities::new();
    let variable = identities.declared(metavar);
    let reference = graph.factor(FactorNode::Ref(variable));
    let lower = graph.factor(FactorNode::Class(ClassType::plain(a)));
    let upper = graph.object();
    for upper_first in [false, true] {
        let mut state = State::new([variable].into_iter());
        let reflexive = state.test_goal(
            Comparison {
                lower: reference.clone(),
                upper: reference.clone(),
            },
            check,
        );
        let membership = Comparison {
            lower: lower.clone(),
            upper: reference.clone(),
        };
        let request = Comparison {
            lower: reference.clone(),
            upper: upper.clone(),
        };
        let (membership, request) = if upper_first {
            let request = state.test_goal(request, check);
            (state.test_goal(membership, check), request)
        } else {
            let membership = state.test_goal(membership, check);
            (membership, state.test_goal(request, check))
        };
        assert!(run_search(graph, &mut state, identities, &relation));
        // A self-comparison adds no expression to X. Otherwise every X <: U
        // would require itself again through that expression.
        assert!(!state.bounds[&variable].lower.contains(&reference));
        assert!(state.goals[reflexive].children.is_empty());
        assert!(
            !state.goals[request]
                .children
                .contains(&(EdgeKind::Ordinary, request))
        );
        let composed = state.goal_ids[&(
            Comparison {
                lower: lower.clone(),
                upper: upper.clone(),
            },
            None,
        )];
        assert!(state.goals[membership].children.is_empty());
        assert!(
            state.goals[request]
                .children
                .contains(&(EdgeKind::Ordinary, composed))
        );
    }
}

#[test]
fn removing_variable_loops_keeps_superclass_and_constructor_steps() {
    let mut problem = RawProblem::new("class A;");
    let x = problem.declare_metavar("X");
    let y = problem.declare_metavar("Y");
    let check = test_atom(&mut problem);
    let input = Input::fixture(&problem);
    let graph = &Graph::new(input.declarations());
    let identities = &mut Identities::new();
    let x = identities.declared(x);
    let y = identities.declared(y);
    let xv = graph.factor(FactorNode::Ref(x));
    let yv = graph.factor(FactorNode::Ref(y));
    let a = lookup_class(input.declarations(), "A");
    let upper = graph.factor(FactorNode::Class(ClassType::plain(a)));
    for kind in [EdgeKind::Constructor, EdgeKind::Superclass] {
        let mut state = State::new([x, y].into_iter());
        let x_goal = state.test_goal(
            Comparison {
                lower: xv.clone(),
                upper: upper.clone(),
            },
            check,
        );
        let y_goal = state.test_goal(
            Comparison {
                lower: yv.clone(),
                upper: upper.clone(),
            },
            check,
        );
        let constructor = state.test_goal(
            Comparison {
                lower: graph.factor(FactorNode::Tuple(vec![xv.clone()])),
                upper: upper.clone(),
            },
            check,
        );
        state.goals[x_goal]
            .children
            .insert((EdgeKind::Ordinary, constructor));
        state.goals[constructor].children.insert((kind, y_goal));
        state.goals[y_goal]
            .children
            .insert((EdgeKind::Ordinary, x_goal));
        assert_eq!(cycles_pass(&state), kind == EdgeKind::Constructor);
    }
}

fn submit(input: &Input<'_>, graph: &Graph, identities: &mut Identities) -> State {
    let mut state = State::new(
        input
            .declarations()
            .metavars()
            .map(|(id, _)| identities.declared(id)),
    );
    for (id, atom) in input.atoms().entries() {
        state.goal(
            Comparison {
                lower: source_value(graph, atom.lower, input.types(), identities),
                upper: source_value(graph, atom.upper, input.types(), identities),
            },
            Context {
                check: id,
                path: Vec::new(),
                scope: ROOT_SCOPE,
            },
        );
    }
    state
}

#[test]
fn a_deferred_record_keeps_eight_independent_checked_instances() {
    let problem = RawProblem::new(include_str!(
        "../../../../../benchmarks/synthetic/37_generic_per_requirement.input"
    ));
    let input = Input::fixture(&problem);
    let relation = ClassRelation::new(&input);
    let graph = &Graph::new(input.declarations());
    let identities = &mut Identities::new();
    let mut state = submit(&input, graph, identities);
    assert!(run_search(graph, &mut state, identities, &relation));
    let records = state.scopes.instance_routes().collect::<Vec<_>>();
    let [(_, instances)] = records.as_slice() else {
        panic!("one generic at one tuple position needs one home record");
    };
    assert_eq!(instances.len(), 8);
    for requirement in instances.keys() {
        assert!(state.goals.iter().any(
            |goal| matches!(goal.rule, Rule::Instance { requirement: id, .. } if id == *requirement)
        ));
    }
}

#[test]
fn failed_instance_alternatives_restore_requirements_and_selection_variables() {
    let problem = RawProblem::new(
        "class B; class A; assert forall X. (X) -> X <: (forall Y. (Y) -> Y) -> (((A) -> B) | ((A) -> A));",
    );
    let input = Input::fixture(&problem);
    let relation = ClassRelation::new(&input);
    let graph = &Graph::new(input.declarations());
    let identities = &mut Identities::new();
    let mut state = submit(&input, graph, identities);
    assert!(run_search(graph, &mut state, identities, &relation));
    // B is declared first, so the failing A -> B instance is tried first.
    // Only the successful A -> A requirement and its variables may survive.
    assert_eq!(state.scopes.choices.len(), 1);
    assert!(
        state
            .scopes
            .instance_routes()
            .all(|(_, instances)| instances.len() == 1)
    );
    assert_eq!(state.bounds.len(), 3);
}

#[test]
fn negative_generic_conversion_uses_arbitrary_parameters_and_constructor_variance() {
    let mut problem = RawProblem::new("class Inv[T];");
    let check = test_atom(&mut problem);
    let input = Input::fixture(&problem);
    let relation = ClassRelation::new(&input);
    let graph = &Graph::new(input.declarations());
    let identities = &mut Identities::new();
    let bound = graph.factor(FactorNode::Bound(BoundRef::new(0, 0)));
    let one = NonZeroU32::new(1).expect("one parameter is nonzero");
    let lower = graph.factor(FactorNode::Generic(Generic {
        parameters: one,
        body: Callable {
            params: vec![bound.clone()],
            ret: graph.object(),
        },
    }));
    let inv = lookup_class(input.declarations(), "Inv");
    let argument = graph.factor(FactorNode::Class(ClassType {
        class: inv,
        arguments: vec![bound.clone()],
    }));
    let generic = graph.factor(FactorNode::Generic(Generic {
        parameters: one,
        body: Callable {
            params: vec![argument],
            ret: bound,
        },
    }));
    let argument = graph.factor(FactorNode::Callable(Callable {
        params: vec![generic],
        ret: graph.object(),
    }));
    let upper = graph.factor(FactorNode::Callable(Callable {
        params: vec![argument],
        ret: graph.object(),
    }));
    let mut state = State::new([].into_iter());
    state.test_goal(Comparison { lower, upper }, check);
    assert!(run_search(graph, &mut state, identities, &relation));
    let arguments = state
        .goals
        .iter()
        .find_map(|goal| match &goal.rule {
            Rule::LowerGeneric { arguments } => Some(arguments),
            _ => None,
        })
        .expect("lower selection exists");
    let selected = bare_variable(&arguments[0]).expect("selection is a variable");
    let narrowed = graph.factor(FactorNode::Callable(Callable {
        params: vec![graph.object()],
        ret: graph.never(),
    }));
    let expected = graph.factor(FactorNode::Callable(Callable {
        params: vec![narrowed],
        ret: graph.object(),
    }));
    assert_eq!(
        state.bounds[&selected].lower,
        [expected].into_iter().collect()
    );
    assert_eq!(state.scopes.introductions.len(), 1);
}

#[test]
fn the_nominal_atom_batch_derives_a_ground_cycle_before_building_values() {
    let problem = RawProblem::new(include_str!(
        "../../../../../tests/data/solve/unsat/nominal_contravariant_cycle.input"
    ));
    let input = Input::fixture(&problem);
    let relation = ClassRelation::new(&input);
    let graph = &Graph::new(input.declarations());
    let identities = &mut Identities::new();
    let mut state = submit(&input, graph, identities);
    while let Some(id) = state.pending.pop_front() {
        state.queued.remove(&id);
        match propagate(graph, id, &mut state, identities, &relation) {
            Step::Done => {}
            Step::Choose(alternatives) => {
                let mut alternatives = alternatives.into_iter();
                let Some(first) = alternatives.next() else {
                    panic!("the fixture has no empty type alternative");
                };
                assert!(
                    alternatives.next().is_none(),
                    "the fixture has one factor per arm"
                );
                apply_alternative(graph, id, first, &mut state, identities);
            }
            Step::Reject => panic!("the clash is a repeated superclass comparison"),
        }
    }
    let c = lookup_class(input.declarations(), "C");
    let n = lookup_class(input.declarations(), "N");
    let c = graph.factor(FactorNode::Class(ClassType::plain(c)));
    let nc = graph.factor(FactorNode::Class(ClassType {
        class: n,
        arguments: vec![c.clone()],
    }));
    assert!(state.goal_ids.contains_key(&(
        Comparison {
            lower: c,
            upper: nc
        },
        None
    )));
    assert!(!cycles_pass(&state));
}

#[test]
fn covariant_class_composition_belongs_to_the_upper_bound_in_every_order() {
    let declarations = "class Seq[+T]; class S extends Seq[S]; metavar ?X;";
    let assertions = [
        "assert S <: ?X;",
        "assert ?X <: Seq[?X];",
        "assert Seq[?X] <: ?X;",
    ];
    for order in [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ] {
        let source = format!(
            "{declarations} {}",
            order.map(|index| assertions[index]).join(" ")
        );
        let problem = RawProblem::new(&source);
        let input = Input::fixture(&problem);
        let relation = ClassRelation::new(&input);
        let graph = &Graph::new(input.declarations());
        let identities = &mut Identities::new();
        let mut state = submit(&input, graph, identities);
        assert!(run_search(graph, &mut state, identities, &relation));
        let x = identities.declared(lookup_metavar(input.declarations(), "X"));
        let x = graph.factor(FactorNode::Ref(x));
        let s_class = lookup_class(input.declarations(), "S");
        let seq_class = lookup_class(input.declarations(), "Seq");
        let s = graph.factor(FactorNode::Class(ClassType::plain(s_class)));
        let seq = graph.factor(FactorNode::Class(ClassType {
            class: seq_class,
            arguments: vec![x.clone()],
        }));
        let membership = state.goal_ids[&(
            Comparison {
                lower: s.clone(),
                upper: x.clone(),
            },
            None,
        )];
        let request = state.goal_ids[&(
            Comparison {
                lower: x,
                upper: seq.clone(),
            },
            None,
        )];
        let composed = state.goal_ids[&(
            Comparison {
                lower: s,
                upper: seq,
            },
            None,
        )];
        assert!(state.goals[membership].children.is_empty());
        assert!(
            state.goals[request]
                .children
                .contains(&(EdgeKind::Ordinary, composed))
        );
    }
}
