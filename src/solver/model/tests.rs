//! Tests for independent model checks with valid witnesses and invalid assignments.

use crate::frontend::Span;
use crate::frontend::problem::{BoundRef, Callable, ClassId, ClassType, Declarations, TypeNode};
use crate::frontend::test_support::{RawProblem, generic_identity, lookup_class, lookup_metavar};
use crate::solver::input::Input;

use super::super::dnf::run_dnf;
use super::super::test_support::{
    FIXTURE_DECLARATIONS, ModelInput, assert_core_minimal, atom, atom_from_ids, fixture_problem,
    model_holds, validate_ok,
};
use super::super::tests::{Engine, check_canonical, run_engine};
use super::super::theory::TheoryResult;
use super::super::{
    AtomFormula, DnfStats, Model, ModelEntry, ModelValue, SharedStats, SolveOutcome, WorkUnit,
    build_model, solve_conjunction, work_units,
};
use std::collections::HashSet;
use std::rc::Rc;

use super::super::theory::closed::{Description, construct};
use super::{AssignedNode, AssignedValue, DisplayNames};

#[test]
fn source_model_checker_rejects_a_changed_invariant_argument() {
    let source = "class Dog; class Cat; class Inv[T]; metavar ?M; assert Inv[Dog] <: ?M;";
    let file = validate_ok(source);
    let SolveOutcome::Satisfiable(mut model) =
        run_engine(Engine::Direct, &work_units(&file), &Input::new(&file))
    else {
        panic!("the source has the model M = Inv[Dog]");
    };
    assert!(model_holds(ModelInput::Source(source), &model));
    let inv = lookup_class(file.declarations(), "Inv");
    let cat = lookup_class(file.declarations(), "Cat");
    model.entries[0].value = described_value(
        file.declarations(),
        &[
            Description::Class(ClassType {
                class: inv,
                arguments: vec![1],
            }),
            Description::Class(ClassType::plain(cat)),
        ],
    );
    assert!(!model_holds(ModelInput::Source(source), &model));
}

#[test]
fn original_and_normalized_witnesses_satisfy_the_source_bounds() {
    for (source, original_text, normalized_text) in [
        (
            "class A; class B1; class B2; metavar ?X; metavar ?Y;
             assert ?Y <: ?X; assert B1 <: ?X; assert ?X & A <: ?Y; assert B2 <: ?Y;",
            "satisfiable\nmodel:\n  ?X = A & B1 | B1 | B2\n  ?Y = A & B1 | B2\n",
            "satisfiable\nmodel:\n  ?X = B1 | B2\n  ?Y = A & B1 | B2\n",
        ),
        (
            "class B; class A extends D; class D; metavar ?X;
             assert (((A) -> D) -> B) & (((A) -> A) -> B) <: ?X;
             assert ?X <: (forall Z. (Z) -> Z) -> B;",
            "satisfiable\nmodel:\n  ?X = (((A) -> A) -> B) & (((A) -> D) -> B)\n",
            "satisfiable\nmodel:\n  ?X = ((A) -> D) -> B\n",
        ),
        (
            // The outward demand must also supply the home selection.
            // Its callable instance makes the intersection with C empty.
            "class A; class C; metavar ?Z; metavar ?W;
             assert forall X. (X) -> tuple[X & C, X]
                 <: (forall Y. (Y) -> Y) -> tuple[?Z, ?W];
             assert ?W <: (A) -> A;",
            "satisfiable\nmodel:\n  ?Z = never\n  ?W = (A) -> A\n",
            "satisfiable\nmodel:\n  ?Z = never\n  ?W = (A) -> A\n",
        ),
    ] {
        let file = validate_ok(source);
        let atoms = work_units(&file)
            .iter()
            .map(|unit| {
                let AtomFormula::Atom(atom) = unit.formula else {
                    panic!("the witness fixture contains only subtype assertions");
                };
                *atom
            })
            .collect::<Vec<_>>();
        let TheoryResult::Satisfiable(solution) = solve_conjunction(&atoms, &Input::new(&file))
        else {
            panic!("the original lower equations satisfy these bounds");
        };
        let originals = file
            .declarations()
            .metavars()
            .map(|(id, name)| {
                let value = solution
                    .witness(id)
                    .expect("the fixture variable is constrained");
                (name.to_owned(), value.clone())
            })
            .collect::<Vec<_>>();
        let normalized = build_model(file.declarations(), solution);
        assert!(model_holds(ModelInput::Source(source), &normalized));
        assert_eq!(normalized.render(), normalized_text);
        let ModelValue::Assigned(value) = &normalized.entries[0].value else {
            panic!("the first fixture variable has an assignment");
        };
        let original = Model {
            entries: originals
                .into_iter()
                .map(|(metavar, original)| ModelEntry {
                    metavar,
                    value: ModelValue::Assigned(AssignedValue {
                        value: original,
                        names: Rc::clone(&value.names),
                    }),
                })
                .collect(),
        };
        assert!(model_holds(ModelInput::Source(source), &original));
        assert_eq!(original.render(), original_text);
    }
}

#[test]
fn independent_checker_accepts_a_generic_declared_assignment() {
    let declarations = "";
    let mut problem = RawProblem::new(declarations);
    let selected = problem.declare_metavar("T");
    let generic = generic_identity(&mut problem);
    let selected_type = problem.types.types().metavar_type(selected);
    let formula = atom_from_ids(&mut problem, generic, selected_type);
    check_canonical(declarations, &Input::fixture(&problem), &[formula], true);
}

#[test]
fn independent_checker_rejects_rigid_as_a_tuple_model() {
    let declarations = "class A;";
    let mut problem = RawProblem::new(declarations);
    let a = lookup_class(&problem.declarations, "A");
    let selected = problem.declare_metavar("T");
    let lower = generic_identity(&mut problem);
    let rigid = problem.types.intern_bound(BoundRef::new(0, 0));
    let upper_body = Callable {
        params: vec![rigid],
        ret: problem.types.types().metavar_type(selected),
    };
    let upper = problem.types.intern_generic(1, &upper_body);
    let atom = problem.atoms.intern_atom(lower, upper);
    let TheoryResult::Satisfiable(solution) = solve_conjunction(&[atom], &Input::fixture(&problem))
    else {
        panic!("generic tuple-model fixture must be satisfiable");
    };
    let mut model = build_model(&problem.declarations, solution);
    model.entries[0].value = described_value(
        &problem.declarations,
        &[
            Description::Tuple(vec![1]),
            Description::Class(ClassType::plain(a)),
        ],
    );
    let formula = AtomFormula::Atom(atom);
    let formulas = [&formula];
    assert!(!model_holds(
        ModelInput::Canonical {
            declarations,
            input: &Input::fixture(&problem),
            formulas: &formulas,
        },
        &model,
    ));
}

#[test]
fn independent_checker_uses_upper_rigids_as_lower_witnesses() {
    let declarations = "";
    let mut problem = RawProblem::new(declarations);
    let object = problem.types.intern_class(ClassId::OBJECT, Vec::new());
    let lower = generic_identity(&mut problem);
    let upper_parameter = problem.types.intern_bound(BoundRef::new(0, 0));
    let upper_body = Callable {
        params: vec![upper_parameter],
        ret: object,
    };
    let upper = problem.types.intern_generic(1, &upper_body);
    let formula = atom_from_ids(&mut problem, lower, upper);
    check_canonical(declarations, &Input::fixture(&problem), &[formula], true);

    let first = problem.types.intern_bound(BoundRef::new(0, 0));
    let second = problem.types.intern_bound(BoundRef::new(0, 1));
    let two_body = Callable {
        params: vec![first, second],
        ret: first,
    };
    let two_parameters = problem.types.intern_generic(2, &two_body);
    let repeated = problem.types.intern_bound(BoundRef::new(0, 0));
    let one_body = Callable {
        params: vec![repeated, repeated],
        ret: repeated,
    };
    let one_parameter = problem.types.intern_generic(1, &one_body);
    let forward = atom_from_ids(&mut problem, two_parameters, one_parameter);
    check_canonical(declarations, &Input::fixture(&problem), &[forward], true);
    let reverse = atom_from_ids(&mut problem, one_parameter, two_parameters);
    check_canonical(declarations, &Input::fixture(&problem), &[reverse], false);
}

#[test]
fn independent_checker_uses_witness_from_a_substituted_body() {
    let declarations = "";
    let mut problem = RawProblem::new(declarations);
    let lower = generic_identity(&mut problem);
    let stored = problem.declare_metavar("G");
    let stored_type = problem.types.types().metavar_type(stored);
    let store_generic = atom_from_ids(&mut problem, lower, stored_type);
    let rigid = problem.types.intern_bound(BoundRef::new(0, 0));
    let rigid_identity = problem.types.intern_callable(vec![rigid], rigid);
    let home_scope_body = Callable {
        params: vec![stored_type],
        ret: rigid_identity,
    };
    let home_scope_upper = problem.types.intern_generic(1, &home_scope_body);
    let home_scope = atom_from_ids(&mut problem, lower, home_scope_upper);
    check_canonical(
        declarations,
        &Input::fixture(&problem),
        &[store_generic, home_scope],
        true,
    );
}

#[test]
fn source_model_checker_accepts_open_world_intersections() {
    let source = "class a;\nclass b;\nmetavar ?T;\nassert ?T <: a;\nassert ?T <: b;";
    let file = validate_ok(source);
    let a = lookup_class(file.declarations(), "a");
    let b = lookup_class(file.declarations(), "b");
    let intersection = Model {
        entries: vec![ModelEntry {
            metavar: String::from("T"),
            value: model_value(&Input::new(&file), &[&[a, b]]),
        }],
    };
    let only_a = Model {
        entries: vec![ModelEntry {
            metavar: String::from("T"),
            value: model_value(&Input::new(&file), &[&[a]]),
        }],
    };

    assert!(model_holds(ModelInput::Source(source), &intersection));
    assert!(!model_holds(ModelInput::Source(source), &only_a));
}

#[test]
fn source_model_checker_closes_direct_edges_transitively() {
    let source = "class a;\nclass b extends a;\nclass c extends b;\nmetavar ?T;\nassert c <: ?T;\nassert ?T <: a;";
    let file = validate_ok(source);
    let c = lookup_class(file.declarations(), "c");
    let model = Model {
        entries: vec![ModelEntry {
            metavar: String::from("T"),
            value: model_value(&Input::new(&file), &[&[c]]),
        }],
    };

    assert!(model_holds(ModelInput::Source(source), &model));
}

#[test]
fn source_model_checker_substitutes_class_values_inside_tuples() {
    let source = "class a;\nmetavar ?T;\nassert tuple[?T] <: tuple[a];";
    let problem = RawProblem::new("class a;");
    let a = lookup_class(&problem.declarations, "a");
    let accepting = Model {
        entries: vec![ModelEntry {
            metavar: String::from("T"),
            value: model_value(&Input::fixture(&problem), &[&[a]]),
        }],
    };
    let rejecting = Model {
        entries: vec![ModelEntry {
            metavar: String::from("T"),
            value: model_value(&Input::fixture(&problem), &[&[ClassId::OBJECT]]),
        }],
    };

    assert!(model_holds(ModelInput::Source(source), &accepting));
    assert!(!model_holds(ModelInput::Source(source), &rejecting));
}

#[test]
fn source_model_checker_accepts_ground_tuple_covariance() {
    for source in [
        "assert tuple[] <: tuple[];",
        "class a;\nclass b extends a;\nassert tuple[b] <: tuple[a];",
        "class a;\nclass b extends a;\nassert tuple[tuple[b], a] <: tuple[tuple[a], object];",
        "class a;\nassert never <: tuple[a];\nassert tuple[a] <: object;",
    ] {
        assert!(ground_source_holds(source), "source was:\n{source}");
    }
}

#[test]
fn source_model_checker_resolves_generic_binders() {
    assert!(ground_source_holds(
        "class A;\nclass X;\nassert forall X. (X) -> X <: (A) -> A;"
    ));
    assert!(!ground_source_holds(
        "class A;\nclass X;\nassert (A) -> A <: forall X. (X) -> X;"
    ));
}

#[test]
fn source_model_checker_rewrites_exact_sets_before_candidate_collection() {
    assert!(ground_source_holds(
        "class A;\n\
         assert forall X. (X) -> X\n\
             <: (tuple[forall Y in {A}. (Y) -> Y])\n\
                -> tuple[forall Z in {A}. (Z) -> Z];"
    ));
}

#[test]
fn source_model_checker_keeps_outer_body_references_after_exact_rewriting() {
    assert!(ground_source_holds(
        "class A;\nclass B;\n\
         assert forall O. (O) ->\n\
                forall P. (P) ->\n\
                forall X in {A}. (X) -> forall Q. (Q) -> tuple[O, P, Q]\n\
             <: (A) -> (B) -> (A) -> forall K. (K) -> tuple[A, B, K];"
    ));
}

#[test]
fn source_model_checker_keeps_outer_body_references_after_upper_rewriting() {
    assert!(ground_source_holds(
        "class A;\nclass B;\nclass C extends A;\n\
         assert forall O. (O) ->\n\
                forall P in {B}. (P) ->\n\
                forall X <: A. (X) ->\n\
                forall Q. (X) -> tuple[O, P, X, Q]\n\
             <: (A) -> (B) -> (C) -> (C) -> tuple[A, B, C, object];"
    ));
}

#[test]
fn source_model_checker_keeps_body_references_before_shadowing() {
    assert!(ground_source_holds(
        "class A;\n\
         assert forall Y. (Y) -> forall X <: A. (X & Y) -> forall Y. (X) -> Y\n\
             <: (A) -> (A) -> forall K. (A) -> K;"
    ));
}

#[test]
fn source_model_checker_rejects_changed_tuple_length_or_element() {
    for source in [
        "class a;\nassert tuple[a] <: tuple[a, a];",
        "class a;\nclass b;\nassert tuple[a] <: tuple[b];",
    ] {
        assert!(!ground_source_holds(source), "source was:\n{source}");
    }
}

#[test]
fn source_model_checker_distinguishes_tuple_never_from_never() {
    assert!(!ground_source_holds("assert tuple[never] <: never;"));
    assert!(ground_source_holds("assert never <: tuple[never];"));
}

#[test]
fn source_model_checker_distinguishes_element_union_from_tuple_union() {
    let declarations = "class a;\nclass b;\n";
    assert!(ground_source_holds(&format!(
        "{declarations}assert tuple[a] | tuple[b] <: tuple[a | b];"
    )));
    assert!(!ground_source_holds(&format!(
        "{declarations}assert tuple[a | b] <: tuple[a] | tuple[b];"
    )));
}

#[test]
fn source_model_checker_distinguishes_element_intersection_from_tuple_intersection() {
    let declarations = "class a;\nclass b;\n";
    assert!(ground_source_holds(&format!(
        "{declarations}assert tuple[a & b] <: tuple[a] & tuple[b];"
    )));
    assert!(!ground_source_holds(&format!(
        "{declarations}assert tuple[a] & tuple[b] <: tuple[a & b];"
    )));
}

#[test]
fn source_model_checker_enforces_tuple_disjointness() {
    assert!(ground_source_holds(
        "class a;\nassert tuple[a] & a <: never;"
    ));
    assert!(ground_source_holds(
        "class a;\nassert tuple[] & tuple[a] <: never;"
    ));
    assert!(!ground_source_holds(
        "class a;\nclass b;\nassert tuple[a] & tuple[b] <: never;"
    ));
}

#[test]
fn canonical_model_checker_rejects_a_missing_hierarchy_edge() {
    let (mut problem, a, b, t) = fixture_problem();
    let lower = atom(
        &mut problem,
        TypeNode::Class(ClassType::plain(a)),
        TypeNode::Flexible(t),
    );
    let upper = atom(
        &mut problem,
        TypeNode::Flexible(t),
        TypeNode::Class(ClassType::plain(b)),
    );
    let formula = AtomFormula::Conjunction(vec![lower, upper]);
    let model = Model {
        entries: vec![ModelEntry {
            metavar: String::from("T"),
            value: model_value(&Input::fixture(&problem), &[&[a]]),
        }],
    };

    assert!(!model_holds(
        ModelInput::Canonical {
            declarations: FIXTURE_DECLARATIONS,
            input: &Input::fixture(&problem),
            formulas: &[&formula],
        },
        &model,
    ));
}

#[test]
fn canonical_model_checker_evaluates_union_nodes() {
    let declarations = "class a; class b; metavar ?T;";
    let mut problem = RawProblem::new(declarations);
    let a = lookup_class(&problem.declarations, "a");
    let b = lookup_class(&problem.declarations, "b");
    let t = lookup_metavar(&problem.declarations, "T");
    let lower = problem.types.intern_class(a, Vec::new());
    let b_type = problem.types.intern_class(b, Vec::new());
    let t_type = problem.types.types().metavar_type(t);
    let upper = problem.types.intern_union(vec![b_type, t_type]);
    let formula = atom_from_ids(&mut problem, lower, upper);
    let accepting = Model {
        entries: vec![ModelEntry {
            metavar: String::from("T"),
            value: model_value(&Input::fixture(&problem), &[&[a]]),
        }],
    };
    let rejecting = Model {
        entries: vec![ModelEntry {
            metavar: String::from("T"),
            value: model_value(&Input::fixture(&problem), &[]),
        }],
    };
    let formulas = [&formula];

    assert!(model_holds(
        ModelInput::Canonical {
            declarations,
            input: &Input::fixture(&problem),
            formulas: &formulas,
        },
        &accepting,
    ));
    assert!(!model_holds(
        ModelInput::Canonical {
            declarations,
            input: &Input::fixture(&problem),
            formulas: &formulas,
        },
        &rejecting,
    ));
}

#[test]
fn core_checker_uses_the_reported_core_units() {
    // Two independent conflicts, {P, Q} and {R, S}: minimization
    // discards P and Q and keeps {R, S}. Checking remainders
    // against the complete unit list would see the discarded
    // {P, Q} conflict and wrongly reject the valid core.
    let mut problem = RawProblem::new("class a; class b;");
    let t = problem.declare_metavar("T");
    let u = problem.declare_metavar("U");
    let a = lookup_class(&problem.declarations, "a");
    let b = lookup_class(&problem.declarations, "b");
    let lower_t = atom(
        &mut problem,
        TypeNode::Class(ClassType::plain(a)),
        TypeNode::Flexible(t),
    );
    let upper_t = atom(
        &mut problem,
        TypeNode::Flexible(t),
        TypeNode::Class(ClassType::plain(b)),
    );
    let lower_u = atom(
        &mut problem,
        TypeNode::Class(ClassType::plain(a)),
        TypeNode::Flexible(u),
    );
    let upper_u = atom(
        &mut problem,
        TypeNode::Flexible(u),
        TypeNode::Class(ClassType::plain(b)),
    );
    let formulas = [lower_t, upper_t, lower_u, upper_u];
    let units = formulas
        .iter()
        .enumerate()
        .map(|(index, formula)| WorkUnit {
            formula,
            label: None,
            span: Span::new(index, index),
        })
        .collect::<Vec<_>>();
    // Only reflexive pairs hold: each conflict pair is
    // unsatisfiable while every singleton is satisfiable.
    let outcome = run_engine(Engine::Dnf, &units, &Input::fixture(&problem));
    let SolveOutcome::Unsatisfiable(core) = &outcome else {
        panic!("expected an unsatisfiable core");
    };
    assert_eq!(core.units().len(), 2);
    let mut rerun = |rest: &[WorkUnit<'_>]| {
        run_dnf(
            rest,
            &Input::fixture(&problem),
            &mut DnfStats::default(),
            &mut SharedStats::default(),
        )
    };
    assert_core_minimal(&units, core, &mut rerun);
}

fn model_value(input: &Input<'_>, arms: &[&[ClassId]]) -> ModelValue {
    let mut description = vec![Description::Union(Vec::new())];
    let mut parts = Vec::new();
    for arm in arms {
        let id = description.len();
        parts.push(id);
        description.push(Description::Intersection(Vec::new()));
        let mut factors = Vec::new();
        for class in *arm {
            factors.push(description.len());
            description.push(Description::Class(ClassType::plain(*class)));
        }
        description[id] = Description::Intersection(factors);
    }
    description[0] = Description::Union(parts);
    described_value(input.declarations(), &description)
}

fn described_value(declarations: &Declarations, description: &[Description]) -> ModelValue {
    let description = description
        .iter()
        .cloned()
        .map(|kind| (kind, Vec::new()))
        .collect::<Vec<_>>();
    let mut values = construct(declarations, &description, &[0]);
    let value = values.remove(0);
    ModelValue::Assigned(AssignedValue {
        value,
        names: Rc::new(DisplayNames {
            reserved: Vec::new(),
        }),
    })
}

fn ground_source_holds(source: &str) -> bool {
    model_holds(
        ModelInput::Source(source),
        &Model {
            entries: Vec::new(),
        },
    )
}

#[test]
fn recursive_union_rendering_names_only_the_referenced_definition() {
    let problem = RawProblem::new("class A; class Box[+T];");
    let a = lookup_class(&problem.declarations, "A");
    let box_class = lookup_class(&problem.declarations, "Box");
    let value = described_value(
        &problem.declarations,
        &[
            Description::Union(vec![1, 2]),
            Description::Class(ClassType::plain(a)),
            Description::Class(ClassType {
                class: box_class,
                arguments: vec![0],
            }),
        ],
    );
    assert_eq!(value.render(), "mu R0. (A | Box[R0])");
}

#[test]
fn recursive_generic_rendering_keeps_its_binder_and_avoids_existing_names() {
    let problem = RawProblem::new("class R0; class T0;");
    let nodes = [
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
        (
            Description::Bound {
                owner: 0,
                position: 0,
            },
            vec![0],
        ),
        (Description::Reference(0), vec![0]),
    ];
    let mut values = construct(&problem.declarations, &nodes, &[0]);
    let value = AssignedValue {
        value: values.remove(0),
        names: Rc::new(DisplayNames {
            reserved: vec![String::from("R1"), String::from("T1")],
        }),
    };
    assert_eq!(value.render(), "mu R2. forall T2. (T2) -> R2");
}

#[test]
fn public_value_equality_uses_class_names_from_its_own_graph() {
    let first = RawProblem::new("class A;");
    let second = RawProblem::new("class B; class A;");
    let first_a = lookup_class(&first.declarations, "A");
    let second_a = lookup_class(&second.declarations, "A");
    let left = described_value(
        &first.declarations,
        &[Description::Class(ClassType::plain(first_a))],
    );
    let right = described_value(
        &second.declarations,
        &[Description::Class(ClassType::plain(second_a))],
    );
    assert_eq!(left, right);
    let ModelValue::Assigned(left) = &left else {
        panic!("the first class has an assigned value");
    };
    let ModelValue::Assigned(right) = &right else {
        panic!("the second class has an assigned value");
    };
    let occurrences = HashSet::from([left.id(), right.id()]);
    assert_eq!(occurrences.len(), 2);
    assert!(occurrences.contains(&left.clone().id()));
    assert!(occurrences.contains(&right.clone().id()));
}

#[test]
fn open_generic_children_render_from_every_saved_outer_owner() {
    for (source, depth, expected) in [
        (
            "metavar ?M; assert forall X. (X) -> forall Y. (Y) -> X <: ?M;",
            1,
            "forall T1. (T1) -> T0",
        ),
        (
            "metavar ?M;
             assert forall X. (X) -> forall Y. (Y) -> forall Z. (Z) -> X <: ?M;",
            2,
            "forall T2. (T2) -> T0",
        ),
    ] {
        let file = validate_ok(source);
        let SolveOutcome::Satisfiable(model) =
            run_engine(Engine::Direct, &work_units(&file), &Input::new(&file))
        else {
            panic!("the nested callable is a complete assignment for M");
        };
        let ModelValue::Assigned(root) = &model.entries[0].value else {
            panic!("M has the nested callable assignment");
        };
        assert!(root.binding_scope().is_empty());
        let mut value = root.clone();
        let mut owners = Vec::new();
        for _ in 0..depth {
            let owner = value.clone();
            let AssignedNode::Generic { body, .. } = value.node() else {
                panic!("each enclosing callable retains its parameter");
            };
            owners.push(owner);
            value = body.ret;
        }
        let saved = value.binding_scope();
        assert_eq!(saved.len(), owners.len());
        assert!(
            saved
                .iter()
                .zip(&owners)
                .all(|(saved, owner)| saved.same_binding(owner))
        );
        let owner = value.clone();
        let AssignedNode::Generic { parameters, body } = value.node() else {
            panic!("the queried child retains its own parameter");
        };
        assert_eq!(parameters, 1);
        let AssignedNode::Bound {
            owner: parameter,
            position,
        } = body.params[0].node()
        else {
            panic!("the child's argument refers to its own parameter");
        };
        assert_eq!(position, 0);
        assert!(parameter.same_binding(&owner));
        let AssignedNode::Bound {
            owner: returned,
            position,
        } = body.ret.node()
        else {
            panic!("the child returns the outermost parameter");
        };
        assert_eq!(position, 0);
        assert!(returned.same_binding(&owners[0]));
        assert_eq!(value.render(), expected);
        assert!(model_holds(ModelInput::Source(source), &model));
    }
}

#[test]
fn a_shared_parameter_keeps_its_shorter_scope_under_an_inner_binder() {
    let source = "metavar ?M; assert forall X. (X) -> forall Y. (Y) -> X <: ?M;";
    let file = validate_ok(source);
    let nodes = [
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
        (
            Description::Bound {
                owner: 0,
                position: 0,
            },
            vec![0],
        ),
        (
            Description::Generic {
                parameters: 1,
                body: Callable {
                    params: vec![3],
                    ret: 1,
                },
            },
            vec![0],
        ),
        (
            Description::Bound {
                owner: 2,
                position: 0,
            },
            vec![0, 2],
        ),
    ];
    let mut values = construct(file.declarations(), &nodes, &[0]);
    let value = AssignedValue {
        value: values.remove(0),
        names: Rc::new(DisplayNames {
            reserved: Vec::new(),
        }),
    };
    let owner = value.clone();
    let AssignedNode::Generic { body, .. } = value.node() else {
        panic!("the constructed root is a generic callable");
    };
    let AssignedNode::Generic { body: inner, .. } = body.ret.node() else {
        panic!("the constructed return is a generic callable");
    };
    assert_eq!(body.params[0].id(), inner.ret.id());
    let AssignedNode::Bound {
        owner: returned,
        position,
    } = inner.ret.node()
    else {
        panic!("the inner return is the shared outer parameter");
    };
    assert_eq!(position, 0);
    assert!(returned.same_binding(&owner));
    assert!(HashSet::from([owner.id()]).contains(&returned.id()));
    let saved = inner.ret.binding_scope();
    assert_eq!(saved.len(), 1);
    assert!(saved[0].same_binding(&owner));
    let model = Model {
        entries: vec![ModelEntry {
            metavar: String::from("M"),
            value: ModelValue::Assigned(value),
        }],
    };
    assert!(model_holds(ModelInput::Source(source), &model));
}

#[test]
fn a_mutually_recursive_child_gets_a_name_for_its_separate_self_loop() {
    let problem = RawProblem::new("");
    let value = described_value(
        &problem.declarations,
        &[
            Description::Tuple(vec![0, 1]),
            Description::Callable(Callable {
                params: vec![1],
                ret: 0,
            }),
        ],
    );
    let ModelValue::Assigned(value) = &value else {
        panic!("the fixture has an assigned value");
    };
    let AssignedNode::Tuple(children) = value.node() else {
        panic!("the root definition is a tuple");
    };
    let AssignedNode::Callable(body) = children[1].node() else {
        panic!("the tuple's second child is a callable");
    };
    assert_eq!(body.params[0].id(), children[1].id());
    assert_eq!(body.ret.id(), value.id());
    assert_eq!(value.render(), "mu R0. tuple[R0, mu R1. (R1) -> R0]");
    assert_eq!(value, &value.clone());
}

#[test]
fn a_finite_prefix_merged_with_its_recursive_child_gets_a_name() {
    let problem = RawProblem::new("");
    let value = described_value(
        &problem.declarations,
        &[Description::Tuple(vec![1]), Description::Tuple(vec![1])],
    );
    let ModelValue::Assigned(assigned) = &value else {
        panic!("the fixture has an assigned value");
    };
    // Both tuple definitions have the same key. Child queries reuse the root
    // handle, so this loop needs a name even if the original root had no back edge.
    let AssignedNode::Tuple(children) = assigned.node() else {
        panic!("the root definition is a tuple");
    };
    assert_eq!(assigned.id(), children[0].id());
    assert_eq!(value.render(), "mu R0. tuple[R0]");
}

#[test]
fn retained_transfer_has_a_valid_model_outside_the_search_alternatives() {
    let source = include_str!("../../../tests/data/solve/unsat/class_retained_transfer.input");
    let problem = RawProblem::new("class Inv[T]; metavar ?M;");
    let inv = lookup_class(&problem.declarations, "Inv");
    let model = Model {
        entries: vec![ModelEntry {
            metavar: String::from("M"),
            value: described_value(
                &problem.declarations,
                &[
                    Description::Callable(Callable {
                        params: vec![1],
                        ret: 1,
                    }),
                    Description::Class(ClassType {
                        class: inv,
                        arguments: vec![2],
                    }),
                    Description::Never,
                ],
            ),
        }],
    };
    assert!(model_holds(ModelInput::Source(source), &model));
}

#[test]
fn a_recursive_generic_lower_can_select_object() {
    let source = "class A; class B; metavar ?G;
        assert forall Z. (?G | Z) -> A <: ?G;
        assert forall V. (?G | V) -> B <: ?G;";
    let file = validate_ok(source);
    let SolveOutcome::Satisfiable(mut model) =
        run_engine(Engine::Direct, &work_units(&file), &Input::new(&file))
    else {
        panic!("the two recursive generic equations have a witness");
    };
    let a = lookup_class(file.declarations(), "A");
    let b = lookup_class(file.declarations(), "B");
    // Each arm has a function that uses its enclosing parameter. This differs
    // from the source equation. Selecting object for Z and V still satisfies
    // the source: each selected function accepts object and has the required
    // return type. Every parameter type in the corresponding upper arm is
    // below object.
    let nodes = [
        (Description::Union(vec![1, 2]), vec![]),
        (
            Description::Generic {
                parameters: 1,
                body: Callable {
                    params: vec![3],
                    ret: 9,
                },
            },
            vec![],
        ),
        (
            Description::Generic {
                parameters: 1,
                body: Callable {
                    params: vec![4],
                    ret: 10,
                },
            },
            vec![],
        ),
        (Description::Union(vec![5, 1, 7]), vec![1]),
        (Description::Union(vec![6, 8, 2]), vec![2]),
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
        (
            Description::Callable(Callable {
                params: vec![3],
                ret: 10,
            }),
            vec![1],
        ),
        (
            Description::Callable(Callable {
                params: vec![4],
                ret: 9,
            }),
            vec![2],
        ),
        (Description::Class(ClassType::plain(a)), vec![]),
        (Description::Class(ClassType::plain(b)), vec![]),
    ];
    let mut values = construct(file.declarations(), &nodes, &[0]);
    model.entries[0].value = ModelValue::Assigned(AssignedValue {
        value: values.remove(0),
        names: Rc::new(DisplayNames {
            reserved: Vec::new(),
        }),
    });
    assert!(model_holds(ModelInput::Source(source), &model));
}
