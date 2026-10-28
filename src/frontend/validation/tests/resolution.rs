//! Tests for declaration checks, reference resolution, generic scopes, and error spans.

use crate::frontend::test_support::{lookup_class, lookup_metavar};
use crate::frontend::validation::{Callable, Generic};

use crate::frontend::diagnostic::{ClassArgumentMismatch, RefKind};

use super::super::super::parse;
use super::super::declarations::Variance;
use super::super::{
    BTreeSet, BoundRef, ClassType, DiagnosticKind, NameKind, Span, TemplateType, TypeNode, collect,
};
use super::{collect_err, resolve_err, resolve_ok, resolved_atom, resolved_lowers};

#[test]
fn class_application_root_errors_precede_argument_resolution() {
    for source in [
        "assert Undeclared[A] <: object;",
        "class B extends Undeclared[forall X. (X) -> X];",
    ] {
        let diagnostic = resolve_err(source);
        assert_eq!(
            *diagnostic.kind(),
            DiagnosticKind::UndeclaredName {
                kind: RefKind::Class,
                name: String::from("Undeclared"),
            }
        );
        assert_eq!(
            &source[diagnostic.span().start()..diagnostic.span().end()],
            "Undeclared"
        );
    }
    let source = "assert forall X <: X[Undeclared]. (X) -> X <: object;";
    let diagnostic = resolve_err(source);
    assert_eq!(
        *diagnostic.kind(),
        DiagnosticKind::ParameterRestriction {
            name: String::from("X"),
        }
    );
    assert_eq!(
        &source[diagnostic.span().start()..diagnostic.span().end()],
        "X"
    );
}

#[test]
fn class_metadata_keeps_unused_parameters_and_root_scope() {
    let source = "class T[U]; class B[T, + # co\nV, -W] extends T[object];";
    let resolved = resolve_ok(source);
    let (b, t) = (
        lookup_class(&resolved.declarations, "B"),
        lookup_class(&resolved.declarations, "T"),
    );
    let parameters = resolved
        .declarations
        .class_parameters(b)
        .collect::<Vec<_>>();
    assert_eq!(
        parameters
            .iter()
            .map(|parameter| parameter.name())
            .collect::<Vec<_>>(),
        ["T", "V", "W"]
    );
    assert_eq!(resolved.declarations.class_arity(b), 3);
    assert_eq!(parameters[0].variance(), Variance::Invariant);
    assert_eq!(parameters[1].variance(), Variance::Covariant);
    assert_eq!(parameters[2].variance(), Variance::Contravariant);
    for parameter in parameters {
        assert_eq!(
            &source[parameter.span().start()..parameter.span().end()],
            parameter.name()
        );
    }
    let Some(record) = resolved.classes.iter().find(|record| record.id == b) else {
        panic!("expected the resolved B declaration");
    };
    let [superclass] = record.superclasses.as_slice() else {
        panic!("expected one direct superclass");
    };
    let base = &superclass.template;
    assert_eq!(base.class, t);
    assert_eq!(base.arguments, [TemplateType::Class(ClassType::OBJECT)]);
    assert_eq!(
        &source[superclass.span.start()..superclass.span.end()],
        "T[object]"
    );
}

#[test]
fn explicit_class_arity_is_checked_at_every_root_before_contents() {
    for suffix in [
        "assert G <: object;",
        "class B extends G;",
        "class B extends G[G];",
    ] {
        let source = format!("class G[T]; {suffix}");
        let diagnostic = resolve_err(&source);
        assert_eq!(
            *diagnostic.kind(),
            DiagnosticKind::ClassArguments {
                name: String::from("G"),
                mismatch: ClassArgumentMismatch::Missing { expected: 1 }
            }
        );
        assert!(
            diagnostic
                .render("test", &source)
                .ends_with("generic class `G` requires 1 explicit type argument")
        );
    }
    for suffix in [
        "assert G[Undeclared, object] <: object;",
        "class B extends G[Undeclared, object];",
        "class B extends G[G[Undeclared, object]];",
    ] {
        let source = format!("class G[T]; {suffix}");
        let diagnostic = resolve_err(&source);
        assert_eq!(
            *diagnostic.kind(),
            DiagnosticKind::ClassArguments {
                name: String::from("G"),
                mismatch: ClassArgumentMismatch::Count {
                    expected: 1,
                    actual: 2
                }
            }
        );
        assert!(
            diagnostic
                .render("test", &source)
                .ends_with("class `G` requires 1 type argument, found 2")
        );
    }
    for (suffix, message) in [
        (
            "assert G <: object;",
            "generic class `G` requires 2 explicit type arguments",
        ),
        (
            "assert G[object] <: object;",
            "class `G` requires 2 type arguments, found 1",
        ),
    ] {
        let source = format!("class G[T, U]; {suffix}");
        assert!(
            resolve_err(&source)
                .render("test", &source)
                .ends_with(message)
        );
    }
    for name in ["Plain", "object", "never"] {
        let diagnostic = resolve_err(&format!(
            "class Plain; assert {name}[Undeclared] <: object;"
        ));
        assert_eq!(
            *diagnostic.kind(),
            DiagnosticKind::ClassArguments {
                name: name.to_owned(),
                mismatch: ClassArgumentMismatch::Unexpected
            }
        );
    }
    let diagnostic = resolve_err("class Plain; class B extends Plain[?Undeclared];");
    assert_eq!(
        *diagnostic.kind(),
        DiagnosticKind::ClassArguments {
            name: String::from("Plain"),
            mismatch: ClassArgumentMismatch::Unexpected
        }
    );
    let diagnostic = resolve_err("class T[U]; class B[T] extends T[T[object]];");
    assert_eq!(
        *diagnostic.kind(),
        DiagnosticKind::ParameterClassApplication {
            name: String::from("T")
        }
    );
}

#[test]
fn ordinary_class_arguments_keep_positions_and_shared_identity() {
    let resolved = resolve_ok(
        "class Pair[T, U]; metavar ?M; assert Pair[?M, forall X. (X) -> X] <: object; assert Pair[forall Y. (Y) -> Y, ?M] <: object; assert Pair[?M, forall Z. (Z) -> Z] <: object; assert Pair[?M, ?M] <: object;",
    );
    let types = resolved_lowers(&resolved);
    assert_eq!(types[0], types[2]);
    assert_ne!(types[0], types[1]);
    let m = lookup_metavar(&resolved.declarations, "M");
    let mut metavars = BTreeSet::new();
    resolved.types.collect_metavars(types[1], &mut metavars);
    assert_eq!(metavars, BTreeSet::from([m]));
    let TypeNode::Class(application) = resolved.types.type_node(types[3]) else {
        panic!("expected class application");
    };
    assert_eq!(application.arguments, [resolved.types.metavar_type(m); 2]);
}

#[test]
fn class_arguments_participate_in_forall_liveness_and_remapping() {
    let resolved = resolve_ok(
        "class Pair[T, U]; assert forall X, Y. (Pair[X, Y]) -> Pair[Y, X] <: object; assert forall Y, X. (Pair[X, Y]) -> Pair[Y, X] <: object;",
    );
    let types = resolved_lowers(&resolved);
    assert_ne!(types[0], types[1]);
    let TypeNode::Generic(Generic { parameters, .. }) = resolved.types.type_node(types[0]) else {
        panic!("expected live binder");
    };
    assert_eq!(parameters.get(), 2);
    let diagnostic =
        resolve_err("class Box[T]; assert forall X. (Box[object | X]) -> object <: object;");
    assert_eq!(
        *diagnostic.kind(),
        DiagnosticKind::UnusedTypeParameter {
            name: String::from("X")
        }
    );
}

#[test]
fn closed_class_argument_restrictions_preserve_outer_body_references() {
    let resolved = resolve_ok(
        "class A; class Box[T]; assert forall O. (O) -> (forall X <: Box[A]. (tuple[O, Box[X]]) -> Box[X]) <: object; assert forall O. (O) -> (forall X. (tuple[O, Box[X & Box[A]]]) -> Box[X & Box[A]]) <: object; assert forall O. (O) -> (forall X in {Box[A]}. (tuple[O, Box[X]]) -> Box[X]) <: object; assert forall O. (O) -> ((tuple[O, Box[Box[A]]]) -> Box[Box[A]]) <: object; assert forall O. (O) -> (forall X in {Box[A]}. (forall Y. (Y) -> tuple[O, Box[X]]) -> Box[X]) <: object; assert forall O. (O) -> ((forall Y. (Y) -> tuple[O, Box[Box[A]]]) -> Box[Box[A]]) <: object;",
    );
    let types = resolved_lowers(&resolved);
    let (pairs, remaining) = types.as_chunks::<2>();
    assert!(
        remaining.is_empty(),
        "expected explicit and rewritten pairs"
    );
    for [rewritten, explicit] in pairs {
        assert_eq!(rewritten, explicit);
    }
    let diagnostic =
        resolve_err("class Box[T]; assert forall X <: Box[?Missing]. (X) -> X <: object;");
    assert_eq!(
        *diagnostic.kind(),
        DiagnosticKind::MetavarParameterRestriction {
            name: String::from("Missing")
        }
    );
    let diagnostic = resolve_err(
        "class Box[T]; assert forall X <: Box[forall Y. (Y) -> Y]. (X) -> X <: object;",
    );
    assert_eq!(
        *diagnostic.kind(),
        DiagnosticKind::GenericParameterRestriction
    );
    let diagnostic = resolve_err("class Box[T]; assert forall X <: Box[X]. (X) -> X <: object;");
    assert_eq!(
        *diagnostic.kind(),
        DiagnosticKind::ParameterRestriction {
            name: String::from("X")
        }
    );
    let diagnostic = resolve_err("class X[T]; assert forall X. (X[object]) -> X <: object;");
    assert_eq!(
        *diagnostic.kind(),
        DiagnosticKind::ParameterClassApplication {
            name: String::from("X")
        }
    );
}

#[test]
fn collection_keeps_spans() {
    let Ok(parsed) = parse("class b extends a;\nassert x: b <: a;\nclass a;") else {
        panic!("expected source to parse");
    };
    let Ok(collected) = collect(parsed) else {
        panic!("expected source to collect");
    };
    assert_eq!(collected.classes.len(), 2);
    assert_eq!(collected.assertions.len(), 1);
    let first = &collected.classes[0];
    assert_eq!(collected.declarations.class_name(first.id), "b");
    assert_eq!(first.span, Span::new(0, 18));
    assert_eq!(first.superclasses.len(), 1);
    assert_eq!(first.superclasses[0].name.name, "a");
    assert_eq!(first.superclasses[0].span, Span::new(16, 17));
    let second = &collected.classes[1];
    assert_eq!(collected.declarations.class_name(second.id), "a");
    assert_eq!(second.span, Span::new(37, 45));
    assert!(second.superclasses.is_empty());
}

#[test]
fn undeclared_superclass_blames_the_reference() {
    let diagnostic = resolve_err("class b extends missing;");
    assert_eq!(diagnostic.span(), Span::new(16, 23));
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::UndeclaredName {
            kind: RefKind::Class,
            ..
        }
    ));
}

#[test]
fn undeclared_left_term_wins_over_right() {
    let diagnostic = resolve_err("assert x <: y;");
    assert_eq!(diagnostic.span(), Span::new(7, 8));
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::UndeclaredName {
            kind: RefKind::Class,
            ..
        }
    ));
}

#[test]
fn undeclared_right_term_blames_the_reference() {
    let diagnostic = resolve_err("class a; assert a <: y;");
    assert_eq!(diagnostic.span(), Span::new(21, 22));
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::UndeclaredName {
            kind: RefKind::Class,
            ..
        }
    ));
}

#[test]
fn undeclared_metavar_as_left_term() {
    let diagnostic = resolve_err("assert ?T <: a;");
    assert_eq!(diagnostic.span(), Span::new(7, 9));
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::UndeclaredName {
            kind: RefKind::Metavar,
            ..
        }
    ));
}

#[test]
fn undeclared_metavar_as_right_term() {
    let diagnostic = resolve_err("metavar ?T; assert object <: ?U;");
    assert_eq!(diagnostic.span(), Span::new(29, 31));
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::UndeclaredName {
            kind: RefKind::Metavar,
            ..
        }
    ));
}

#[test]
fn undeclared_names_inside_nested_tuples_keep_exact_spans() {
    let diagnostic = resolve_err("class a;\nassert tuple[a, tuple[missing]] <: object;");
    assert_eq!(diagnostic.span(), Span::new(31, 38));
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::UndeclaredName {
            kind: RefKind::Class,
            ..
        }
    ));

    let diagnostic = resolve_err("metavar ?T;\nassert object <: tuple[?T, tuple[?U]];");
    assert_eq!(diagnostic.span(), Span::new(45, 47));
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::UndeclaredName {
            kind: RefKind::Metavar,
            ..
        }
    ));
}

#[test]
fn class_error_beats_earlier_assertion_error() {
    let diagnostic = resolve_err("assert x <: a;\nclass b extends missing;");
    assert_eq!(diagnostic.span(), Span::new(31, 38));
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::UndeclaredName {
            kind: RefKind::Class,
            ..
        }
    ));
}

#[test]
fn forward_references_resolve() {
    let resolved = resolve_ok("assert b <: a;\nclass b extends a;\nclass a;");
    let b = lookup_class(&resolved.declarations, "b");
    let a = lookup_class(&resolved.declarations, "a");
    let [assertion] = resolved.assertions.as_slice() else {
        panic!("expected one assertion");
    };
    let atom = resolved_atom(&resolved, assertion);
    assert_eq!(
        Some(atom.lower),
        resolved
            .types
            .find_type(&TypeNode::Class(ClassType::plain(b)))
    );
    assert_eq!(
        Some(atom.upper),
        resolved
            .types
            .find_type(&TypeNode::Class(ClassType::plain(a)))
    );
}

#[test]
fn builtins_resolve_without_declaration() {
    let resolved = resolve_ok("class a extends object;\nassert a <: never;");
    let object = lookup_class(&resolved.declarations, "object");
    assert_eq!(resolved.classes.len(), 1);
    assert_eq!(resolved.classes[0].superclasses.len(), 1);
    assert_eq!(resolved.classes[0].superclasses[0].template.class, object);
}

#[test]
fn generic_parameter_hides_a_class_name() {
    let resolved = resolve_ok("class X; assert forall X. (X) -> X <: object;");
    let [assertion] = resolved.assertions.as_slice() else {
        panic!("expected one assertion");
    };
    let atom = resolved_atom(&resolved, assertion);
    let TypeNode::Generic(Generic { body, .. }) = resolved.types.type_node(atom.lower) else {
        panic!("expected one generic callable");
    };
    let Callable { params, ret } = body;
    assert!(matches!(
        resolved.types.type_node(params[0]),
        TypeNode::Bound(_)
    ));
    assert!(matches!(resolved.types.type_node(*ret), TypeNode::Bound(_)));
}

#[test]
fn nearest_generic_parameter_wins() {
    let resolved = resolve_ok("class A; assert forall X. (forall X. (X) -> X) -> X <: object;");
    let [assertion] = resolved.assertions.as_slice() else {
        panic!("expected one assertion");
    };
    let atom = resolved_atom(&resolved, assertion);
    let TypeNode::Generic(Generic { body, .. }) = resolved.types.type_node(atom.lower) else {
        panic!("expected outer generic");
    };
    let Callable { params, ret } = body;
    let TypeNode::Generic(Generic {
        body: inner_body, ..
    }) = resolved.types.type_node(params[0])
    else {
        panic!("expected inner generic");
    };
    let Callable {
        params: inner_params,
        ret: inner_ret,
    } = inner_body;
    assert_eq!(
        resolved.types.type_node(inner_params[0]),
        &TypeNode::Bound(BoundRef::new(0, 0))
    );
    assert_eq!(
        resolved.types.type_node(*inner_ret),
        &TypeNode::Bound(BoundRef::new(0, 0))
    );
    assert_eq!(
        resolved.types.type_node(*ret),
        &TypeNode::Bound(BoundRef::new(0, 0))
    );
}

#[test]
fn generic_parameter_names_do_not_change_fixed_position_identity() {
    let resolved = resolve_ok(
        "assert forall X, Y. (X, Y) -> X <: object;
         assert forall A, B. (A, B) -> A <: object;",
    );
    let types = resolved_lowers(&resolved);
    assert_eq!(types[0], types[1]);
}

#[test]
fn reordering_generic_parameter_roles_changes_identity() {
    let resolved = resolve_ok(
        "assert forall X, Y. (X, Y) -> X <: object;\nassert forall Y, X. (X, Y) -> X <: object;",
    );
    let [first, second] = resolved.assertions.as_slice() else {
        panic!("expected two assertions");
    };
    let (first, second) = (
        resolved_atom(&resolved, first),
        resolved_atom(&resolved, second),
    );
    assert_ne!(first.lower, second.lower);
}

#[test]
fn restricted_parameters_share_identity_with_their_rewrites() {
    let resolved = resolve_ok(
        "class A;\nclass B;\n\
         assert forall X <: A. (X) -> X <: object;\n\
         assert forall X. (X & A) -> X & A <: object;\n\
         assert forall X in {A, B}. (X) -> X <: object;\n\
         assert ((A) -> A) & ((B) -> B) <: object;",
    );
    let [upper, explicit_upper, exact, explicit_exact] = resolved.assertions.as_slice() else {
        panic!("expected four assertions");
    };
    let (upper, explicit_upper, exact, explicit_exact) = (
        resolved_atom(&resolved, upper),
        resolved_atom(&resolved, explicit_upper),
        resolved_atom(&resolved, exact),
        resolved_atom(&resolved, explicit_exact),
    );
    assert_eq!(upper.lower, explicit_upper.lower);
    assert_eq!(exact.lower, explicit_exact.lower);
}

#[test]
fn restricted_parameter_names_and_order_do_not_change_identity() {
    let resolved = resolve_ok(
        "class A;\nclass B;\n\
         assert forall X <: A, Y in {A, B}. (X, Y) -> X <: object;\n\
         assert forall Second in {B, A}, First <: A. (First, Second) -> First <: object;",
    );
    let [first, second] = resolved.assertions.as_slice() else {
        panic!("expected two assertions");
    };
    let (first, second) = (
        resolved_atom(&resolved, first),
        resolved_atom(&resolved, second),
    );
    assert_eq!(first.lower, second.lower);
}

#[test]
fn parameter_restriction_errors_follow_source_order_and_scope() {
    let diagnostic = resolve_err("class X;\nclass A;\nassert forall X <: X. (X) -> X <: object;");
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::ParameterRestriction { .. }
    ));

    let diagnostic =
        resolve_err("metavar ?T;\nassert forall X <: Missing | ?T. (X) -> X <: object;");
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::UndeclaredName {
            kind: RefKind::Class,
            ..
        }
    ));

    let diagnostic = resolve_err("metavar ?T;\nassert forall X in {?T}. (X) -> X <: object;");
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::MetavarParameterRestriction { .. }
    ));

    let diagnostic =
        resolve_err("class A;\nassert forall X <: (forall Y. (Y) -> Y). (X) -> X <: object;");
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::GenericParameterRestriction
    ));
}

#[test]
fn restrictions_reject_outer_parameters_before_normalization() {
    for (restriction, name) in [
        ("<: O", "O"),
        ("in {O}", "O"),
        ("<: tuple[O]", "O"),
        ("in {(O) -> A}", "O"),
        ("<: object | O", "O"),
        ("in {never & O}", "O"),
        ("<: O[Missing]", "O"),
        ("<: X", "X"),
    ] {
        let source = format!(
            "class A; class O; assert forall O. (O) -> forall X {restriction}. (X) -> X <: object;"
        );
        let diagnostic = resolve_err(&source);
        assert_eq!(
            diagnostic.kind(),
            &DiagnosticKind::ParameterRestriction {
                name: name.to_owned()
            }
        );
        assert_eq!(
            &source[diagnostic.span().start()..diagnostic.span().end()],
            name
        );
    }
    let diagnostic = resolve_err(
        "class A; assert forall O. (O) -> forall X <: Missing | O. (X) -> X <: object;",
    );
    assert!(
        matches!(diagnostic.kind(), DiagnosticKind::UndeclaredName { name, .. } if name == "Missing")
    );
}

#[test]
fn unused_checks_are_local_to_each_binder_rewrite() {
    resolve_ok("class A;\nassert forall X, Y <: never. (X & Y) -> A <: object;");
    resolve_ok("class A;\nassert forall X in {never}. (forall Y. (Y & X) -> A) -> A <: object;");

    let diagnostic =
        resolve_err("class A;\nassert forall X. (forall Y <: never. (X & Y) -> A) -> A <: object;");
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::UnusedTypeParameter { ref name } if name == "X"
    ));
}

#[test]
fn builtins_cannot_be_generic_parameters() {
    for name in ["object", "never"] {
        let source = format!("assert forall {name}. ({name}) -> {name} <: object;");
        let diagnostic = resolve_err(&source);
        assert!(matches!(
            *diagnostic.kind(),
            DiagnosticKind::BuiltinTypeParameter { .. }
        ));
    }
}

#[test]
fn never_as_superclass_blames_the_mention() {
    let diagnostic = collect_err("class a extends never;");
    assert_eq!(diagnostic.span(), Span::new(16, 21));
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::NeverAsSuperclass
    ));
}

#[test]
fn never_as_term_still_resolves() {
    let resolved = resolve_ok("class a;\nassert a <: never;");
    let [assertion] = resolved.assertions.as_slice() else {
        panic!("expected one assertion");
    };
    let atom = resolved_atom(&resolved, assertion);
    let never = lookup_class(&resolved.declarations, "never");
    assert_eq!(
        Some(atom.upper),
        resolved
            .types
            .find_type(&TypeNode::Class(ClassType::plain(never)))
    );
}

#[test]
fn duplicate_class_blames_the_second_name() {
    let diagnostic = collect_err("class a;\nclass b;\nclass a;");
    assert_eq!(diagnostic.span(), Span::new(24, 25));
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::DuplicateName {
            kind: NameKind::Class,
            ..
        }
    ));
}

#[test]
fn duplicate_metavar_blames_the_second_sigil() {
    let diagnostic = collect_err("metavar ?T;\nmetavar ?T;");
    assert_eq!(diagnostic.span(), Span::new(20, 22));
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::DuplicateName {
            kind: NameKind::Metavar,
            ..
        }
    ));
}

#[test]
fn duplicate_assertion_name_blames_the_second_label() {
    let diagnostic = collect_err("assert foo: a <: b;\nassert foo: a <: b;");
    assert_eq!(diagnostic.span(), Span::new(27, 30));
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::DuplicateName {
            kind: NameKind::AssertionName,
            ..
        }
    ));
}

#[test]
fn duplicate_superclass_blames_the_second_mention() {
    let diagnostic = collect_err("class a extends b, b;");
    assert_eq!(diagnostic.span(), Span::new(19, 20));
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::DuplicateSuperclass { .. }
    ));
}

#[test]
fn redeclared_object_blames_the_name() {
    let diagnostic = collect_err("class object;");
    assert_eq!(diagnostic.span(), Span::new(6, 12));
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::BuiltinRedeclared { .. }
    ));
}

#[test]
fn redeclared_never_blames_the_name() {
    let diagnostic = collect_err("class never;");
    assert_eq!(diagnostic.span(), Span::new(6, 11));
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::BuiltinRedeclared { .. }
    ));
}

#[test]
fn restrictions_rewrite_to_existing_type_forms() {
    for (actual, expected) in [
        ("forall X <: A. (X) -> X", "forall X. (X & A) -> (X & A)"),
        ("forall X <: object. (X) -> X", "forall X. (X) -> X"),
        ("forall X <: never. (X) -> X", "(never) -> never"),
        ("forall X in {A, B}. (X) -> X", "((A) -> A) & ((B) -> B)"),
        ("forall X in {A, A}. (X) -> X", "(A) -> A"),
    ] {
        let source =
            format!("class A; class B; assert {actual} <: object; assert {expected} <: object;");
        let resolved = resolve_ok(&source);
        let lowers = resolved_lowers(&resolved);
        let [actual_type, expected_type] = lowers.as_slice() else {
            panic!("expected two resolved assertions");
        };
        assert_eq!(
            actual_type, expected_type,
            "restriction rewrite differs for {actual}"
        );
    }
}

#[test]
fn closed_restriction_rewrites_preserve_outer_body_bindings() {
    for (actual, expected) in [
        (
            "forall U. (U) -> (forall X in {A}. (X) -> U)",
            "forall U. (U) -> ((A) -> U)",
        ),
        (
            "forall U. () -> (forall X <: A. (X & U) -> (forall Y. (X) -> Y))",
            "forall U. () -> (forall X. ((X & A) & U) -> (forall Y. (X & A) -> Y))",
        ),
    ] {
        let source = format!("class A; assert {actual} <: object; assert {expected} <: object;");
        let resolved = resolve_ok(&source);
        let lowers = resolved_lowers(&resolved);
        let [actual_type, expected_type] = lowers.as_slice() else {
            panic!("expected two resolved assertions");
        };
        assert_eq!(
            actual_type, expected_type,
            "outer reference rewrite differs for {actual}"
        );
    }
}

#[test]
fn exact_rewrite_compacts_outer_positions_inside_a_nested_binder() {
    let resolved = resolve_ok(
        "class A; class B;
         assert forall X in {A, B}, Y. (X, Y) -> forall Z. (Z) -> tuple[X, Y, Z] <: object;
         assert (forall Y. (A, Y) -> forall Z. (Z) -> tuple[A, Y, Z])
              & (forall Y. (B, Y) -> forall Z. (Z) -> tuple[B, Y, Z]) <: object;",
    );
    let lowers = resolved_lowers(&resolved);
    let [restricted, expanded] = lowers.as_slice() else {
        panic!("expected the restricted type and its explicit expansion");
    };
    assert_eq!(restricted, expanded);
}

#[test]
fn multiple_exact_sets_expand_the_complete_cartesian_product() {
    let expected = [("A", "A"), ("A", "B"), ("B", "A"), ("B", "B")]
        .into_iter()
        .map(|(first, second)| {
            format!("(forall Z. ({first}, {second}, Z & C) -> tuple[{first}, {second}, Z & C])")
        })
        .collect::<Vec<_>>()
        .join(" & ");
    let source = format!(
        "class A; class B; class C; assert forall X in {{A, B}}, Y in {{A, B}}, Z <: C. (X, Y, Z) -> tuple[X, Y, Z] <: object; assert {expected} <: object;"
    );
    let resolved = resolve_ok(&source);
    let lowers = resolved_lowers(&resolved);
    let [actual_type, expected_type] = lowers.as_slice() else {
        panic!("expected two resolved assertions");
    };
    assert_eq!(actual_type, expected_type);
}
