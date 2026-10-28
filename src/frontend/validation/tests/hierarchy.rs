//! Tests for C3 order, ancestor arguments, variance, and hierarchy diagnostics.

use std::fmt::Write;

use crate::frontend::test_support::lookup_class;

use super::super::classes::render;
use super::super::{DiagnosticKind, Span, TemplateType};
use super::{collect_err, last_start, order_err, order_ok, resolve_err, resolve_ok};

#[test]
fn superclass_source_scan_precedes_all_argument_resolution() {
    let source = "class G[T, U]; class B extends G[Undeclared, tuple[?Missing | object]];";
    let diagnostic = resolve_err(source);
    assert_eq!(
        *diagnostic.kind(),
        DiagnosticKind::MetavarSuperclassArgument {
            name: String::from("Missing")
        }
    );
    assert_eq!(
        &source[diagnostic.span().start()..diagnostic.span().end()],
        "?Missing"
    );
    let source =
        "class G[T, U]; class B extends G[Undeclared, forall X in {Undeclared}. (X) -> X];";
    let diagnostic = resolve_err(source);
    assert_eq!(
        *diagnostic.kind(),
        DiagnosticKind::GenericSuperclassArgument
    );
    assert_eq!(
        &source[diagnostic.span().start()..diagnostic.span().end()],
        "forall"
    );
    let diagnostic =
        resolve_err("class G[T, U]; class B extends G[tuple[?First], forall X. (X) -> X];");
    assert_eq!(
        *diagnostic.kind(),
        DiagnosticKind::MetavarSuperclassArgument {
            name: String::from("First")
        }
    );
    let diagnostic = resolve_err("class G[T, U]; class B extends G[forall X. (X) -> X, ?Second];");
    assert_eq!(
        *diagnostic.kind(),
        DiagnosticKind::GenericSuperclassArgument
    );
    let diagnostic = collect_err(
        "class G[T]; class B extends G[forall X. (X) -> X]; class C extends object, object;",
    );
    assert_eq!(
        *diagnostic.kind(),
        DiagnosticKind::DuplicateSuperclass {
            name: String::from("object")
        }
    );
    let diagnostic = collect_err(
        "class G[T]; class B extends G[forall X. (X) -> X]; class C extends never[?Missing];",
    );
    assert_eq!(*diagnostic.kind(), DiagnosticKind::NeverAsSuperclass);
}

#[test]
fn ancestor_templates_compose_and_normalize_in_c3_order() {
    let ordered = order_ok(
        "class Root[+T]; class Left[+T] extends Root[tuple[T | never]]; class Right[+T] extends Root[tuple[never | T]]; class Join[+T] extends Left[T], Right[T]; class Leaf extends Join[object | never];",
    );
    let leaf = lookup_class(ordered.declarations(), "Leaf");
    let ancestors = ordered
        .hierarchy
        .ancestors(leaf)
        .iter()
        .map(|template| {
            (
                ordered.declarations().class_name(template.class),
                template
                    .arguments
                    .iter()
                    .map(|argument| render(argument, ordered.declarations()))
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        ancestors,
        [
            ("Join", vec![String::from("object")]),
            ("Left", vec![String::from("object")]),
            ("Right", vec![String::from("object")]),
            ("Root", vec![String::from("tuple[object]")]),
            ("object", vec![])
        ]
    );
    let join = lookup_class(ordered.declarations(), "Join");
    let root_class = lookup_class(ordered.declarations(), "Root");
    let Some(root) = ordered
        .hierarchy
        .ancestors(join)
        .iter()
        .find(|template| template.class == root_class)
    else {
        panic!("expected root template");
    };
    let [TemplateType::Tuple(children)] = root.arguments.as_slice() else {
        panic!("expected composed tuple");
    };
    let [TemplateType::Parameter { reference }] = children.as_slice() else {
        panic!("expected descendant parameter");
    };
    assert_eq!(reference.owner, join);
    assert_eq!(reference.position, 0);
}

#[test]
fn repeated_ancestors_require_structural_equality_at_all_variances() {
    for sign in ["", "+", "-"] {
        let source = format!(
            "class Root[{sign}T]; class A; class B extends A; class Left extends Root[A]; class Right extends Root[B]; class Join extends Left, Right;"
        );
        let diagnostic = order_err(&source);
        assert_eq!(
            *diagnostic.kind(),
            DiagnosticKind::ConflictingAncestorArguments {
                name: String::from("Root"),
                first: vec![String::from("A")].into_boxed_slice(),
                second: vec![String::from("B")].into_boxed_slice()
            }
        );
        assert_eq!(diagnostic.span().start(), last_start(&source, "Right"));
    }
    // Parameter positions differ even if a later application could use equal arguments.
    let diagnostic = order_err(
        "class Root[T]; class L[X] extends Root[X]; class R[Y] extends Root[Y]; class Join[X, Y] extends L[X], R[Y];",
    );
    assert_eq!(
        *diagnostic.kind(),
        DiagnosticKind::ConflictingAncestorArguments {
            name: String::from("Root"),
            first: vec![String::from("X")].into_boxed_slice(),
            second: vec![String::from("Y")].into_boxed_slice()
        }
    );
    let ordered = order_ok(
        "class Root[T]; class A; class B; class L extends Root[A | (never | B)]; class R extends Root[B | A | A]; class Join extends L, R;",
    );
    assert_eq!(ordered.declarations().user_class_count(), 6);
}

#[test]
fn ancestor_conflicts_follow_source_order_and_taint_dependents() {
    let source = "class Dependent extends Later; class First extends LaterBase, EarlierBase; class Later extends EarlierBase, LaterBase; class EarlierBase extends Root[object]; class LaterBase extends Root[never]; class Root[T];";
    let diagnostic = order_err(source);
    assert_eq!(
        *diagnostic.kind(),
        DiagnosticKind::ConflictingAncestorArguments {
            name: String::from("Root"),
            first: vec![String::from("never")].into_boxed_slice(),
            second: vec![String::from("object")].into_boxed_slice()
        }
    );
    assert_eq!(
        diagnostic.span().start(),
        "class Dependent extends Later; class First extends LaterBase, ".len()
    );
}

#[test]
fn nested_class_references_preserve_direct_inheritance_checks() {
    for source in [
        "class Comparable[T]; class Int extends Comparable[Int];",
        "class N[T]; class C extends N[N[C]];",
        "class G[T]; class A extends G[B]; class B extends G[A];",
    ] {
        order_ok(source);
    }
    order_ok("class N[T]; class C[C] extends N[C];");
    let diagnostic = order_err("class N[T]; class C extends N[N[C]]; class Self extends Self;");
    assert_eq!(
        *diagnostic.kind(),
        DiagnosticKind::SelfEdge {
            name: String::from("Self")
        }
    );
    let diagnostic =
        order_err("class N[T]; class C extends N[N[C]]; class A extends B; class B extends A;");
    assert!(matches!(*diagnostic.kind(), DiagnosticKind::Cycle { .. }));
    let diagnostic = order_err(
        "class N[T]; class C extends N[N[C]]; class X; class Y; class A extends X, Y; class B extends Y, X; class Join extends A, B;",
    );
    assert_eq!(
        *diagnostic.kind(),
        DiagnosticKind::InconsistentOrder {
            name: String::from("Join")
        }
    );
}

#[test]
fn normalization_removes_ineffective_class_dependencies() {
    for (argument, expected) in [
        ("object | B", "object"),
        ("B | object", "object"),
        ("never & B", "never"),
        ("B & never", "never"),
        ("tuple[object | B]", "tuple[object]"),
        ("(object | B) -> object", "(object) -> object"),
    ] {
        let ordered = order_ok(&format!(
            "class G[T]; class A extends G[{argument}]; class B extends G[A];"
        ));
        let a = lookup_class(ordered.declarations(), "A");
        let g = lookup_class(ordered.declarations(), "G");
        let template = ordered
            .hierarchy
            .ancestors(a)
            .iter()
            .find(|template| template.class == g)
            .expect("A extends G");
        assert_eq!(
            render(&template.arguments[0], ordered.declarations()),
            expected
        );
    }
    order_ok("class G[T]; class A extends G[object | A];");
}

#[test]
fn declared_variance_uses_normalized_occurrences_and_source_order() {
    order_ok(
        "class Co[+T]; class Contra[-T]; class Inv[T]; class Good[+T, -U, V] extends Co[tuple[Contra[Contra[T]]]], Contra[tuple[U]], Inv[(V) -> V];",
    );
    order_ok("class Co[+T]; class Good[+T] extends Co[((T) -> object) | object];");
    for source in [
        "class Co[+T]; class Bad[-T] extends Co[T];",
        "class Contra[-T]; class Bad[+T] extends Contra[T];",
        "class Inv[T]; class Bad[+T] extends Inv[T];",
        "class Co[+T]; class Bad[+T] extends Co[(T) -> object];",
        "class Co[+T]; class Inv[T]; class Bad[+T] extends Co[tuple[Inv[T]]];",
    ] {
        let diagnostic = order_err(source);
        assert_eq!(
            *diagnostic.kind(),
            DiagnosticKind::ClassParameterVariance {
                name: String::from("T")
            }
        );
    }
    let source = "class Co[+X]; class Bad[-T, -U] extends Co[U | T];";
    let diagnostic = order_err(source);
    assert_eq!(
        *diagnostic.kind(),
        DiagnosticKind::ClassParameterVariance {
            name: String::from("U")
        }
    );
    assert_eq!(diagnostic.span().start(), last_start(source, "U"));
    let diagnostic = order_err(
        "class Co[+X]; class Bad[-T] extends Co[T]; class Root[X]; class L extends Root[object]; class R extends Root[never]; class Join extends L, R;",
    );
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::ConflictingAncestorArguments { .. }
    ));
}

#[test]
fn equal_parameter_uses_keep_the_first_source_span() {
    let source = "class Co[+X]; class Bad[-T] extends Co[T | T];";
    let start = "class Co[+X]; class Bad[-T] extends Co[".len();
    let first = Span::new(start, start + 1);
    let resolved = resolve_ok(source);
    let uses = &resolved.classes[1].superclasses[0].parameter_uses;
    assert_eq!(
        uses.iter().map(|use_| use_.span).collect::<Vec<_>>(),
        [first]
    );
    assert_eq!(order_err(source).span(), first);
}

#[test]
fn self_edge_blames_the_mention() {
    for (source, span) in [
        ("class a extends a;", Span::new(16, 17)),
        ("class a[T] extends a[object];", Span::new(19, 20)),
    ] {
        let diagnostic = order_err(source);
        assert_eq!(diagnostic.span(), span);
        assert!(matches!(
            *diagnostic.kind(),
            DiagnosticKind::SelfEdge { .. }
        ));
    }
}

#[test]
fn self_edge_beats_cycle() {
    let diagnostic = order_err("class a extends b;\nclass b extends a;\nclass c extends c;");
    assert_eq!(diagnostic.span(), Span::new(54, 55));
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::SelfEdge { .. }
    ));
}

#[test]
fn two_cycle_reports_path_and_declaration() {
    let diagnostic = order_err("class a extends b;\nclass b extends a;");
    assert_eq!(diagnostic.span(), Span::new(19, 37));
    let DiagnosticKind::Cycle { path } = diagnostic.kind() else {
        panic!("expected a cycle");
    };
    assert_eq!(path.as_slice(), ["a", "b", "a"]);
}

#[test]
fn three_cycle_reports_path_and_declaration() {
    let diagnostic = order_err("class a extends b;\nclass b extends c;\nclass c extends a;");
    assert_eq!(diagnostic.span(), Span::new(38, 56));
    let DiagnosticKind::Cycle { path } = diagnostic.kind() else {
        panic!("expected a cycle");
    };
    assert_eq!(path.as_slice(), ["a", "b", "c", "a"]);
}

#[test]
fn diamond_linearizes() {
    let ordered =
        order_ok("class a;\nclass b extends a;\nclass c extends a;\nclass d extends b, c;");
    let (d, b, c, a, object) = (
        lookup_class(ordered.declarations(), "d"),
        lookup_class(ordered.declarations(), "b"),
        lookup_class(ordered.declarations(), "c"),
        lookup_class(ordered.declarations(), "a"),
        lookup_class(ordered.declarations(), "object"),
    );
    let linearization = ordered.hierarchy.linearization(d).collect::<Vec<_>>();
    assert_eq!(linearization, [d, b, c, a, object]);
}

#[test]
fn deep_chain_linearizes() {
    let mut source = String::from("class t0;\n");
    for index in 1..200 {
        let _ = writeln!(source, "class t{index} extends t{};", index - 1);
    }
    let ordered = order_ok(&source);
    let last = lookup_class(ordered.declarations(), "t199");
    let object = lookup_class(ordered.declarations(), "object");
    let linearization = ordered.hierarchy.linearization(last).collect::<Vec<_>>();
    assert_eq!(linearization.len(), 201);
    assert_eq!(linearization[0], last);
    assert_eq!(linearization[200], object);
}

#[test]
fn c3_failures_follow_declaration_order_and_taint_dependents() {
    let source = "class Dependent extends Later; class Earlier extends DelayedA, B; class Later extends A, B; class DelayedA extends A; class A extends X, Y; class B extends Y, X; class X; class Y;";
    let diagnostic = order_err(source);
    assert_eq!(
        *diagnostic.kind(),
        DiagnosticKind::InconsistentOrder {
            name: String::from("Earlier")
        }
    );
    assert_eq!(
        &source[diagnostic.span().start()..diagnostic.span().end()],
        "class Earlier extends DelayedA, B;"
    );
}

#[test]
fn crisscross_order_fails() {
    let diagnostic = order_err(
        "class a;\nclass b;\nclass c extends a, b;\nclass d extends b, a;\nclass e extends c, d;",
    );
    assert_eq!(diagnostic.span(), Span::new(62, 83));
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::InconsistentOrder { .. }
    ));
}

#[test]
fn object_first_fails() {
    let diagnostic = order_err("class b;\nclass a extends object, b;");
    assert_eq!(diagnostic.span(), Span::new(9, 35));
    assert!(matches!(
        *diagnostic.kind(),
        DiagnosticKind::InconsistentOrder { .. }
    ));
}

#[test]
fn object_last_linearizes() {
    let ordered = order_ok("class b;\nclass a extends b, object;");
    let (a, b, object) = (
        lookup_class(ordered.declarations(), "a"),
        lookup_class(ordered.declarations(), "b"),
        lookup_class(ordered.declarations(), "object"),
    );
    let linearization = ordered.hierarchy.linearization(a).collect::<Vec<_>>();
    assert_eq!(linearization, [a, b, object]);
}
