//! Tests for interned formulas, shared atom identity, source spans, and core unit boundaries.

use crate::frontend::test_support::{lookup_class, lookup_metavar};
use crate::frontend::validation::Callable;

use std::collections::{BTreeMap, BTreeSet};

use crate::frontend::ast::{Formula, TypeExpr};

use super::super::super::parse;
use super::super::ClassType;
use super::super::{
    Atom, AtomFormula, ClassId, Declaration, MetaVarId, Span, TypeId, TypeNode, TypeStore,
};
use super::order_ok;
use crate::frontend::ValidatedFile;

fn parsed_type_member(
    type_expr: &TypeExpr,
    classes: &BTreeMap<&str, bool>,
    metavars: &BTreeMap<&str, bool>,
) -> bool {
    match type_expr {
        TypeExpr::Name(ident) => classes.get(ident.name.as_str()).copied().unwrap_or(false),
        TypeExpr::MetaName(ident) => metavars.get(ident.name.as_str()).copied().unwrap_or(false),
        TypeExpr::ClassApplication(_)
        | TypeExpr::Tuple(_)
        | TypeExpr::Callable(_)
        | TypeExpr::Generic(_) => {
            panic!("constructor type reached the class-only canonicalization checker")
        }
        TypeExpr::Union(node) => node
            .operands()
            .any(|child| parsed_type_member(child, classes, metavars)),
        TypeExpr::Intersection(node) => node
            .operands()
            .all(|child| parsed_type_member(child, classes, metavars)),
        TypeExpr::Paren(node) => parsed_type_member(&node.inner, classes, metavars),
    }
}

fn canonical_type_member(
    type_id: TypeId,
    types: &TypeStore,
    classes: &BTreeMap<ClassId, bool>,
    metavars: &BTreeMap<MetaVarId, bool>,
) -> bool {
    match types.type_node(type_id) {
        TypeNode::Bound(_) | TypeNode::Generic(..) => {
            panic!("generic type reached the class-only canonicalization checker")
        }
        TypeNode::Class(application) if application.arguments.is_empty() => {
            classes.get(&application.class).copied().unwrap_or(false)
        }
        TypeNode::Flexible(id) => metavars.get(id).copied().unwrap_or(false),
        TypeNode::Tuple(_) | TypeNode::Callable(..) | TypeNode::Class(_) => {
            panic!("constructor type reached the class-only canonicalization checker")
        }
        TypeNode::Union(children) => children
            .iter()
            .any(|child| canonical_type_member(*child, types, classes, metavars)),
        TypeNode::Intersection(children) => children
            .iter()
            .all(|child| canonical_type_member(*child, types, classes, metavars)),
    }
}

fn assert_type_canonicalization(expression: &str) {
    let source = format!(
        "class zebra;\nclass apple;\nmetavar ?T;\nmetavar ?U;\nassert {expression} <: object;"
    );
    let Ok(parsed) = parse(&source) else {
        panic!("expected source to parse");
    };
    let Some(Declaration::Assert(assertion)) = parsed.declarations().last() else {
        panic!("expected a parsed assertion");
    };
    let Formula::Subtype(parsed_atom) = &assertion.formula else {
        panic!("expected a parsed subtype");
    };
    let validated = order_ok(&source);
    let [assertion] = validated.assertions() else {
        panic!("expected one validated assertion");
    };
    let [unit] = assertion.units.as_slice() else {
        panic!("expected one validated unit");
    };
    let AtomFormula::Atom(atom) = &unit.formula else {
        panic!("expected one validated atom");
    };
    let canonical = validated.atoms().atom(*atom).lower;
    let (zebra, apple, t, u) = (
        lookup_class(validated.declarations(), "zebra"),
        lookup_class(validated.declarations(), "apple"),
        lookup_metavar(validated.declarations(), "T"),
        lookup_metavar(validated.declarations(), "U"),
    );

    for bits in 0u8..16 {
        let classes = BTreeMap::from([
            (ClassId::OBJECT, true),
            (ClassId::NEVER, false),
            (zebra, bits & 1 != 0),
            (apple, bits & 2 != 0),
        ]);
        let parsed_classes = BTreeMap::from([
            ("object", true),
            ("never", false),
            ("zebra", bits & 1 != 0),
            ("apple", bits & 2 != 0),
        ]);
        let metavars = BTreeMap::from([(t, bits & 4 != 0), (u, bits & 8 != 0)]);
        let parsed_metavars = BTreeMap::from([("T", bits & 4 != 0), ("U", bits & 8 != 0)]);
        assert_eq!(
            parsed_type_member(&parsed_atom.left, &parsed_classes, &parsed_metavars),
            canonical_type_member(canonical, validated.types(), &classes, &metavars),
            "membership differs for {expression:?} at bit pattern {bits:04b}"
        );
    }
}

#[test]
fn formula_parentheses_are_excluded_from_unit_spans() {
    let validated = order_ok("class a;\nclass b;\nassert ((a <: b));");
    let [assertion] = validated.assertions() else {
        panic!("expected one assertion");
    };
    let [unit] = assertion.units.as_slice() else {
        panic!("expected one unit");
    };
    let AtomFormula::Atom(_) = &unit.formula else {
        panic!("expected an atom without formula parentheses");
    };
    assert_eq!(unit.span, Span::new(27, 33));
}

#[test]
fn type_parentheses_and_rewritten_endpoints_keep_unit_spans() {
    let source =
        "assert saved: (((forall X <: never. (X) -> X) <: (object)) and (object <: object));";
    let validated = order_ok(source);
    let [assertion] = validated.assertions() else {
        panic!("expected one assertion");
    };
    let [first, second] = assertion.units.as_slice() else {
        panic!("expected two core units");
    };
    let AtomFormula::Atom(atom) = &first.formula else {
        panic!("expected a subtype atom");
    };
    assert_eq!(
        &source[first.span.start()..first.span.end()],
        "(forall X <: never. (X) -> X) <: (object)"
    );
    assert_eq!(
        &source[second.span.start()..second.span.end()],
        "object <: object"
    );
    let never = plain_type(&validated, ClassId::NEVER);
    assert_eq!(
        validated
            .types()
            .type_node(validated.atoms().atom(*atom).lower),
        &TypeNode::Callable(Callable {
            params: vec![never],
            ret: never,
        })
    );
}

#[test]
fn shared_atoms_intern_once_with_distinct_spans() {
    let validated = order_ok("class a;\nclass b;\nassert (a <: b) and (a <: b);");
    let [assertion] = validated.assertions() else {
        panic!("expected one assertion");
    };
    let [first, second] = assertion.units.as_slice() else {
        panic!("expected two units");
    };
    assert_eq!(first.span, Span::new(26, 32));
    assert_eq!(second.span, Span::new(39, 45));
    let AtomFormula::Atom(first) = &first.formula else {
        panic!("expected a subtype atom");
    };
    let AtomFormula::Atom(second) = &second.formula else {
        panic!("expected a subtype atom");
    };
    assert_eq!(*first, *second);
    assert_eq!(validated.atoms().atom_count(), 1);
}

#[test]
fn restriction_rewrite_controls_atom_identity_and_metavariable_use() {
    let validated = order_ok(
        "class A;\nmetavar ?T;\n\
         assert forall X <: never. (X & ?T) -> A <: object;\n\
         assert (never) -> A <: object;",
    );
    let [first, second] = validated.assertions() else {
        panic!("expected two assertions");
    };
    let ([first], [second]) = (first.units.as_slice(), second.units.as_slice()) else {
        panic!("expected one unit per assertion");
    };
    let (AtomFormula::Atom(first), AtomFormula::Atom(second)) = (&first.formula, &second.formula)
    else {
        panic!("expected subtype atoms");
    };
    assert_eq!(*first, *second);
    let t = lookup_metavar(validated.declarations(), "T");
    let atom = validated.atoms().atom(*first);
    let mut metavars = BTreeSet::new();
    validated
        .types()
        .collect_metavars(atom.lower, &mut metavars);
    validated
        .types()
        .collect_metavars(atom.upper, &mut metavars);
    assert!(!metavars.contains(&t));
}

#[test]
fn canonical_union_endpoints_share_atom_ids() {
    let validated = order_ok("class a;\nmetavar ?T;\nassert a | never <: ?T;\nassert a <: ?T;");
    let [first, second] = validated.assertions() else {
        panic!("expected two assertions");
    };
    let [first] = first.units.as_slice() else {
        panic!("expected one first unit");
    };
    let [second] = second.units.as_slice() else {
        panic!("expected one second unit");
    };
    let (AtomFormula::Atom(first), AtomFormula::Atom(second)) = (&first.formula, &second.formula)
    else {
        panic!("expected subtype atoms");
    };

    assert_eq!(*first, *second);
    assert_eq!(validated.atoms().atom_count(), 1);
}

#[test]
fn canonical_intersection_endpoints_share_atom_ids() {
    let validated = order_ok("class a;\nmetavar ?T;\nassert a & object <: ?T;\nassert a <: ?T;");
    let [first, second] = validated.assertions() else {
        panic!("expected two assertions");
    };
    let [first] = first.units.as_slice() else {
        panic!("expected one first unit");
    };
    let [second] = second.units.as_slice() else {
        panic!("expected one second unit");
    };
    let (AtomFormula::Atom(first), AtomFormula::Atom(second)) = (&first.formula, &second.formula)
    else {
        panic!("expected subtype atoms");
    };

    assert_eq!(*first, *second);
    assert_eq!(validated.atoms().atom_count(), 1);
}

#[test]
fn type_canonicalization_preserves_pointwise_membership() {
    for expression in [
        "((?T | zebra) | (never | ?U))",
        "?T | object",
        "zebra | zebra",
        "?T | ?T | never",
        "((?T & zebra) & (object & ?U))",
        "?T & never",
        "zebra & zebra",
        "(zebra | apple) & ?T",
    ] {
        assert_type_canonicalization(expression);
    }
}

#[test]
fn assertions_retain_labels() {
    let validated = order_ok("class a;\nclass b;\nassert named: a <: b;\nassert a <: b;");
    let [first, second] = validated.assertions() else {
        panic!("expected two assertions");
    };
    let Some(label) = &first.label else {
        panic!("expected a label");
    };
    assert_eq!(label, "named");
    assert!(second.label.is_none());
}

#[test]
fn interned_atoms_expose_their_bounds() {
    let validated = order_ok("class a;\nclass b;\nassert a <: b;\nassert b <: a;");
    let [first, second] = validated.assertions() else {
        panic!("expected two assertions");
    };
    let [first] = first.units.as_slice() else {
        panic!("expected one unit");
    };
    let [second] = second.units.as_slice() else {
        panic!("expected one unit");
    };
    let AtomFormula::Atom(first) = &first.formula else {
        panic!("expected a subtype atom");
    };
    let AtomFormula::Atom(second) = &second.formula else {
        panic!("expected a subtype atom");
    };
    assert_ne!(*first, *second);
    let (a, b) = (
        lookup_class(validated.declarations(), "a"),
        lookup_class(validated.declarations(), "b"),
    );
    let a_type = plain_type(&validated, a);
    let b_type = plain_type(&validated, b);
    assert_eq!(
        validated.atoms().atom(*first),
        &Atom {
            lower: a_type,
            upper: b_type,
        }
    );
    assert_eq!(
        validated.atoms().atom(*second),
        &Atom {
            lower: b_type,
            upper: a_type,
        }
    );
}

#[test]
fn nested_connectives_keep_shape_order_and_atoms() {
    let validated = order_ok(
        "class a;\nclass b;\nclass c;\nclass d;\nassert (a <: b) and (c <: d) and ((a <: c) or (b <: d));",
    );
    let [assertion] = validated.assertions() else {
        panic!("expected one assertion");
    };
    let [first, second, third] = assertion.units.as_slice() else {
        panic!("expected three units");
    };
    assert_eq!(first.span, Span::new(44, 50));
    assert_eq!(second.span, Span::new(57, 63));
    assert_eq!(third.span, Span::new(70, 90));
    let AtomFormula::Atom(first) = &first.formula else {
        panic!("expected a subtype atom");
    };
    let AtomFormula::Atom(second) = &second.formula else {
        panic!("expected a subtype atom");
    };
    let AtomFormula::Disjunction(nested) = &third.formula else {
        panic!("expected a disjunction");
    };
    let [left, right] = nested.as_slice() else {
        panic!("expected two operands");
    };
    let AtomFormula::Atom(left) = left else {
        panic!("expected a subtype atom");
    };
    let AtomFormula::Atom(right) = right else {
        panic!("expected a subtype atom");
    };
    let ids = [*first, *second, *left, *right];
    assert_eq!(validated.atoms().atom_count(), 4);
    for (index, id) in ids.iter().enumerate() {
        assert!(
            !ids[..index].contains(id),
            "atom identifiers must be distinct"
        );
    }
}

#[test]
fn outer_parens_split_into_units() {
    let validated = order_ok("class a;\nclass b;\nassert bad: (a <: b and b <: a);");
    let [assertion] = validated.assertions() else {
        panic!("expected one assertion");
    };
    let Some(label) = &assertion.label else {
        panic!("expected a label");
    };
    assert_eq!(label, "bad");
    let [first, second] = assertion.units.as_slice() else {
        panic!("expected two units");
    };
    assert_eq!(first.span, Span::new(31, 37));
    assert_eq!(second.span, Span::new(42, 48));
    let AtomFormula::Atom(first) = &first.formula else {
        panic!("expected a subtype atom");
    };
    let AtomFormula::Atom(second) = &second.formula else {
        panic!("expected a subtype atom");
    };
    assert_ne!(*first, *second);
}

#[test]
fn disjunction_forms_one_whole_span_unit() {
    let validated =
        order_ok("class a;\nclass b;\nclass c;\nclass d;\nassert (a <: b) or (c <: d);");
    let [assertion] = validated.assertions() else {
        panic!("expected one assertion");
    };
    let [unit] = assertion.units.as_slice() else {
        panic!("expected one unit");
    };
    assert_eq!(unit.span, Span::new(43, 63));
    let AtomFormula::Disjunction(children) = &unit.formula else {
        panic!("expected a disjunction");
    };
    assert_eq!(children.len(), 2);
}

#[test]
fn nested_conjunction_stays_whole_in_its_unit() {
    let validated =
        order_ok("class a;\nclass b;\nclass c;\nclass d;\nassert a <: b and (c <: d and d <: c);");
    let [assertion] = validated.assertions() else {
        panic!("expected one assertion");
    };
    let [first, second] = assertion.units.as_slice() else {
        panic!("expected two units");
    };
    assert_eq!(first.span, Span::new(43, 49));
    assert_eq!(second.span, Span::new(55, 72));
    let AtomFormula::Atom(_) = &first.formula else {
        panic!("expected a subtype atom");
    };
    let AtomFormula::Conjunction(nested) = &second.formula else {
        panic!("expected a nested conjunction");
    };
    assert_eq!(nested.len(), 2);
}

#[test]
fn metavar_names_follow_declaration_order() {
    let validated = order_ok("metavar ?U;\nmetavar ?T;");
    let collected: Vec<_> = validated.declarations().metavars().collect();
    assert_eq!(
        collected.iter().map(|(_, name)| *name).collect::<Vec<_>>(),
        ["U", "T"]
    );
    for (id, name) in &collected {
        assert_eq!(validated.declarations().lookup_metavar(name), Some(*id));
    }
}

fn plain_type(file: &ValidatedFile, class: ClassId) -> TypeId {
    let Some(id) = file
        .types()
        .find_type(&TypeNode::Class(ClassType::plain(class)))
    else {
        panic!("fixture plain class has no canonical type");
    };
    id
}
