//! Frontend: spanned syntax trees with parsing and semantic validation.
//!
//! [`parse`] runs lexical and syntactic analysis over one input file and
//! returns a [`ParsedFile`] or the first [`Diagnostic`]. [`validate`]
//! runs semantic checks over a parsed file and returns a
//! [`ValidatedFile`] or the first [`Diagnostic`].

mod ast;
mod diagnostic;
pub mod problem;
#[cfg(test)]
pub mod test_support;
mod validation;

use lalrpop_util::{ParseError, lalrpop_mod};

#[doc(inline)]
pub use ast::ParsedFile;
#[doc(inline)]
pub use diagnostic::{Diagnostic, Span};
#[doc(inline)]
pub use validation::ValidatedFile;

use ast::parsed_file;
use diagnostic::{DiagnosticKind, ExpectedToken, Found, diagnostic};

lalrpop_mod!(
    #[allow(
        clippy::pedantic,
        clippy::allow_attributes_without_reason,
        clippy::renamed_function_params,
        clippy::if_then_some_else_none,
        reason = "generated parser code"
    )]
    grammar,
    "/frontend/grammar.rs"
);

/// Parse one input file into a spanned syntax tree.
///
/// Runs lexical and syntactic analysis only. No semantic checks apply.
///
/// # Errors
///
/// Returns the first [`Diagnostic`] when analysis fails.
///
/// # Panics
///
/// Panics when generated parser data violates the frontend's terminal or span
/// invariants. Such a failure indicates a programming error in the grammar
/// integration.
pub fn parse(source: &str) -> Result<ParsedFile, Diagnostic> {
    let expected_tokens = |expected: Vec<String>| {
        let mut expected: Vec<ExpectedToken> = expected
            .iter()
            .map(|name| ExpectedToken::from_generated(name))
            .collect();
        expected.sort_unstable();
        expected.dedup();
        expected
    };

    match grammar::DeclarationsParser::new().parse(source) {
        Ok(decls) => Ok(parsed_file(Span::new(0, source.len()), decls)),
        Err(ParseError::InvalidToken { location }) => {
            let Some(ch) = source.get(location..).and_then(|rest| rest.chars().next()) else {
                panic!("generated lexer reported invalid end of input at byte {location}");
            };
            Err(diagnostic(
                Span::new(location, location + ch.len_utf8()),
                DiagnosticKind::IllegalChar(ch),
            ))
        }
        Err(ParseError::UnrecognizedEof { location, expected }) => Err(diagnostic(
            Span::new(location, location),
            DiagnosticKind::UnexpectedToken {
                expected: expected_tokens(expected),
                found: Found::EndOfInput,
            },
        )),
        Err(ParseError::UnrecognizedToken {
            token: (start, _, end),
            expected,
        }) => {
            let Some(spelling) = source.get(start..end) else {
                panic!("generated parser returned invalid token span {start}..{end}");
            };
            Err(diagnostic(
                Span::new(start, end),
                DiagnosticKind::UnexpectedToken {
                    expected: expected_tokens(expected),
                    found: Found::Token(spelling.to_owned()),
                },
            ))
        }
        Err(ParseError::ExtraToken {
            token: (start, _, end),
        }) => {
            let Some(spelling) = source.get(start..end) else {
                panic!("generated parser returned invalid token span {start}..{end}");
            };
            Err(diagnostic(
                Span::new(start, end),
                DiagnosticKind::UnexpectedToken {
                    expected: Vec::new(),
                    found: Found::Token(spelling.to_owned()),
                },
            ))
        }
        Err(ParseError::User { error }) => Err(error),
    }
}

/// Validate one parsed file.
///
/// Checks declarations, resolves references, and checks superclass templates.
/// Declarations move into identifier tables. Each name maps to its identifier.
/// Each user class stores its C3 order and superclass templates. Resolution
/// builds formulas over interned atoms. The validated file is returned only
/// after all whole-file checks pass.
///
/// # Errors
///
/// Returns the first [`Diagnostic`] when validation fails.
pub fn validate(parsed: ParsedFile) -> Result<ValidatedFile, Diagnostic> {
    let collected = validation::collect(parsed)?;
    let resolved = validation::resolve(collected)?;
    validation::order(resolved)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::ast::{
        AssertDecl, ClassDecl, Declaration, Formula, GenericParameterExpr, Ident, Nary, Subtype,
        TypeExpr, into_declarations, parsed_file,
    };
    use super::diagnostic::{DiagnosticKind, ExpectedToken, Span};
    use super::parse;

    fn one_assertion(source: &str) -> AssertDecl {
        let Ok(parsed) = parse(source) else {
            panic!("expected source to parse: {source:?}");
        };
        let mut declarations = into_declarations(parsed).into_iter();
        let Some(Declaration::Assert(assertion)) = declarations.next() else {
            panic!("expected one assertion: {source:?}");
        };
        assert!(
            declarations.next().is_none(),
            "expected one declaration: {source:?}"
        );
        assertion
    }

    fn reject_at(source: &str, start: usize, end: usize) {
        let Err(diagnostic) = parse(source) else {
            panic!("expected source to fail: {source:?}");
        };
        assert_eq!(diagnostic.span(), Span::new(start, end), "{source:?}");
    }

    fn ident(name: &str, start: usize, end: usize) -> Ident {
        Ident {
            span: Span::new(start, end),
            name: String::from(name),
        }
    }

    fn name_type(name: &str, start: usize, end: usize) -> TypeExpr {
        TypeExpr::Name(ident(name, start, end))
    }

    fn meta_type(name: &str, start: usize, end: usize) -> TypeExpr {
        TypeExpr::MetaName(ident(name, start, end))
    }

    fn subtype(left: TypeExpr, right: TypeExpr) -> Formula {
        let span = Span::new(left.span().start(), right.span().end());
        Formula::Subtype(Subtype { span, left, right })
    }

    fn union(
        first: TypeExpr,
        operator: Span,
        second: TypeExpr,
        rest: Vec<(Span, Box<TypeExpr>)>,
    ) -> TypeExpr {
        let last = rest
            .last()
            .map_or_else(|| second.span(), |(_, child)| child.span());
        TypeExpr::Union(Nary {
            span: Span::new(first.span().start(), last.end()),
            first: Box::new(first),
            second: (operator, Box::new(second)),
            rest,
        })
    }

    fn intersection(
        first: TypeExpr,
        operator: Span,
        second: TypeExpr,
        rest: Vec<(Span, Box<TypeExpr>)>,
    ) -> TypeExpr {
        let last = rest
            .last()
            .map_or_else(|| second.span(), |(_, child)| child.span());
        TypeExpr::Intersection(Nary {
            span: Span::new(first.span().start(), last.end()),
            first: Box::new(first),
            second: (operator, Box::new(second)),
            rest,
        })
    }

    #[test]
    fn empty_source_parses_to_empty_file() {
        let Ok(parsed) = parse("") else {
            panic!("expected empty source to parse");
        };
        assert_eq!(parsed, parsed_file(Span::new(0, 0), Vec::new()));
    }

    #[test]
    fn lexical_failure_surfaces_first_diagnostic() {
        let Err(diagnostic) = parse("class @;") else {
            panic!("expected an error");
        };
        assert_eq!(diagnostic.span(), Span::new(6, 7));
        assert!(matches!(
            *diagnostic.kind(),
            DiagnosticKind::IllegalChar('@')
        ));
    }

    #[test]
    fn whitespace_and_comments_parse_to_empty_file() {
        let source = "  # nothing here\n\t\n";
        let Ok(parsed) = parse(source) else {
            panic!("expected whitespace to parse");
        };
        assert_eq!(parsed.span(), Span::new(0, source.len()));
    }

    #[test]
    fn whitespace_comments_and_keyword_prefixes_parse() {
        let source = "# head\r\nclass typex; # one\r\nclass andrey;\nclass or2;\nclass tuplex;\nclass inx;\nclass forallx;";
        let Ok(parsed) = parse(source) else {
            panic!("expected source to parse");
        };
        let names: Vec<&str> = parsed
            .declarations()
            .iter()
            .map(|declaration| {
                let Declaration::Class(class) = declaration else {
                    panic!("expected class declarations");
                };
                class.name.name.as_str()
            })
            .collect();
        assert_eq!(
            names,
            ["typex", "andrey", "or2", "tuplex", "inx", "forallx"]
        );
    }

    #[test]
    fn type_is_an_ordinary_class_name() {
        let Ok(parsed) = parse("class type;") else {
            panic!("expected source to parse");
        };
        assert_eq!(
            parsed.declarations(),
            [Declaration::Class(ClassDecl {
                span: Span::new(0, 11),
                name: ident("type", 6, 10),
                parameters: None,
                superclasses: Vec::new(),
            })]
        );
    }

    #[test]
    fn comment_at_end_of_input_needs_no_newline() {
        let source = "class a; # trailing";
        let Ok(parsed) = parse(source) else {
            panic!("expected source to parse");
        };
        assert_eq!(parsed.span(), Span::new(0, source.len()));
        assert_eq!(
            parsed.declarations(),
            [Declaration::Class(ClassDecl {
                span: Span::new(0, 8),
                name: ident("a", 6, 7),
                parameters: None,
                superclasses: Vec::new(),
            })]
        );
    }

    #[test]
    fn illegal_characters_keep_exact_spans() {
        for (source, ch, start, end) in [
            ("class @;", '@', 6, 7),
            ("class a;\rb;", '\r', 8, 9),
            ("# comment\rclass a;", '\r', 9, 10),
            ("class café;", 'é', 9, 11),
            ("class <;", '<', 6, 7),
            ("metavar ?;", '?', 8, 9),
            ("metavar ?5;", '?', 8, 9),
        ] {
            let Err(diagnostic) = parse(source) else {
                panic!("expected source to fail: {source:?}");
            };
            assert_eq!(diagnostic.span(), Span::new(start, end), "{source:?}");
            assert_eq!(
                *diagnostic.kind(),
                DiagnosticKind::IllegalChar(ch),
                "{source:?}"
            );
        }
    }

    #[test]
    fn reserved_metavariable_names_fail_in_complete_constructs() {
        for word in [
            "class", "extends", "metavar", "assert", "and", "or", "tuple", "forall", "in",
        ] {
            let source = format!("metavar ?{word};");
            let Err(diagnostic) = parse(&source) else {
                panic!("expected source to fail: {source:?}");
            };
            assert_eq!(diagnostic.span(), Span::new(8, 9 + word.len()));
            assert_eq!(
                *diagnostic.kind(),
                DiagnosticKind::ReservedWord(String::from(word))
            );
        }
    }

    #[test]
    fn generic_callable_keeps_binder_and_body_spans() {
        let source = "assert forall X, Y. (X, tuple[Y]) -> X | A <: object;";
        let assertion = one_assertion(source);
        let Formula::Subtype(atom) = assertion.formula else {
            panic!("expected subtype formula");
        };
        let TypeExpr::Generic(generic) = atom.left else {
            panic!("expected generic callable");
        };
        assert_eq!(
            &source[generic.span.start()..generic.span.end()],
            "forall X, Y. (X, tuple[Y]) -> X | A"
        );
        assert_eq!(
            &source[generic.keyword.start()..generic.keyword.end()],
            "forall"
        );
        assert_eq!(&source[generic.dot.start()..generic.dot.end()], ".");
        assert_eq!(
            generic
                .parameters
                .iter()
                .map(|parameter| parameter.name().name.as_str())
                .collect::<Vec<_>>(),
            ["X", "Y"]
        );
        assert_eq!(generic.body.params.len(), 2);
        assert!(matches!(*generic.body.ret, TypeExpr::Union(_)));
    }

    #[test]
    fn generic_parameter_restrictions_keep_operator_and_delimiter_spans() {
        let source = "assert forall X <: A, Y in {A, tuple[B]}. (X, Y) -> X <: object;";
        let assertion = one_assertion(source);
        let Formula::Subtype(atom) = assertion.formula else {
            panic!("expected subtype formula");
        };
        let TypeExpr::Generic(generic) = atom.left else {
            panic!("expected generic callable");
        };
        let [
            GenericParameterExpr::UpperBound {
                operator, upper, ..
            },
            GenericParameterExpr::ExactSet {
                keyword,
                open_brace,
                first,
                rest,
                close_brace,
                ..
            },
        ] = generic.parameters.as_slice()
        else {
            panic!("expected upper-bound and exact-set parameters");
        };
        assert_eq!(&source[operator.start()..operator.end()], "<:");
        assert!(matches!(upper, TypeExpr::Name(_)));
        assert_eq!(&source[keyword.start()..keyword.end()], "in");
        assert_eq!(&source[open_brace.start()..open_brace.end()], "{");
        assert_eq!(&source[close_brace.start()..close_brace.end()], "}");
        assert!(matches!(first, TypeExpr::Name(_)));
        assert_eq!(rest.len(), 1);
    }

    #[test]
    fn invalid_source_forms_keep_blame_spans() {
        for (source, start, end) in [
            ("assert ?T: a <: b;", 9, 10),
            ("assert tuple: a <: b;", 12, 13),
            ("assert tuple[a,] <: object;", 15, 16),
            ("assert tuple[, a] <: object;", 13, 14),
            ("assert tuple[a,, b] <: object;", 15, 16),
            ("assert tuple[a b] <: object;", 15, 16),
            ("assert tuple a <: object;", 13, 14),
            ("assert tuple[a <: object;", 15, 17),
            ("assert (a <: b) | c;", 16, 17),
            ("assert (a <: b) & c;", 16, 17),
            ("assert a <: b <: c;", 14, 16),
            ("class a;;", 8, 9),
        ] {
            reject_at(source, start, end);
        }
    }

    #[test]
    fn assertion_label_allows_space_before_colon() {
        let assertion = one_assertion("assert label : a <: b;");
        let Some(label) = assertion.label else {
            panic!("expected assertion label");
        };
        assert_eq!(label.name, "label");
        assert_eq!(label.span, Span::new(7, 12));
    }

    #[test]
    fn repeated_or_stays_flat() {
        assert_eq!(
            one_assertion("assert a <: b or c <: d or e <: f;"),
            AssertDecl {
                span: Span::new(0, 34),
                label: None,
                formula: Formula::Or(Nary {
                    span: Span::new(7, 33),
                    first: Box::new(subtype(name_type("a", 7, 8), name_type("b", 12, 13))),
                    second: (
                        Span::new(14, 16),
                        Box::new(subtype(name_type("c", 17, 18), name_type("d", 22, 23))),
                    ),
                    rest: vec![(
                        Span::new(24, 26),
                        Box::new(subtype(name_type("e", 27, 28), name_type("f", 32, 33))),
                    )],
                }),
            }
        );
    }

    #[test]
    fn repeated_and_stays_flat() {
        assert_eq!(
            one_assertion("assert a <: b and c <: d and e <: f;"),
            AssertDecl {
                span: Span::new(0, 36),
                label: None,
                formula: Formula::And(Nary {
                    span: Span::new(7, 35),
                    first: Box::new(subtype(name_type("a", 7, 8), name_type("b", 12, 13))),
                    second: (
                        Span::new(14, 17),
                        Box::new(subtype(name_type("c", 18, 19), name_type("d", 23, 24))),
                    ),
                    rest: vec![(
                        Span::new(25, 28),
                        Box::new(subtype(name_type("e", 29, 30), name_type("f", 34, 35))),
                    )],
                }),
            }
        );
    }

    #[test]
    fn repeated_union_stays_flat() {
        assert_eq!(
            one_assertion("assert a | b | c <: d;"),
            AssertDecl {
                span: Span::new(0, 22),
                label: None,
                formula: subtype(
                    union(
                        name_type("a", 7, 8),
                        Span::new(9, 10),
                        name_type("b", 11, 12),
                        vec![(Span::new(13, 14), Box::new(name_type("c", 15, 16)))],
                    ),
                    name_type("d", 20, 21),
                ),
            }
        );
    }

    #[test]
    fn repeated_intersection_stays_flat() {
        assert_eq!(
            one_assertion("assert a & b & c <: d;"),
            AssertDecl {
                span: Span::new(0, 22),
                label: None,
                formula: subtype(
                    intersection(
                        name_type("a", 7, 8),
                        Span::new(9, 10),
                        name_type("b", 11, 12),
                        vec![(Span::new(13, 14), Box::new(name_type("c", 15, 16)))],
                    ),
                    name_type("d", 20, 21),
                ),
            }
        );
    }

    #[test]
    fn intersection_binds_more_tightly_than_union() {
        assert_eq!(
            one_assertion("assert a | b & ?T <: c;"),
            AssertDecl {
                span: Span::new(0, 23),
                label: None,
                formula: subtype(
                    union(
                        name_type("a", 7, 8),
                        Span::new(9, 10),
                        intersection(
                            name_type("b", 11, 12),
                            Span::new(13, 14),
                            meta_type("T", 15, 17),
                            Vec::new(),
                        ),
                        Vec::new(),
                    ),
                    name_type("c", 21, 22),
                ),
            }
        );
    }

    #[test]
    fn parenthesized_union_remains_the_first_outer_union_operand() {
        let assertion = one_assertion("assert (a | b) | c <: d;");
        let Formula::Subtype(atom) = assertion.formula else {
            panic!("expected subtype formula");
        };
        let TypeExpr::Union(outer) = atom.left else {
            panic!("expected outer union");
        };
        assert_eq!(outer.span, Span::new(7, 18));
        assert_eq!(outer.second.0, Span::new(15, 16));
        let TypeExpr::Paren(group) = *outer.first else {
            panic!("expected parenthesized first operand");
        };
        assert_eq!(group.span, Span::new(7, 14));
        assert!(matches!(*group.inner, TypeExpr::Union(_)));
    }

    #[test]
    fn generated_expected_names_cover_every_terminal() {
        let mut actual = BTreeSet::new();
        for source in [
            "&",
            "class",
            "class a",
            "class a[",
            "class a extends b",
            "metavar",
            "assert",
            "assert a",
            "assert tuple",
            "assert tuple[a",
            "assert (a",
            "assert ()",
            "assert forall X",
            "assert forall X in",
            "assert forall X in {a",
            "assert a <: b",
        ] {
            let Err(diagnostic) = parse(source) else {
                panic!("expected incomplete source to fail: {source:?}");
            };
            let DiagnosticKind::UnexpectedToken { expected, .. } = diagnostic.kind() else {
                panic!("expected syntax diagnostic: {source:?}");
            };
            actual.extend(expected);
        }
        assert_eq!(
            actual,
            ExpectedToken::ALL.into_iter().collect::<BTreeSet<_>>()
        );
    }

    #[test]
    fn nesting_beyond_the_old_limit_parses() {
        const DEPTH: usize = 129;
        let source = format!("assert {}a <: b{};", "(".repeat(DEPTH), ")".repeat(DEPTH));
        let assertion = one_assertion(&source);
        assert_eq!(assertion.formula.span(), Span::new(7, source.len() - 1));
    }
}
