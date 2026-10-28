//! Source syntax nodes and grammar construction helpers.
//!
//! Nodes retain source spans. Formula and type operators retain source order.

use std::iter;

use super::diagnostic::{Diagnostic, DiagnosticKind, Span, diagnostic};

/// Parsed syntax tree of one input file.
#[derive(Debug, PartialEq, Eq)]
pub struct ParsedFile {
    /// Span of the whole file.
    span: Span,
    /// Declarations in source order.
    decls: Vec<Declaration>,
}

/// Keep grammar output and its whole-file span together inside the frontend.
pub fn parsed_file(span: Span, decls: Vec<Declaration>) -> ParsedFile {
    ParsedFile { span, decls }
}

/// Move source declarations into collection without exposing mutable syntax.
pub fn into_declarations(parsed: ParsedFile) -> Vec<Declaration> {
    parsed.decls
}

impl ParsedFile {
    /// Span of the whole source file.
    #[must_use]
    pub fn span(&self) -> Span {
        self.span
    }

    /// Read source syntax for parser tests and the independent model evaluator.
    #[cfg(test)]
    #[must_use]
    pub fn declarations(&self) -> &[Declaration] {
        &self.decls
    }
}

/// One top-level declaration.
#[derive(Debug, PartialEq, Eq)]
pub enum Declaration {
    Class(ClassDecl),
    Metavar(MetavarDecl),
    Assert(AssertDecl),
}

/// `class` declaration with optional parameters and superclasses.
#[derive(Debug, PartialEq, Eq)]
pub struct ClassDecl {
    /// Span of the whole declaration, keyword through `;`.
    pub span: Span,
    /// Declared class name.
    pub name: Ident,
    /// Non-empty parameter list when brackets are present.
    pub parameters: Option<ClassParameters>,
    /// Superclass expressions in source order.
    pub superclasses: Vec<SuperclassExpr>,
}

/// Non-empty class parameter list with its bracket spans.
#[derive(Debug, PartialEq, Eq)]
pub struct ClassParameters {
    /// Opening bracket span.
    pub open_bracket: Span,
    /// First parameter. Explicit parameter lists cannot be empty.
    pub first: ClassParameterExpr,
    /// Remaining parameters in declaration order.
    pub rest: Vec<ClassParameterExpr>,
    /// Closing bracket span.
    pub close_bracket: Span,
}

impl ClassParameters {
    /// Read every parameter in declaration order.
    #[cfg(test)]
    pub fn operands(&self) -> impl Iterator<Item = &ClassParameterExpr> {
        iter::once(&self.first).chain(&self.rest)
    }

    /// Consume the list and return parameters in declaration order.
    pub fn into_operands(self) -> impl Iterator<Item = ClassParameterExpr> {
        iter::once(self.first).chain(self.rest)
    }
}

/// One class parameter with its declared variance and source spans.
#[derive(Debug, PartialEq, Eq)]
pub struct ClassParameterExpr {
    /// Span from the variance sign, if present, through the name.
    pub span: Span,
    /// Local parameter name.
    pub name: Ident,
    /// Declared variance, including the sign span when present.
    pub variance: VarianceExpr,
}

/// Parsed variance. An omitted sign declares an invariant position.
#[derive(Debug, PartialEq, Eq)]
pub enum VarianceExpr {
    Invariant,
    Covariant(Span),
    Contravariant(Span),
}

/// Superclass root name with an optional explicit argument list.
#[derive(Debug, PartialEq, Eq)]
pub struct SuperclassExpr {
    /// Span from the root name through its arguments, if present.
    pub span: Span,
    /// Root name. Resolution checks this name in the class table.
    pub name: Ident,
    /// Non-empty argument list when brackets are present.
    pub arguments: Option<ClassArguments>,
}

/// `metavar` declaration.
#[derive(Debug, PartialEq, Eq)]
pub struct MetavarDecl {
    /// Span of the whole declaration, keyword through `;`.
    pub span: Span,
    /// Declared metavariable name, without the leading `?`.
    pub name: Ident,
}

/// `assert` declaration with an optional label.
#[derive(Debug, PartialEq, Eq)]
pub struct AssertDecl {
    /// Span of the whole assertion, keyword through `;`.
    pub span: Span,
    /// Label name when the assertion is named.
    pub label: Option<Ident>,
    /// Asserted formula over syntactic types.
    pub formula: Formula,
}

/// Parsed Boolean formula over subtype atoms with source type expressions.
#[derive(Debug, PartialEq, Eq)]
pub enum Formula {
    And(Nary<Formula>),
    Or(Nary<Formula>),
    Subtype(Subtype),
    Paren(Paren),
}

impl Formula {
    /// Span of the formula. Parenthesized formulas carry the outer span
    /// including the parens.
    #[must_use]
    pub fn span(&self) -> Span {
        match self {
            Self::And(node) | Self::Or(node) => node.span,
            Self::Subtype(atom) => atom.span,
            Self::Paren(group) => group.span,
        }
    }
}

/// Subtype atom between two type expressions.
#[derive(Debug, PartialEq, Eq)]
pub struct Subtype {
    /// Span from the left term through the right term.
    pub span: Span,
    /// Lower bound type.
    pub left: TypeExpr,
    /// Upper bound type.
    pub right: TypeExpr,
}

/// Parenthesized formula: grouping with the outer span.
#[derive(Debug, PartialEq, Eq)]
pub struct Paren {
    /// Span including the parentheses.
    pub span: Span,
    /// Grouped formula with its own inner span.
    pub inner: Box<Formula>,
}

/// Parsed source type with complete operator and grouping spans.
#[derive(Debug, PartialEq, Eq)]
pub enum TypeExpr {
    Name(Ident),
    ClassApplication(ClassApplication),
    MetaName(Ident),
    Tuple(TupleTypeExpr),
    Callable(CallableTypeExpr),
    Generic(Box<GenericCallableTypeExpr>),
    Union(Nary<TypeExpr>),
    Intersection(Nary<TypeExpr>),
    Paren(ParenTypeExpr),
}

impl TypeExpr {
    /// Span of the complete type expression.
    #[must_use]
    pub fn span(&self) -> Span {
        match self {
            Self::Name(ident) | Self::MetaName(ident) => ident.span,
            Self::ClassApplication(node) => node.span,
            Self::Tuple(node) => node.span,
            Self::Callable(node) => node.span,
            Self::Generic(node) => node.span,
            Self::Union(node) | Self::Intersection(node) => node.span,
            Self::Paren(node) => node.span,
        }
    }
}

/// Explicit class application, separate from a bare type name.
#[derive(Debug, PartialEq, Eq)]
pub struct ClassApplication {
    /// Span from the class name through the closing bracket.
    pub span: Span,
    /// Name before the argument list.
    pub name: Ident,
    /// Complete arguments in source order.
    pub arguments: ClassArguments,
}

/// Non-empty class argument list with complete expressions and bracket spans.
#[derive(Debug, PartialEq, Eq)]
pub struct ClassArguments {
    /// Opening bracket span.
    pub open_bracket: Span,
    /// First argument. Explicit argument lists cannot be empty.
    pub first: Box<TypeExpr>,
    /// Remaining arguments in source order.
    pub rest: Vec<TypeExpr>,
    /// Closing bracket span.
    pub close_bracket: Span,
}

impl ClassArguments {
    /// Read every argument in source order.
    pub fn operands(&self) -> impl Iterator<Item = &TypeExpr> {
        iter::once(self.first.as_ref()).chain(&self.rest)
    }

    /// Consume the list and return arguments in source order.
    pub fn into_operands(self) -> impl Iterator<Item = TypeExpr> {
        iter::once(*self.first).chain(self.rest)
    }
}

/// Build one flat n-ary syntax node, or return its only operand.
///
/// `rest` holds each operator span and following operand in source order. The
/// constructed span starts at `first` and ends at the final operand.
pub fn build_nary<T>(
    first: T,
    rest: Vec<(Span, T)>,
    operand_span: impl Fn(&T) -> Span,
    node: impl FnOnce(Nary<T>) -> T,
) -> T {
    let mut operands = rest.into_iter();
    let Some((second_operator, second_operand)) = operands.next() else {
        return first;
    };
    let rest: Vec<(Span, Box<T>)> = operands
        .map(|(operator, operand)| (operator, Box::new(operand)))
        .collect();
    let last = match rest.last() {
        Some((_, operand)) => operand_span(operand),
        None => operand_span(&second_operand),
    };
    let span = Span::new(operand_span(&first).start(), last.end());
    node(Nary {
        span,
        first: Box::new(first),
        second: (second_operator, Box::new(second_operand)),
        rest,
    })
}

/// Apply intersection tails, then union tails, to one first type operand.
pub fn build_type_operators(
    first: TypeExpr,
    intersection_rest: Vec<(Span, TypeExpr)>,
    union_rest: Vec<(Span, TypeExpr)>,
) -> TypeExpr {
    let intersection = build_nary(
        first,
        intersection_rest,
        TypeExpr::span,
        TypeExpr::Intersection,
    );
    build_nary(intersection, union_rest, TypeExpr::span, TypeExpr::Union)
}

/// Build one callable from its outer bounds, parameters, arrow, and return.
pub fn build_callable(
    start: usize,
    params: Vec<TypeExpr>,
    (arrow, ret): (Span, TypeExpr),
    end: usize,
) -> CallableTypeExpr {
    CallableTypeExpr {
        span: Span::new(start, end),
        arrow,
        params,
        ret: Box::new(ret),
    }
}

/// Fixed-length tuple type with its complete outer span.
#[derive(Debug, PartialEq, Eq)]
pub struct TupleTypeExpr {
    /// Span from the `tuple` keyword through the closing bracket.
    pub span: Span,
    /// Element types in source order.
    pub elements: Vec<TypeExpr>,
}

/// Fixed-arity callable type with complete child and operator spans.
#[derive(Debug, PartialEq, Eq)]
pub struct CallableTypeExpr {
    /// Span from the opening parenthesis through the return type.
    pub span: Span,
    /// Arrow operator span.
    pub arrow: Span,
    /// Positional parameter types in source order.
    pub params: Vec<TypeExpr>,
    /// Return type.
    pub ret: Box<TypeExpr>,
}

/// Generic callable type with complete binder and body spans.
#[derive(Debug, PartialEq, Eq)]
pub struct GenericCallableTypeExpr {
    /// Span from `forall` through the callable body.
    pub span: Span,
    /// Span of the `forall` keyword.
    pub keyword: Span,
    /// Simultaneous generic parameters in source order.
    pub parameters: Vec<GenericParameterExpr>,
    /// Span of the dot between the parameters and body.
    pub dot: Span,
    /// Callable body controlled by this binder.
    pub body: CallableTypeExpr,
}

/// One parsed generic parameter and its optional restriction.
#[derive(Debug, PartialEq, Eq)]
pub enum GenericParameterExpr {
    /// Plain parameter with no source restriction.
    Plain { name: Ident },
    /// Parameter restricted to subtypes of one upper-bound type.
    UpperBound {
        name: Ident,
        operator: Span,
        upper: TypeExpr,
    },
    /// Parameter restricted to one of a non-empty list of exact types.
    ExactSet {
        name: Ident,
        keyword: Span,
        open_brace: Span,
        first: TypeExpr,
        rest: Vec<TypeExpr>,
        close_brace: Span,
    },
}

impl GenericParameterExpr {
    /// Parameter name shared by all restriction forms.
    #[must_use]
    pub fn name(&self) -> &Ident {
        match self {
            Self::Plain { name } | Self::UpperBound { name, .. } | Self::ExactSet { name, .. } => {
                name
            }
        }
    }
}

/// An operator with at least two operands and every operator span retained.
#[derive(Debug, PartialEq, Eq)]
pub struct Nary<T> {
    /// Span from the first child through the last child.
    pub span: Span,
    /// First child.
    pub first: Box<T>,
    /// Second operator span plus child.
    pub second: (Span, Box<T>),
    /// Further operator-span and child pairs.
    pub rest: Vec<(Span, Box<T>)>,
}

impl<T> Nary<T> {
    /// Operands keep source order; every node has at least two.
    pub fn operands(&self) -> impl Iterator<Item = &T> {
        iter::once(self.first.as_ref())
            .chain(iter::once(self.second.1.as_ref()))
            .chain(self.rest.iter().map(|(_, operand)| operand.as_ref()))
    }

    /// Consume the node and return its operands in source order.
    pub fn into_operands(self) -> impl Iterator<Item = T> {
        iter::once(*self.first)
            .chain(iter::once(*self.second.1))
            .chain(self.rest.into_iter().map(|(_, operand)| *operand))
    }
}

/// Parenthesized type with its complete outer span.
#[derive(Debug, PartialEq, Eq)]
pub struct ParenTypeExpr {
    /// Span including the parentheses.
    pub span: Span,
    /// Grouped type with its own inner span.
    pub inner: Box<TypeExpr>,
}

/// Identifier: token span plus the name without any sigil.
#[derive(Debug, PartialEq, Eq)]
pub struct Ident {
    /// Span of the name token.
    pub span: Span,
    /// Name text.
    pub name: String,
}

/// Build one metavariable identifier from its complete source spelling.
///
/// # Errors
///
/// Returns a reserved-word diagnostic when the name after `?` is a keyword.
///
/// # Panics
///
/// Panics when `raw` has no leading `?`. The generated lexer guarantees this
/// invariant for every caller.
pub fn metavar_ident(raw: &str, span: Span) -> Result<Ident, Diagnostic> {
    let Some(name) = raw.strip_prefix('?') else {
        panic!("metavariable token has no `?` prefix: {raw:?}");
    };
    if matches!(
        name,
        "class" | "extends" | "metavar" | "assert" | "and" | "or" | "tuple" | "forall" | "in"
    ) {
        Err(diagnostic(
            span,
            DiagnosticKind::ReservedWord(name.to_owned()),
        ))
    } else {
        Ok(Ident {
            span,
            name: name.to_owned(),
        })
    }
}
