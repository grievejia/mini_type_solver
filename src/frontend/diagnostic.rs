//! Source spans and frontend diagnostics.
//!
//! Diagnostic coordinates use original source bytes and Unicode columns.

use std::backtrace::Backtrace;
use std::error::Error;
use std::fmt::{self, Display, Formatter};

/// Byte-offset span into the original source text.
///
/// Both bounds are byte offsets on character boundaries with
/// `start <= end`. An empty span marks a point position such as end of
/// input.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    start: usize,
    end: usize,
}

impl Span {
    /// Span from `start` (inclusive) to `end` (exclusive).
    ///
    /// Both bounds must sit on character boundaries.
    ///
    /// # Panics
    ///
    /// Panics when `start` exceeds `end`.
    #[must_use]
    pub fn new(start: usize, end: usize) -> Self {
        assert!(start <= end, "span start {start} exceeds end {end}");
        Self { start, end }
    }

    /// Start byte offset, inclusive.
    #[must_use]
    pub fn start(&self) -> usize {
        self.start
    }

    /// End byte offset, exclusive.
    #[must_use]
    pub fn end(&self) -> usize {
        self.end
    }

    /// One-based line and column of the span start.
    #[must_use]
    pub fn start_line_col(&self, source: &str) -> (usize, usize) {
        line_col(source, self.start)
    }
}

/// One-based line and column of a byte offset.
///
/// Lines break on `\n` and `\r\n`, counted once. Columns count Unicode
/// scalar values. A bare `\r` counts as an ordinary character here: lexical
/// analysis rejects it before any later span is rendered, so its treatment is
/// unobservable. Offsets past the end clamp to the end.
fn line_col(source: &str, offset: usize) -> (usize, usize) {
    // The clamp keeps `index` below `source.len` for the byte reads below.
    let offset = offset.min(source.len());
    let bytes = source.as_bytes();
    let mut line = 1;
    let mut col = 1;
    let mut index = 0;
    while index < offset {
        if bytes[index] == b'\n' {
            line += 1;
            col = 1;
            index += 1;
        } else if bytes[index] == b'\r' && bytes.get(index + 1) == Some(&b'\n') {
            line += 1;
            col = 1;
            index += 2;
        } else if let Some(rest) = source.get(index..)
            && let Some(ch) = rest.chars().next()
        {
            col += 1;
            index += ch.len_utf8();
        } else {
            break;
        }
    }
    (line, col)
}

/// Failure of lexical, syntactic, or semantic analysis.
#[derive(Debug)]
pub struct Diagnostic {
    span: Span,
    kind: DiagnosticKind,
    backtrace: Backtrace,
}

/// One terminal that the generated parser accepts at an error position.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ExpectedToken {
    Assert,
    Class,
    Extends,
    Metavar,
    And,
    Or,
    Tuple,
    Forall,
    In,
    Name,
    MetaName,
    Subtype,
    Arrow,
    Plus,
    Minus,
    Comma,
    Colon,
    Semicolon,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Amp,
    Pipe,
    Dot,
}

impl ExpectedToken {
    #[cfg(test)]
    pub const ALL: [Self; 27] = [
        Self::Assert,
        Self::Class,
        Self::Extends,
        Self::Metavar,
        Self::And,
        Self::Or,
        Self::Tuple,
        Self::Forall,
        Self::In,
        Self::Name,
        Self::MetaName,
        Self::Subtype,
        Self::Arrow,
        Self::Plus,
        Self::Minus,
        Self::Comma,
        Self::Colon,
        Self::Semicolon,
        Self::LParen,
        Self::RParen,
        Self::LBracket,
        Self::RBracket,
        Self::LBrace,
        Self::RBrace,
        Self::Amp,
        Self::Pipe,
        Self::Dot,
    ];

    pub fn from_generated(name: &str) -> Self {
        match name {
            "\"assert\"" => Self::Assert,
            "\"class\"" => Self::Class,
            "\"extends\"" => Self::Extends,
            "\"metavar\"" => Self::Metavar,
            "\"and\"" => Self::And,
            "\"or\"" => Self::Or,
            "\"tuple\"" => Self::Tuple,
            "\"forall\"" => Self::Forall,
            "\"in\"" => Self::In,
            "NAME" => Self::Name,
            "META_NAME" => Self::MetaName,
            "\"<:\"" => Self::Subtype,
            "\"->\"" => Self::Arrow,
            "\"+\"" => Self::Plus,
            "\"-\"" => Self::Minus,
            "\",\"" => Self::Comma,
            "\":\"" => Self::Colon,
            "\";\"" => Self::Semicolon,
            "\"(\"" => Self::LParen,
            "\")\"" => Self::RParen,
            "\"[\"" => Self::LBracket,
            "\"]\"" => Self::RBracket,
            "\"{\"" => Self::LBrace,
            "\"}\"" => Self::RBrace,
            "\"&\"" => Self::Amp,
            "\"|\"" => Self::Pipe,
            "\".\"" => Self::Dot,
            _ => panic!("generated parser returned unknown terminal name {name:?}"),
        }
    }
}

impl Display for ExpectedToken {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Assert => write!(f, "keyword `assert`"),
            Self::Class => write!(f, "keyword `class`"),
            Self::Extends => write!(f, "keyword `extends`"),
            Self::Metavar => write!(f, "keyword `metavar`"),
            Self::And => write!(f, "keyword `and`"),
            Self::Or => write!(f, "keyword `or`"),
            Self::Tuple => write!(f, "keyword `tuple`"),
            Self::Forall => write!(f, "keyword `forall`"),
            Self::In => write!(f, "keyword `in`"),
            Self::Name => write!(f, "a name"),
            Self::MetaName => write!(f, "a metavariable name"),
            Self::Subtype => write!(f, "`<:`"),
            Self::Arrow => write!(f, "`->`"),
            Self::Plus => write!(f, "`+`"),
            Self::Minus => write!(f, "`-`"),
            Self::Comma => write!(f, "`,`"),
            Self::Colon => write!(f, "`:`"),
            Self::Semicolon => write!(f, "`;`"),
            Self::LParen => write!(f, "`(`"),
            Self::RParen => write!(f, "`)`"),
            Self::LBracket => write!(f, "`[`"),
            Self::RBracket => write!(f, "`]`"),
            Self::LBrace => write!(f, "`{{`"),
            Self::RBrace => write!(f, "`}}`"),
            Self::Amp => write!(f, "`&`"),
            Self::Pipe => write!(f, "`|`"),
            Self::Dot => write!(f, "`.`"),
        }
    }
}

/// Input found where the generated parser stopped.
#[derive(Debug, PartialEq, Eq)]
pub enum Found {
    Token(String),
    EndOfInput,
}

impl Display for Found {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Token(spelling) => write!(f, "`{spelling}`"),
            Self::EndOfInput => write!(f, "end of input"),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum DiagnosticKind {
    IllegalChar(char),
    ReservedWord(String),
    UnexpectedToken {
        expected: Vec<ExpectedToken>,
        found: Found,
    },
    DuplicateName {
        kind: NameKind,
        name: String,
    },
    DuplicateSuperclass {
        name: String,
    },
    BuiltinRedeclared {
        name: String,
    },
    NeverAsSuperclass,
    BuiltinTypeParameter {
        name: String,
    },
    UnusedTypeParameter {
        name: String,
    },
    ParameterRestriction {
        name: String,
    },
    MetavarParameterRestriction {
        name: String,
    },
    GenericParameterRestriction,
    ClassArguments {
        name: String,
        mismatch: ClassArgumentMismatch,
    },
    ParameterClassApplication {
        name: String,
    },
    MetavarSuperclassArgument {
        name: String,
    },
    GenericSuperclassArgument,
    ConflictingAncestorArguments {
        name: String,
        first: Box<[String]>,
        second: Box<[String]>,
    },
    ClassParameterVariance {
        name: String,
    },
    UndeclaredName {
        kind: RefKind,
        name: String,
    },
    SelfEdge {
        name: String,
    },
    Cycle {
        path: Vec<String>,
    },
    InconsistentOrder {
        name: String,
    },
}

/// How explicit class arguments disagree with the class parameters.
#[derive(Debug, PartialEq, Eq)]
pub enum ClassArgumentMismatch {
    /// A generic class has no argument list.
    Missing { expected: usize },
    /// A class without parameters has an argument list.
    Unexpected,
    /// A generic class has an argument list of the wrong length.
    Count { expected: usize, actual: usize },
}

impl ClassArgumentMismatch {
    fn message(&self, name: &str) -> String {
        let arguments = |count: usize| if count == 1 { "argument" } else { "arguments" };
        match self {
            Self::Missing { expected } => format!(
                "generic class `{name}` requires {expected} explicit type {}",
                arguments(*expected)
            ),
            Self::Unexpected => {
                format!("class `{name}` has no type parameters and cannot take arguments")
            }
            Self::Count { expected, actual } => format!(
                "class `{name}` requires {expected} type {}, found {actual}",
                arguments(*expected)
            ),
        }
    }
}

/// Which namespace a duplicate name offends.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NameKind {
    Class,
    Metavar,
    AssertionName,
    TypeParameter,
}

/// Which namespace an undeclared reference needs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RefKind {
    Class,
    Metavar,
}

/// Construct a diagnostic inside the frontend implementation.
/// The diagnostic's state remains private; callers can render it or read its span.
pub fn diagnostic(span: Span, kind: DiagnosticKind) -> Diagnostic {
    Diagnostic {
        span,
        kind,
        backtrace: Backtrace::capture(),
    }
}

impl Diagnostic {
    /// Borrow the failure kind for semantic regression checks.
    #[cfg(test)]
    pub fn kind(&self) -> &DiagnosticKind {
        &self.kind
    }

    /// Source span of the failure.
    pub fn span(&self) -> Span {
        self.span
    }

    /// Render one diagnostic line with coordinates.
    pub fn render(&self, path: &str, source: &str) -> String {
        let (line, col) = self.span.start_line_col(source);
        format!("{path}:{line}:{col}: {}", self.message())
    }

    fn message(&self) -> String {
        match &self.kind {
            DiagnosticKind::IllegalChar(ch) => format!("illegal character {ch:?}"),
            DiagnosticKind::ReservedWord(word) => {
                format!("reserved word `{word}` cannot be used as a name")
            }
            DiagnosticKind::UnexpectedToken { expected, found } => match expected.as_slice() {
                [] => format!("unexpected {found}"),
                [expected] => format!("expected {expected}, found {found}"),
                _ => {
                    let expected = expected
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("expected one of {expected}, found {found}")
                }
            },
            DiagnosticKind::DuplicateName { kind, name } => match kind {
                NameKind::Class => format!("duplicate class `{name}`"),
                NameKind::Metavar => format!("duplicate metavariable `?{name}`"),
                NameKind::AssertionName => {
                    format!("duplicate assertion name `{name}`")
                }
                NameKind::TypeParameter => format!("duplicate type parameter `{name}`"),
            },
            DiagnosticKind::DuplicateSuperclass { name } => {
                format!("duplicate superclass `{name}`")
            }
            DiagnosticKind::BuiltinRedeclared { name } => {
                format!("cannot redeclare built-in class `{name}`")
            }
            DiagnosticKind::NeverAsSuperclass => String::from("`never` cannot be a superclass"),
            DiagnosticKind::BuiltinTypeParameter { name } => {
                format!("built-in `{name}` cannot be a type parameter")
            }
            DiagnosticKind::UnusedTypeParameter { name } => {
                format!("type parameter `{name}` is unused after normalization")
            }
            DiagnosticKind::ParameterRestriction { name } => {
                format!("generic parameter restriction cannot contain type parameter `{name}`")
            }
            DiagnosticKind::MetavarParameterRestriction { name } => {
                format!("generic parameter restriction cannot contain metavariable `?{name}`")
            }
            DiagnosticKind::GenericParameterRestriction => {
                String::from("generic parameter restriction cannot contain a generic callable")
            }
            DiagnosticKind::ClassArguments { name, mismatch } => mismatch.message(name),
            DiagnosticKind::ParameterClassApplication { name } => {
                format!("type parameter `{name}` cannot take class arguments")
            }
            DiagnosticKind::MetavarSuperclassArgument { name } => {
                format!("superclass argument cannot contain metavariable `?{name}`")
            }
            DiagnosticKind::GenericSuperclassArgument => {
                String::from("superclass argument cannot contain a generic callable")
            }
            DiagnosticKind::ConflictingAncestorArguments {
                name,
                first,
                second,
            } => format!(
                "conflicting argument templates for ancestor `{name}`: [{}] and [{}]",
                first.join(", "),
                second.join(", ")
            ),
            DiagnosticKind::ClassParameterVariance { name } => format!(
                "incompatible variance for class parameter `{name}` in superclass arguments"
            ),
            DiagnosticKind::UndeclaredName { kind, name } => match kind {
                RefKind::Class => format!("undeclared class `{name}`"),
                RefKind::Metavar => format!("undeclared metavariable `?{name}`"),
            },
            DiagnosticKind::SelfEdge { name } => {
                format!("class `{name}` cannot be its own superclass")
            }
            DiagnosticKind::Cycle { path } => {
                let chain = path
                    .iter()
                    .map(|name| format!("`{name}`"))
                    .collect::<Vec<_>>()
                    .join(" extends ");
                format!("cyclic superclass hierarchy: {chain}")
            }
            DiagnosticKind::InconsistentOrder { name } => {
                format!("inconsistent superclass order for class `{name}`")
            }
        }
    }
}

impl Display for Diagnostic {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}", self.message())?;
        write!(f, "{}", self.backtrace)
    }
}

impl Error for Diagnostic {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn line_col_counts_lines_and_scalar_columns() {
        assert_eq!(line_col("", 0), (1, 1));
        assert_eq!(line_col("ab", 0), (1, 1));
        assert_eq!(line_col("ab", 2), (1, 3));
        assert_eq!(line_col("ab\ncd", 4), (2, 2));
        assert_eq!(line_col("a\r\nb", 3), (2, 1));
        assert_eq!(line_col("éx", 2), (1, 2));
        assert_eq!(line_col("ab", 99), (1, 3));
        assert_eq!(line_col("ab\n", 3), (2, 1));
        assert_eq!(line_col("héllo", 3), (1, 3));
    }

    #[test]
    fn render_pins_path_coordinates_and_message() {
        for (kind, message) in [
            (DiagnosticKind::IllegalChar('!'), "illegal character '!'"),
            (
                DiagnosticKind::ReservedWord(String::from("and")),
                "reserved word `and` cannot be used as a name",
            ),
            (
                DiagnosticKind::UnexpectedToken {
                    expected: vec![ExpectedToken::Name],
                    found: Found::Token(String::from("and")),
                },
                "expected a name, found `and`",
            ),
        ] {
            let diagnostic = diagnostic(Span::new(3, 3), kind);
            assert_eq!(
                diagnostic.render("input.txt", "ab\ncd"),
                format!("input.txt:2:1: {message}")
            );
        }
    }

    #[test]
    #[should_panic(expected = "span start 5 exceeds end 3")]
    fn span_rejects_reversed_bounds() {
        let _ = Span::new(5, 3);
    }

    #[test]
    fn display_mentions_the_summary() {
        let diagnostic = diagnostic(Span::new(0, 0), DiagnosticKind::IllegalChar('?'));
        let text = diagnostic.to_string();
        assert!(
            text.starts_with("illegal character '?'\n"),
            "unexpected display: {text:?}"
        );
    }
}
