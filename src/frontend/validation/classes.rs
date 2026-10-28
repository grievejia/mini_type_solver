//! Class declaration metadata and owned superclass templates.
//!
//! A template parameter belongs to one class and keeps its declaration
//! position. Templates contain no callable binder or metavariable. Only surviving
//! parameter uses retain source spans for variance checks.

use std::cmp::Ordering;
use std::collections::BTreeMap;

use super::super::ast::{ClassApplication, ClassArguments, Ident, TypeExpr};
use super::super::diagnostic::{
    ClassArgumentMismatch, Diagnostic, DiagnosticKind, RefKind, Span, diagnostic,
};
use super::declarations::Variance;
use super::types::Junction;
use super::{
    ClassId, ClassType, CollectedClass, Declarations, NameLookup, ResolvedClass,
    ResolvedSuperclass, checked_u32,
};

/// Parameter position in the declaration that owns a template.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ClassParamRef {
    pub owner: ClassId,
    pub position: u32,
}

/// Generic-free superclass argument, with owned children.
///
/// During resolution, parameter data includes source spans. Published templates
/// retain only parameter owners and positions. Each position belongs to the
/// class declaration that owns its parameter.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TemplateType<P = ClassParamRef> {
    Parameter {
        reference: P,
    },
    Class(ClassType<TemplateType<P>>),
    Tuple(Vec<TemplateType<P>>),
    Callable {
        params: Vec<TemplateType<P>>,
        ret: Box<TemplateType<P>>,
    },
    Union(Vec<TemplateType<P>>),
    Intersection(Vec<TemplateType<P>>),
}

/// One surviving use of a class parameter in a direct superclass argument.
/// Positions refer to the class that declares this superclass list.
#[derive(Debug)]
pub struct ParameterUse {
    pub position: u32,
    pub polarity: Polarity,
    pub span: Span,
}

/// Direction of a parameter use after composing constructor variance.
#[derive(Debug, Clone, Copy)]
pub enum Polarity {
    Positive,
    Negative,
    Both,
}

impl Polarity {
    fn reversed(self) -> Self {
        match self {
            Self::Positive => Self::Negative,
            Self::Negative => Self::Positive,
            Self::Both => Self::Both,
        }
    }

    fn through(self, variance: Variance) -> Self {
        match variance {
            Variance::Invariant => Self::Both,
            Variance::Covariant => self,
            Variance::Contravariant => self.reversed(),
        }
    }
}

// Source spans do not affect template identity. Stable normalization keeps the
// first occurrence of equal parameters, including inside equal constructors.
#[derive(Debug)]
struct ParameterOccurrence {
    parameter: ClassParamRef,
    span: Span,
}

impl PartialEq for ParameterOccurrence {
    fn eq(&self, other: &Self) -> bool {
        self.parameter == other.parameter
    }
}
impl Eq for ParameterOccurrence {}
impl PartialOrd for ParameterOccurrence {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for ParameterOccurrence {
    fn cmp(&self, other: &Self) -> Ordering {
        self.parameter.cmp(&other.parameter)
    }
}

/// Resolution of one class's superclass arguments under its parameter scope.
struct TemplateResolver<'a> {
    declarations: &'a Declarations,
    names: &'a NameLookup,
    positions: &'a BTreeMap<&'a str, ClassParamRef>,
}

/// Look up a class root and check its argument count before resolving its
/// argument contents.
///
/// An undeclared name fails before the argument count is checked.
pub fn resolve_class_root(
    name: &Ident,
    arguments: Option<&ClassArguments>,
    declarations: &Declarations,
    names: &NameLookup,
) -> Result<ClassId, Diagnostic> {
    let Some(class) = names.lookup_class(&name.name) else {
        return Err(diagnostic(
            name.span,
            DiagnosticKind::UndeclaredName {
                kind: RefKind::Class,
                name: name.name.clone(),
            },
        ));
    };
    let expected = declarations.class_arity(class);
    let actual = arguments.map_or(0, |arguments| arguments.operands().count());
    let class_name = || declarations.class_name(class).to_owned();
    match (expected, arguments) {
        (0, None) => Ok(class),
        (0, Some(arguments)) => Err(diagnostic(
            arguments.open_bracket,
            DiagnosticKind::ClassArguments {
                name: class_name(),
                mismatch: ClassArgumentMismatch::Unexpected,
            },
        )),
        (_, None) => Err(diagnostic(
            name.span,
            DiagnosticKind::ClassArguments {
                name: class_name(),
                mismatch: ClassArgumentMismatch::Missing { expected },
            },
        )),
        (_, Some(arguments)) if expected != actual => Err(diagnostic(
            Span::new(
                arguments.open_bracket.start(),
                arguments.close_bracket.end(),
            ),
            DiagnosticKind::ClassArguments {
                name: class_name(),
                mismatch: ClassArgumentMismatch::Count { expected, actual },
            },
        )),
        (_, Some(_)) => Ok(class),
    }
}

/// Reject forbidden source forms before normalization can remove them.
fn check_superclass_argument(ty: &TypeExpr) -> Result<(), Diagnostic> {
    match ty {
        TypeExpr::MetaName(name) => {
            return Err(diagnostic(
                name.span,
                DiagnosticKind::MetavarSuperclassArgument {
                    name: name.name.clone(),
                },
            ));
        }
        TypeExpr::Generic(node) => {
            return Err(diagnostic(
                node.keyword,
                DiagnosticKind::GenericSuperclassArgument,
            ));
        }
        TypeExpr::Name(_) => {}
        TypeExpr::ClassApplication(node) => {
            for argument in node.arguments.operands() {
                check_superclass_argument(argument)?;
            }
        }
        TypeExpr::Tuple(node) => {
            for element in &node.elements {
                check_superclass_argument(element)?;
            }
        }
        TypeExpr::Callable(node) => {
            for parameter in &node.params {
                check_superclass_argument(parameter)?;
            }
            check_superclass_argument(&node.ret)?;
        }
        TypeExpr::Union(node) | TypeExpr::Intersection(node) => {
            for child in node.operands() {
                check_superclass_argument(child)?;
            }
        }
        TypeExpr::Paren(node) => check_superclass_argument(&node.inner)?,
    }
    Ok(())
}

/// Resolve superclass roots in the class table and arguments in local scope.
pub fn resolve_class(
    record: CollectedClass,
    declarations: &Declarations,
    names: &NameLookup,
) -> Result<ResolvedClass, Diagnostic> {
    let CollectedClass {
        id,
        span,
        superclasses,
    } = record;
    let positions: BTreeMap<&str, ClassParamRef> = declarations
        .class_parameters(id)
        .enumerate()
        .map(|(position, parameter)| {
            (
                parameter.name(),
                ClassParamRef {
                    owner: id,
                    position: checked_u32(position, "class parameter position"),
                },
            )
        })
        .collect();
    let resolver = TemplateResolver {
        declarations,
        names,
        positions: &positions,
    };
    let mut resolved_superclasses = Vec::with_capacity(superclasses.len());
    for superclass in superclasses {
        let class = resolve_class_root(
            &superclass.name,
            superclass.arguments.as_ref(),
            declarations,
            names,
        )?;
        if let Some(arguments) = &superclass.arguments {
            for argument in arguments.operands() {
                check_superclass_argument(argument)?;
            }
        }
        let arguments = match superclass.arguments {
            Some(arguments) => resolver.resolve_children(arguments.into_operands())?,
            None => Vec::new(),
        };
        let mut parameter_uses = Vec::new();
        let arguments = arguments
            .into_iter()
            .zip(declarations.class_parameters(class))
            .map(|(argument, parameter)| {
                resolver.finish_template(
                    argument,
                    Polarity::Positive.through(parameter.variance()),
                    &mut parameter_uses,
                )
            })
            .collect();
        resolved_superclasses.push(ResolvedSuperclass {
            name_span: superclass.name.span,
            span: superclass.span,
            parameter_uses,
            template: ClassType { class, arguments },
        });
    }
    Ok(ResolvedClass {
        id,
        span,
        superclasses: resolved_superclasses,
    })
}

impl TemplateResolver<'_> {
    /// The source scan has excluded metavariables and generic callables.
    /// Normalize children before their parent, retaining spans only on parameters.
    fn resolve_template(
        &self,
        ty: TypeExpr,
    ) -> Result<TemplateType<ParameterOccurrence>, Diagnostic> {
        let ty = match ty {
            TypeExpr::Name(name) => {
                if let Some(reference) = self.positions.get(name.name.as_str()) {
                    TemplateType::Parameter {
                        reference: ParameterOccurrence {
                            parameter: *reference,
                            span: name.span,
                        },
                    }
                } else {
                    TemplateType::Class(ClassType::plain(resolve_class_root(
                        &name,
                        None,
                        self.declarations,
                        self.names,
                    )?))
                }
            }
            TypeExpr::ClassApplication(node) => return self.resolve_template_application(node),
            TypeExpr::MetaName(_) | TypeExpr::Generic(_) => {
                panic!("forbidden source form passed the superclass argument scan")
            }
            TypeExpr::Tuple(node) => TemplateType::Tuple(self.resolve_children(node.elements)?),
            TypeExpr::Callable(node) => TemplateType::Callable {
                params: self.resolve_children(node.params)?,
                ret: Box::new(self.resolve_template(*node.ret)?),
            },
            TypeExpr::Union(node) => {
                TemplateType::Union(self.resolve_children(node.into_operands())?)
            }
            TypeExpr::Intersection(node) => {
                TemplateType::Intersection(self.resolve_children(node.into_operands())?)
            }
            TypeExpr::Paren(node) => return self.resolve_template(*node.inner),
        };
        Ok(normalize_template(ty))
    }

    fn resolve_children(
        &self,
        children: impl IntoIterator<Item = TypeExpr>,
    ) -> Result<Vec<TemplateType<ParameterOccurrence>>, Diagnostic> {
        children
            .into_iter()
            .map(|child| self.resolve_template(child))
            .collect()
    }

    /// Class roots are checked before their arguments are resolved.
    fn resolve_template_application(
        &self,
        node: ClassApplication,
    ) -> Result<TemplateType<ParameterOccurrence>, Diagnostic> {
        if self.positions.contains_key(node.name.name.as_str()) {
            return Err(diagnostic(
                node.name.span,
                DiagnosticKind::ParameterClassApplication {
                    name: node.name.name,
                },
            ));
        }
        let class = resolve_class_root(
            &node.name,
            Some(&node.arguments),
            self.declarations,
            self.names,
        )?;
        let arguments = self.resolve_children(node.arguments.into_operands())?;
        Ok(TemplateType::Class(ClassType { class, arguments }))
    }

    /// Discard source data after recording the polarity and span of each surviving
    /// parameter. Published templates contain declaration coordinates only.
    fn finish_template(
        &self,
        ty: TemplateType<ParameterOccurrence>,
        polarity: Polarity,
        uses: &mut Vec<ParameterUse>,
    ) -> TemplateType {
        match ty {
            TemplateType::Parameter { reference } => {
                uses.push(ParameterUse {
                    position: reference.parameter.position,
                    polarity,
                    span: reference.span,
                });
                TemplateType::Parameter {
                    reference: reference.parameter,
                }
            }
            TemplateType::Class(class) => {
                let arguments = class
                    .arguments
                    .into_iter()
                    .zip(self.declarations.class_parameters(class.class))
                    .map(|(argument, parameter)| {
                        self.finish_template(argument, polarity.through(parameter.variance()), uses)
                    })
                    .collect();
                TemplateType::Class(ClassType {
                    class: class.class,
                    arguments,
                })
            }
            TemplateType::Tuple(children) => TemplateType::Tuple(
                children
                    .into_iter()
                    .map(|child| self.finish_template(child, polarity, uses))
                    .collect(),
            ),
            TemplateType::Callable { params, ret } => TemplateType::Callable {
                params: params
                    .into_iter()
                    .map(|child| self.finish_template(child, polarity.reversed(), uses))
                    .collect(),
                ret: Box::new(self.finish_template(*ret, polarity, uses)),
            },
            TemplateType::Union(children) => TemplateType::Union(
                children
                    .into_iter()
                    .map(|child| self.finish_template(child, polarity, uses))
                    .collect(),
            ),
            TemplateType::Intersection(children) => TemplateType::Intersection(
                children
                    .into_iter()
                    .map(|child| self.finish_template(child, polarity, uses))
                    .collect(),
            ),
        }
    }
}

/// Stable sorting keeps the first source occurrence among equal children.
/// Absorbing and neutral elements remove ineffective parameter uses.
fn normalize_template<P: Ord>(ty: TemplateType<P>) -> TemplateType<P> {
    let (junction, children) = match ty {
        TemplateType::Union(children) => (Junction::Union, children),
        TemplateType::Intersection(children) => (Junction::Intersection, children),
        ty => return ty,
    };
    let mut flattened = Vec::new();
    for child in children {
        match (child, junction) {
            (TemplateType::Union(children), Junction::Union)
            | (TemplateType::Intersection(children), Junction::Intersection) => {
                flattened.extend(children);
            }
            (child, _) => flattened.push(child),
        }
    }
    let absorbing = TemplateType::Class(ClassType::plain(junction.absorbing()));
    let neutral = TemplateType::Class(ClassType::plain(junction.neutral()));
    flattened.retain(|child| *child != neutral);
    flattened.sort();
    flattened.dedup();
    if let Some(index) = flattened.iter().position(|child| *child == absorbing) {
        return flattened.remove(index);
    }
    match flattened.as_slice() {
        [] => neutral,
        [_] => flattened.remove(0),
        _ => match junction {
            Junction::Union => TemplateType::Union(flattened),
            Junction::Intersection => TemplateType::Intersection(flattened),
        },
    }
}

/// Replace parameters owned by the base declaration without substituting again
/// inside actual arguments. Constructors retain their argument structure.
///
/// # Panics
///
/// Panics if a parameter belongs to another owner or exceeds its argument list.
pub fn substitute(ty: &TemplateType, owner: ClassId, arguments: &[TemplateType]) -> TemplateType {
    let child = |child: &TemplateType| substitute(child, owner, arguments);
    let replaced = match ty {
        TemplateType::Parameter { reference } => {
            assert_eq!(
                reference.owner, owner,
                "template parameter belongs to a different class"
            );
            let Some(argument) = arguments.get(reference.position as usize) else {
                panic!("template parameter exceeds the base argument count: {reference:?}");
            };
            return argument.clone();
        }
        TemplateType::Class(class) => TemplateType::Class(class.map(child)),
        TemplateType::Tuple(elements) => TemplateType::Tuple(elements.iter().map(child).collect()),
        TemplateType::Callable { params, ret } => TemplateType::Callable {
            params: params.iter().map(child).collect(),
            ret: Box::new(child(ret)),
        },
        TemplateType::Union(members) => TemplateType::Union(members.iter().map(child).collect()),
        TemplateType::Intersection(members) => {
            TemplateType::Intersection(members.iter().map(child).collect())
        }
    };
    normalize_template(replaced)
}

/// Render normalized templates with their declaring parameter names.
///
/// # Panics
///
/// Panics if a parameter position exceeds its declaration's parameter list.
#[must_use]
pub fn render(ty: &TemplateType, declarations: &Declarations) -> String {
    match ty {
        TemplateType::Parameter { reference } => {
            let Some(parameter) = declarations
                .class_parameters(reference.owner)
                .nth(reference.position as usize)
            else {
                panic!("template parameter exceeds its declaration: {reference:?}");
            };
            parameter.name().to_owned()
        }
        TemplateType::Class(application) => {
            let name = declarations.class_name(application.class);
            if application.arguments.is_empty() {
                name.to_owned()
            } else {
                format!(
                    "{name}[{}]",
                    application
                        .arguments
                        .iter()
                        .map(|child| render(child, declarations))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
        TemplateType::Tuple(children) => format!(
            "tuple[{}]",
            children
                .iter()
                .map(|child| render(child, declarations))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        TemplateType::Callable { params, ret } => format!(
            "({}) -> {}",
            params
                .iter()
                .map(|child| render(child, declarations))
                .collect::<Vec<_>>()
                .join(", "),
            render(ret, declarations)
        ),
        TemplateType::Union(children) => render_junction(children, declarations, " | "),
        TemplateType::Intersection(children) => render_junction(children, declarations, " & "),
    }
}

fn render_junction(
    children: &[TemplateType],
    declarations: &Declarations,
    separator: &str,
) -> String {
    children
        .iter()
        .map(|child| match child {
            TemplateType::Callable { .. }
            | TemplateType::Union(_)
            | TemplateType::Intersection(_) => {
                format!("({})", render(child, declarations))
            }
            TemplateType::Parameter { .. } | TemplateType::Class(_) | TemplateType::Tuple(_) => {
                render(child, declarations)
            }
        })
        .collect::<Vec<_>>()
        .join(separator)
}
