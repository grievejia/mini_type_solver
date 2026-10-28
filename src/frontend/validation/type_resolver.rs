//! Resolve assertion types in the type store with lexical parameter scopes.
//!
//! Each lexical frame keeps parameter names in declaration order. Bound
//! references use frame depth and parameter position. Source declarations
//! supply diagnostic spans.
//! Restrictions are closed types. Each complete selection rewrites the
//! original callable body before unused parameters are removed and live
//! positions are renumbered.

use std::collections::BTreeSet;

use super::super::ast::{
    CallableTypeExpr, ClassApplication, GenericCallableTypeExpr, GenericParameterExpr, TypeExpr,
};
use super::super::diagnostic::{Diagnostic, DiagnosticKind, NameKind, RefKind, diagnostic};
use super::{
    BinderReplacement, BoundRef, Callable, Declarations, NameLookup, TypeBuilder, TypeId,
    checked_u32, classes, live_bound_positions,
};

#[derive(Debug)]
enum Restriction {
    Plain,
    Upper(TypeId),
    Exact { first: TypeId, rest: Vec<TypeId> },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Context {
    Body,
    Restriction,
}

/// Own lexical names and borrow declarations, name lookup, and the type builder.
#[derive(Debug)]
pub struct TypeResolver<'a> {
    declarations: &'a Declarations,
    names: &'a NameLookup,
    types: &'a mut TypeBuilder,
    binders: Vec<Vec<String>>,
}

impl<'a> TypeResolver<'a> {
    /// Names and class parameters are fixed before assertion resolution starts.
    pub fn new(
        declarations: &'a Declarations,
        names: &'a NameLookup,
        types: &'a mut TypeBuilder,
    ) -> Self {
        Self {
            declarations,
            names,
            types,
            binders: Vec::new(),
        }
    }

    /// Resolve one complete subtype occurrence with no outside binder references.
    pub fn pair(
        &mut self,
        lower: &TypeExpr,
        upper: &TypeExpr,
    ) -> Result<(TypeId, TypeId), Diagnostic> {
        let lower = self.resolve(lower, Context::Body)?;
        let upper = self.resolve(upper, Context::Body)?;
        assert!(
            self.binders.is_empty(),
            "type resolution left a lexical binder open"
        );
        Ok((lower, upper))
    }

    fn named_parameter(&self, name: &str) -> Option<BoundRef> {
        self.binders
            .iter()
            .rev()
            .enumerate()
            .find_map(|(depth, frame)| {
                frame
                    .iter()
                    .position(|parameter| parameter == name)
                    .map(|position| {
                        BoundRef::new(
                            checked_u32(depth, "binder depth"),
                            checked_u32(position, "parameter position"),
                        )
                    })
            })
    }

    fn resolve(&mut self, expr: &TypeExpr, context: Context) -> Result<TypeId, Diagnostic> {
        match expr {
            TypeExpr::Name(name) => {
                if let Some(reference) = self.named_parameter(&name.name) {
                    if context == Context::Restriction {
                        return Err(diagnostic(
                            name.span,
                            DiagnosticKind::ParameterRestriction {
                                name: name.name.clone(),
                            },
                        ));
                    }
                    return Ok(self.types.intern_bound(reference));
                }
                let class = classes::resolve_class_root(name, None, self.declarations, self.names)?;
                Ok(self.types.intern_class(class, Vec::new()))
            }
            TypeExpr::MetaName(name) => {
                if context == Context::Restriction {
                    return Err(diagnostic(
                        name.span,
                        DiagnosticKind::MetavarParameterRestriction {
                            name: name.name.clone(),
                        },
                    ));
                }
                let Some(variable) = self.names.lookup_metavar(&name.name) else {
                    return Err(diagnostic(
                        name.span,
                        DiagnosticKind::UndeclaredName {
                            kind: RefKind::Metavar,
                            name: name.name.clone(),
                        },
                    ));
                };
                Ok(self.types.types().metavar_type(variable))
            }
            TypeExpr::ClassApplication(application) => self.class_application(application, context),
            TypeExpr::Tuple(tuple) => {
                let children = self.resolve_children(tuple.elements.iter(), context)?;
                Ok(self.types.intern_tuple(children))
            }
            TypeExpr::Callable(callable) => {
                let body = self.callable(callable, context)?;
                Ok(self.types.intern_callable(body.params, body.ret))
            }
            TypeExpr::Generic(generic) => {
                if context == Context::Restriction {
                    return Err(diagnostic(
                        generic.keyword,
                        DiagnosticKind::GenericParameterRestriction,
                    ));
                }
                self.resolve_generic(generic)
            }
            TypeExpr::Union(nary) => {
                let children = self.resolve_children(nary.operands(), context)?;
                Ok(self.types.intern_union(children))
            }
            TypeExpr::Intersection(nary) => {
                let children = self.resolve_children(nary.operands(), context)?;
                Ok(self.types.intern_intersection(children))
            }
            TypeExpr::Paren(group) => self.resolve(&group.inner, context),
        }
    }

    /// A parameter cannot be used as a class root. Class arity is checked
    /// before resolving argument contents.
    fn class_application(
        &mut self,
        application: &ClassApplication,
        context: Context,
    ) -> Result<TypeId, Diagnostic> {
        if self.named_parameter(&application.name.name).is_some() {
            let kind = if context == Context::Restriction {
                DiagnosticKind::ParameterRestriction {
                    name: application.name.name.clone(),
                }
            } else {
                DiagnosticKind::ParameterClassApplication {
                    name: application.name.name.clone(),
                }
            };
            return Err(diagnostic(application.name.span, kind));
        }
        let class = classes::resolve_class_root(
            &application.name,
            Some(&application.arguments),
            self.declarations,
            self.names,
        )?;
        let arguments = self.resolve_children(application.arguments.operands(), context)?;
        Ok(self.types.intern_class(class, arguments))
    }

    fn resolve_children<'b>(
        &mut self,
        children: impl Iterator<Item = &'b TypeExpr>,
        context: Context,
    ) -> Result<Vec<TypeId>, Diagnostic> {
        children.map(|child| self.resolve(child, context)).collect()
    }

    fn callable(
        &mut self,
        callable: &CallableTypeExpr,
        context: Context,
    ) -> Result<Callable<TypeId>, Diagnostic> {
        let params = self.resolve_children(callable.params.iter(), context)?;
        let ret = self.resolve(&callable.ret, context)?;
        Ok(Callable { params, ret })
    }

    fn restriction(&mut self, parameter: &GenericParameterExpr) -> Result<Restriction, Diagnostic> {
        match parameter {
            GenericParameterExpr::Plain { .. } => Ok(Restriction::Plain),
            GenericParameterExpr::UpperBound { upper, .. } => Ok(Restriction::Upper(
                self.resolve(upper, Context::Restriction)?,
            )),
            GenericParameterExpr::ExactSet { first, rest, .. } => {
                let first = self.resolve(first, Context::Restriction)?;
                let rest = self.resolve_children(rest.iter(), Context::Restriction)?;
                Ok(Restriction::Exact { first, rest })
            }
        }
    }

    fn resolve_generic(&mut self, generic: &GenericCallableTypeExpr) -> Result<TypeId, Diagnostic> {
        // Duplicate names take priority over built-in names across the whole binder.
        let mut seen = BTreeSet::new();
        for parameter in &generic.parameters {
            let name = parameter.name();
            if !seen.insert(name.name.as_str()) {
                return Err(diagnostic(
                    name.span,
                    DiagnosticKind::DuplicateName {
                        kind: NameKind::TypeParameter,
                        name: name.name.clone(),
                    },
                ));
            }
        }
        for parameter in &generic.parameters {
            let name = parameter.name();
            if Declarations::is_builtin(&name.name) {
                return Err(diagnostic(
                    name.span,
                    DiagnosticKind::BuiltinTypeParameter {
                        name: name.name.clone(),
                    },
                ));
            }
        }
        let names = generic
            .parameters
            .iter()
            .map(|parameter| parameter.name().name.clone())
            .collect();
        self.binders.push(names);
        let restrictions = generic
            .parameters
            .iter()
            .map(|parameter| self.restriction(parameter))
            .collect::<Result<Vec<_>, _>>()?;
        let body = self.callable(&generic.body, Context::Body)?;
        let live = live_bound_positions(
            self.types.types(),
            &body,
            checked_u32(generic.parameters.len(), "parameter count"),
        );
        for (position, parameter) in generic.parameters.iter().enumerate() {
            if !live.contains(&checked_u32(position, "parameter position")) {
                let name = parameter.name();
                return Err(diagnostic(
                    name.span,
                    DiagnosticKind::UnusedTypeParameter {
                        name: name.name.clone(),
                    },
                ));
            }
        }
        let rewritten = self.expand_restrictions(&restrictions, &body);
        self.binders.pop();
        Ok(rewritten)
    }

    /// Each complete selection starts from the original body. An earlier
    /// result can have fewer binders and different parameter positions.
    fn expand_restrictions(
        &mut self,
        restrictions: &[Restriction],
        body: &Callable<TypeId>,
    ) -> TypeId {
        let mut replacements = Vec::with_capacity(restrictions.len());
        let mut exact = Vec::new();
        for (position, restriction) in restrictions.iter().enumerate() {
            replacements.push(match restriction {
                Restriction::Plain => BinderReplacement::Keep,
                Restriction::Upper(bound) => BinderReplacement::Upper(*bound),
                Restriction::Exact { first, rest } => {
                    exact.push((position, *first, rest.as_slice()));
                    BinderReplacement::Exact(*first)
                }
            });
        }
        let mut remaining = exact
            .iter()
            .map(|(_, _, rest)| rest.iter())
            .collect::<Vec<_>>();
        let parameter_count = checked_u32(replacements.len(), "parameter count");
        let mut alternatives = Vec::new();
        'selections: loop {
            let rewritten = self.types.rewrite_binder(body, &replacements);
            alternatives.push(self.types.intern_generic(parameter_count, &rewritten));
            for ((position, first, rest), remaining) in exact.iter().zip(&mut remaining).rev() {
                if let Some(member) = remaining.next() {
                    replacements[*position] = BinderReplacement::Exact(*member);
                    continue 'selections;
                }
                replacements[*position] = BinderReplacement::Exact(*first);
                *remaining = rest.iter();
            }
            break;
        }
        self.types.intern_intersection(alternatives)
    }
}
