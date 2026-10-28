//! Read assertion syntax with explicit parameter owners and site scopes.
//!
//! Each exact selection reads the original body. Closed replacements are shared.
//! Open references are created in the scope of each source occurrence.

use std::collections::BTreeMap;

use crate::frontend::problem::Callable;
use crate::frontend::test_support::{
    CallableTypeExpr, GenericCallableTypeExpr, GenericParameterExpr, TypeExpr,
};

use super::super::{Graph, Type};

#[derive(Debug, Clone, Copy)]
enum Replacement {
    Bound {
        owner: usize,
        position: usize,
    },
    Upper {
        owner: usize,
        position: usize,
        upper: usize,
    },
    Exact(usize),
}

enum Restriction {
    Plain,
    Upper(usize),
    Exact { first: usize, rest: Vec<usize> },
}

struct Source<'a> {
    graph: &'a mut Graph,
    classes: &'a BTreeMap<String, usize>,
    variables: &'a BTreeMap<String, usize>,
    binders: Vec<BTreeMap<String, Replacement>>,
    scope: Vec<usize>,
}

/// Read one source type with the supplied complete assignment.
///
/// The source has passed validation, so restrictions contain only closed types.
/// Parameter ownership comes from lexical declarations and each reference site's scope.
pub fn read(
    graph: &mut Graph,
    root: &TypeExpr,
    classes: &BTreeMap<String, usize>,
    variables: &BTreeMap<String, usize>,
) -> Option<usize> {
    Source {
        graph,
        classes,
        variables,
        binders: Vec::new(),
        scope: Vec::new(),
    }
    .value(root)
}

impl Source<'_> {
    fn value(&mut self, expression: &TypeExpr) -> Option<usize> {
        let kind = match expression {
            TypeExpr::Name(name) => {
                let replacement = self
                    .binders
                    .iter()
                    .rev()
                    .find_map(|frame| frame.get(&name.name))
                    .copied();
                match replacement {
                    Some(Replacement::Bound { owner, position }) => Type::Bound { owner, position },
                    Some(Replacement::Upper {
                        owner,
                        position,
                        upper,
                    }) => {
                        let bound = self
                            .graph
                            .add(Type::Bound { owner, position }, self.scope.clone());
                        return Some(
                            self.graph
                                .intersection(vec![bound, upper], self.scope.clone()),
                        );
                    }
                    Some(Replacement::Exact(member)) => return Some(member),
                    None => Type::Class {
                        class: *self.classes.get(&name.name)?,
                        arguments: Vec::new(),
                    },
                }
            }
            TypeExpr::ClassApplication(application) => Type::Class {
                class: *self.classes.get(&application.name.name)?,
                arguments: application
                    .arguments
                    .operands()
                    .map(|argument| self.value(argument))
                    .collect::<Option<Vec<_>>>()?,
            },
            TypeExpr::MetaName(name) => return self.variables.get(&name.name).copied(),
            TypeExpr::Tuple(tuple) => Type::Tuple(
                tuple
                    .elements
                    .iter()
                    .map(|element| self.value(element))
                    .collect::<Option<Vec<_>>>()?,
            ),
            TypeExpr::Callable(callable) => Type::Callable(self.callable(callable)?),
            TypeExpr::Generic(generic) => return self.generic(generic),
            TypeExpr::Union(parts) => Type::Union(
                parts
                    .operands()
                    .map(|child| self.value(child))
                    .collect::<Option<Vec<_>>>()?,
            ),
            TypeExpr::Intersection(parts) => Type::Intersection(
                parts
                    .operands()
                    .map(|child| self.value(child))
                    .collect::<Option<Vec<_>>>()?,
            ),
            TypeExpr::Paren(group) => return self.value(&group.inner),
        };
        Some(self.graph.add(kind, self.scope.clone()))
    }

    fn callable(&mut self, callable: &CallableTypeExpr) -> Option<Callable<usize>> {
        let params = callable
            .params
            .iter()
            .map(|param| self.value(param))
            .collect::<Option<Vec<_>>>()?;
        let ret = self.value(&callable.ret)?;
        Some(Callable { params, ret })
    }

    fn restrictions(&mut self, generic: &GenericCallableTypeExpr) -> Option<Vec<Restriction>> {
        generic
            .parameters
            .iter()
            .map(|parameter| {
                Some(match parameter {
                    GenericParameterExpr::Plain { .. } => Restriction::Plain,
                    GenericParameterExpr::UpperBound { upper, .. } => {
                        Restriction::Upper(self.value(upper)?)
                    }
                    GenericParameterExpr::ExactSet { first, rest, .. } => Restriction::Exact {
                        first: self.value(first)?,
                        rest: rest
                            .iter()
                            .map(|member| self.value(member))
                            .collect::<Option<Vec<_>>>()?,
                    },
                })
            })
            .collect()
    }

    fn generic(&mut self, generic: &GenericCallableTypeExpr) -> Option<usize> {
        // Restrictions are closed and are read before the new name frame exists.
        let restrictions = self.restrictions(generic)?;
        let exact = restrictions
            .iter()
            .enumerate()
            .filter_map(|(position, restriction)| {
                if let Restriction::Exact { first, rest } = restriction {
                    Some((position, *first, rest.as_slice()))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        let mut selected = exact
            .iter()
            .map(|(position, first, _)| (*position, *first))
            .collect::<BTreeMap<_, _>>();
        let mut remaining = exact
            .iter()
            .map(|(_, _, rest)| rest.iter())
            .collect::<Vec<_>>();
        let parameters = restrictions.len() - exact.len();
        let mut alternatives = Vec::new();
        'selections: loop {
            let id = self.graph.add(Type::Never, self.scope.clone());
            let mut frame = BTreeMap::new();
            let mut position = 0;
            for (index, (parameter, restriction)) in
                generic.parameters.iter().zip(&restrictions).enumerate()
            {
                let replacement = match restriction {
                    Restriction::Plain => Replacement::Bound {
                        owner: id,
                        position,
                    },
                    Restriction::Upper(upper) => Replacement::Upper {
                        owner: id,
                        position,
                        upper: *upper,
                    },
                    Restriction::Exact { .. } => Replacement::Exact(selected[&index]),
                };
                if !matches!(restriction, Restriction::Exact { .. }) {
                    position += 1;
                }
                frame.insert(parameter.name().name.clone(), replacement);
            }
            self.binders.push(frame);
            if parameters != 0 {
                self.scope.push(id);
            }
            let body = self.callable(&generic.body)?;
            if parameters != 0 {
                self.scope.pop();
            }
            self.binders.pop();
            self.graph.nodes[id].kind = if parameters == 0 {
                Type::Callable(body)
            } else {
                Type::Generic { parameters, body }
            };
            alternatives.push(id);
            for ((position, first, rest), remaining) in exact.iter().zip(&mut remaining).rev() {
                if let Some(member) = remaining.next() {
                    selected.insert(*position, *member);
                    continue 'selections;
                }
                selected.insert(*position, *first);
                *remaining = rest.iter();
            }
            break;
        }
        Some(self.graph.intersection(alternatives, self.scope.clone()))
    }
}
