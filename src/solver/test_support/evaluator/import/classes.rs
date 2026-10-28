//! Read direct class templates without creating ordinary type graph nodes.

use std::collections::BTreeMap;

use crate::frontend::problem::{Callable, ClassVariance};
use crate::frontend::test_support::{
    ClassArguments, ClassParameters, Declaration, TypeExpr, VarianceExpr,
};

use super::super::{ClassRule, Graph, Template, TemplateId, Type};

/// Build direct class rules from syntax and the supplied class identities.
///
/// Argument checks use complete headers for every class. Template children
/// precede their parents. No template node enters the ordinary type graph.
pub fn class_rules(
    declarations: &[Declaration],
    names: &BTreeMap<String, usize>,
) -> Option<Vec<ClassRule>> {
    let mut classes = (0..names.len())
        .map(|_| ClassRule {
            variances: Vec::new(),
            templates: Vec::new(),
            direct: Vec::new(),
        })
        .collect::<Vec<_>>();
    for declaration in declarations {
        if let Declaration::Class(class) = declaration {
            let id = *names.get(&class.name.name)?;
            classes.get_mut(id)?.variances = class
                .parameters
                .iter()
                .flat_map(ClassParameters::operands)
                .map(|parameter| match parameter.variance {
                    VarianceExpr::Invariant => ClassVariance::Invariant,
                    VarianceExpr::Covariant(_) => ClassVariance::Covariant,
                    VarianceExpr::Contravariant(_) => ClassVariance::Contravariant,
                })
                .collect();
        }
    }
    for declaration in declarations {
        let Declaration::Class(class) = declaration else {
            continue;
        };
        let parameters = class
            .parameters
            .iter()
            .flat_map(ClassParameters::operands)
            .enumerate()
            .map(|(position, parameter)| (parameter.name.name.clone(), position))
            .collect();
        let mut templates = Vec::new();
        let mut direct = Vec::new();
        for base in &class.superclasses {
            let upper = *names.get(&base.name.name)?;
            let arguments = base
                .arguments
                .iter()
                .flat_map(ClassArguments::operands)
                .collect::<Vec<_>>();
            if classes.get(upper)?.variances.len() != arguments.len() {
                return None;
            }
            let arguments = arguments
                .into_iter()
                .map(|argument| {
                    read_template(argument, names, &classes, &parameters, &mut templates)
                })
                .collect::<Option<Vec<_>>>()?;
            direct.push((upper, arguments));
        }
        let id = *names.get(&class.name.name)?;
        let class = classes.get_mut(id)?;
        class.templates = templates;
        class.direct = direct;
    }
    Some(classes)
}

fn read_template(
    expression: &TypeExpr,
    names: &BTreeMap<String, usize>,
    classes: &[ClassRule],
    parameters: &BTreeMap<String, usize>,
    templates: &mut Vec<Template>,
) -> Option<TemplateId> {
    let template = match expression {
        TypeExpr::Name(name) => {
            if let Some(position) = parameters.get(&name.name) {
                Template::Parameter(*position)
            } else {
                let class = *names.get(&name.name)?;
                if !classes.get(class)?.variances.is_empty() {
                    return None;
                }
                Template::Class {
                    class,
                    arguments: Vec::new(),
                }
            }
        }
        TypeExpr::ClassApplication(application) => {
            let class = *names.get(&application.name.name)?;
            let actual = application.arguments.operands().count();
            if classes.get(class)?.variances.len() != actual {
                return None;
            }
            let arguments = application
                .arguments
                .operands()
                .map(|argument| read_template(argument, names, classes, parameters, templates))
                .collect::<Option<Vec<_>>>()?;
            Template::Class { class, arguments }
        }
        TypeExpr::Tuple(tuple) => Template::Tuple(
            tuple
                .elements
                .iter()
                .map(|element| read_template(element, names, classes, parameters, templates))
                .collect::<Option<Vec<_>>>()?,
        ),
        TypeExpr::Callable(callable) => {
            let params = callable
                .params
                .iter()
                .map(|param| read_template(param, names, classes, parameters, templates))
                .collect::<Option<Vec<_>>>()?;
            let ret = read_template(&callable.ret, names, classes, parameters, templates)?;
            Template::Callable(Callable { params, ret })
        }
        TypeExpr::Union(parts) => Template::Union(
            parts
                .operands()
                .map(|child| read_template(child, names, classes, parameters, templates))
                .collect::<Option<Vec<_>>>()?,
        ),
        TypeExpr::Intersection(parts) => Template::Intersection(
            parts
                .operands()
                .map(|child| read_template(child, names, classes, parameters, templates))
                .collect::<Option<Vec<_>>>()?,
        ),
        TypeExpr::Paren(group) => {
            return read_template(&group.inner, names, classes, parameters, templates);
        }
        TypeExpr::MetaName(_) | TypeExpr::Generic(_) => return None,
    };
    let id = TemplateId(templates.len());
    templates.push(template);
    Some(id)
}

/// Instantiate one direct superclass's arguments in the expanded class's scope.
/// Actual arguments retain their handles and owners. Every template child was
/// stored before its parent, so the local memo never follows a template cycle.
pub fn instantiate_arguments(
    graph: &mut Graph,
    class: usize,
    roots: &[TemplateId],
    arguments: &[usize],
    scope: &[usize],
) -> Vec<usize> {
    let mut memo = BTreeMap::new();
    let mut pending = roots
        .iter()
        .rev()
        .map(|id| (*id, false))
        .collect::<Vec<_>>();
    while let Some((id, finished)) = pending.pop() {
        if memo.contains_key(&id) {
            continue;
        }
        let template = &graph.classes[class].templates[id.0];
        if !finished {
            pending.push((id, true));
            pending.extend(template.children().into_iter().rev().map(|id| (id, false)));
            continue;
        }
        let value = match template {
            Template::Parameter(position) => arguments[*position],
            Template::Class { class, arguments } => graph.intern(
                Type::Class {
                    class: *class,
                    arguments: arguments.iter().map(|child| memo[child]).collect(),
                },
                scope.to_vec(),
            ),
            Template::Tuple(children) => graph.intern(
                Type::Tuple(children.iter().map(|child| memo[child]).collect()),
                scope.to_vec(),
            ),
            Template::Callable(body) => graph.intern(
                Type::Callable(body.map(|child| memo[child])),
                scope.to_vec(),
            ),
            Template::Union(children) => graph.intern(
                Type::Union(children.iter().map(|child| memo[child]).collect()),
                scope.to_vec(),
            ),
            Template::Intersection(children) => graph.intern(
                Type::Intersection(children.iter().map(|child| memo[child]).collect()),
                scope.to_vec(),
            ),
        };
        memo.insert(id, value);
    }
    roots.iter().map(|root| memo[root]).collect()
}
