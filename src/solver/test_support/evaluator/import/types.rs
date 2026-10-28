//! Substitute model roots into source and canonical expressions.

use std::collections::BTreeMap;

use crate::frontend::problem::{AtomFormula, MetaVarId, TypeId, TypeNode};
use crate::frontend::test_support::Formula;
use crate::solver::input::Input;

use super::super::{Graph, Type};
use super::Condition;
use super::source;

impl Graph {
    fn canonical(
        &mut self,
        root: TypeId,
        input: &Input<'_>,
        variables: &BTreeMap<MetaVarId, usize>,
    ) -> Option<usize> {
        let result = self.add(Type::Never, Vec::new());
        let mut pending = vec![(result, root, Vec::new())];
        let mut memo = BTreeMap::from([((root, Vec::new()), result)]);
        while let Some((id, source, mut scope)) = pending.pop() {
            let node = input.types().type_node(source);
            if matches!(node, TypeNode::Generic(_)) {
                scope.push(id);
            }
            let add = |child: &TypeId| {
                let key = (*child, scope.clone());
                if let Some(id) = memo.get(&key) {
                    return *id;
                }
                let id = self.add(Type::Never, scope.clone());
                memo.insert(key, id);
                pending.push((id, *child, scope.clone()));
                id
            };
            let kind = match node {
                TypeNode::Bound(reference) => Type::Bound {
                    owner: *scope.iter().rev().nth(reference.binder() as usize)?,
                    position: reference.position() as usize,
                },
                TypeNode::Flexible(variable) => Type::Reference(*variables.get(variable)?),
                TypeNode::Class(class) => Type::Class {
                    class: class.class.index(),
                    arguments: class.arguments.iter().map(add).collect(),
                },
                TypeNode::Tuple(children) => Type::Tuple(children.iter().map(add).collect()),
                TypeNode::Callable(body) => Type::Callable(body.map(add)),
                TypeNode::Generic(generic) => Type::Generic {
                    parameters: generic.parameters.get() as usize,
                    body: generic.body.map(add),
                },
                TypeNode::Union(children) => Type::Union(children.iter().map(add).collect()),
                TypeNode::Intersection(children) => {
                    Type::Intersection(children.iter().map(add).collect())
                }
            };
            self.nodes[id].kind = kind;
        }
        Some(result)
    }
}

pub fn canonical_conditions(
    graph: &mut Graph,
    input: &Input<'_>,
    formulas: &[&AtomFormula],
    variables: &BTreeMap<MetaVarId, usize>,
    conditions: &mut Vec<Condition>,
) -> Option<Vec<usize>> {
    let mut results = Vec::new();
    let mut roots = Vec::new();
    for formula in formulas {
        let mut pending = vec![(*formula, false)];
        while let Some((formula, finished)) = pending.pop() {
            let condition = match formula {
                AtomFormula::Atom(atom) => {
                    let atom = input.atoms().atom(*atom);
                    Condition::Compare(
                        graph.canonical(atom.lower, input, variables)?,
                        graph.canonical(atom.upper, input, variables)?,
                    )
                }
                AtomFormula::Conjunction(children) | AtomFormula::Disjunction(children) => {
                    if !finished {
                        pending.push((formula, true));
                        pending.extend(children.iter().rev().map(|child| (child, false)));
                        continue;
                    }
                    let children = results.split_off(results.len() - children.len());
                    if matches!(formula, AtomFormula::Conjunction(_)) {
                        Condition::All(children)
                    } else {
                        Condition::Any(children)
                    }
                }
            };
            results.push(conditions.len());
            conditions.push(condition);
        }
        roots.push(results.pop()?);
    }
    Some(roots)
}

pub fn source_conditions(
    graph: &mut Graph,
    formulas: &[&Formula],
    classes: &BTreeMap<String, usize>,
    variables: &BTreeMap<String, usize>,
    conditions: &mut Vec<Condition>,
) -> Option<Vec<usize>> {
    let mut results = Vec::new();
    let mut roots = Vec::new();
    for formula in formulas {
        let mut pending = vec![(*formula, false)];
        while let Some((formula, finished)) = pending.pop() {
            let (all, children) = match formula {
                Formula::Subtype(atom) => {
                    let condition = Condition::Compare(
                        source::read(graph, &atom.left, classes, variables)?,
                        source::read(graph, &atom.right, classes, variables)?,
                    );
                    results.push(conditions.len());
                    conditions.push(condition);
                    continue;
                }
                Formula::Paren(group) => {
                    pending.push((&group.inner, false));
                    continue;
                }
                Formula::And(parts) => (true, parts.operands().collect::<Vec<_>>()),
                Formula::Or(parts) => (false, parts.operands().collect()),
            };
            if !finished {
                pending.push((formula, true));
                pending.extend(children.into_iter().rev().map(|child| (child, false)));
                continue;
            }
            let children = results.split_off(results.len() - children.len());
            results.push(conditions.len());
            conditions.push(if all {
                Condition::All(children)
            } else {
                Condition::Any(children)
            });
        }
        roots.push(results.pop()?);
    }
    Some(roots)
}
