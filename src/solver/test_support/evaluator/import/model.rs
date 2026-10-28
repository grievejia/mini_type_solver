//! Copy model occurrences with their saved owners into one independent graph.
//!
//! A repeated occurrence must map to the same saved scope. Owner handles are
//! matched by binding identity. Owner links never become type-cycle edges.

use crate::frontend::problem::Callable;
use crate::solver::{AssignedNode, AssignedValue};

use super::super::Type;
use super::{ImportedNode, ModelImport};

type Environment = Vec<(AssignedValue, usize)>;
type Pending = Vec<(usize, AssignedValue, Environment)>;

impl ModelImport<'_> {
    /// Memoize each occurrence before reading children, so type cycles terminate.
    /// A missing required owner or a conflicting saved scope fails the import.
    pub fn assigned_value(&mut self, root: &AssignedValue) -> Option<usize> {
        let mut pending = Vec::new();
        let root = self.include(root.clone(), &Vec::new(), &mut pending)?;
        while let Some((id, value, mut environment)) = pending.pop() {
            let kind = match value.node() {
                AssignedNode::Never => Type::Never,
                AssignedNode::Bound { owner, position } => Type::Bound {
                    owner: environment
                        .iter()
                        .find(|(candidate, _)| candidate.same_binding(&owner))?
                        .1,
                    position: position as usize,
                },
                AssignedNode::Class { name, arguments } => Type::Class {
                    class: *self.classes.get(&name)?,
                    arguments: arguments
                        .into_iter()
                        .map(|child| self.edge(child, &environment, &mut pending))
                        .collect::<Option<Vec<_>>>()?,
                },
                AssignedNode::Tuple(children) => Type::Tuple(
                    children
                        .into_iter()
                        .map(|child| self.edge(child, &environment, &mut pending))
                        .collect::<Option<Vec<_>>>()?,
                ),
                AssignedNode::Callable(body) => {
                    Type::Callable(self.callable(body, &environment, &mut pending)?)
                }
                AssignedNode::Generic { parameters, body } => {
                    environment.push((value.clone(), id));
                    Type::Generic {
                        parameters: parameters as usize,
                        body: self.callable(body, &environment, &mut pending)?,
                    }
                }
                AssignedNode::Union(children) => Type::Union(
                    children
                        .into_iter()
                        .map(|child| self.edge(child, &environment, &mut pending))
                        .collect::<Option<Vec<_>>>()?,
                ),
                AssignedNode::Intersection(children) => Type::Intersection(
                    children
                        .into_iter()
                        .map(|child| self.edge(child, &environment, &mut pending))
                        .collect::<Option<Vec<_>>>()?,
                ),
            };
            self.graph.nodes[id].kind = kind;
        }
        Some(root)
    }

    fn callable(
        &mut self,
        body: Callable<AssignedValue>,
        environment: &Environment,
        pending: &mut Pending,
    ) -> Option<Callable<usize>> {
        Some(Callable {
            params: body
                .params
                .into_iter()
                .map(|child| self.edge(child, environment, pending))
                .collect::<Option<Vec<_>>>()?,
            ret: self.edge(body.ret, environment, pending)?,
        })
    }

    fn include(
        &mut self,
        value: AssignedValue,
        environment: &Environment,
        pending: &mut Pending,
    ) -> Option<usize> {
        // Saved scope, rather than traversal depth, determines the environment.
        // An absent saved owner can be unused. Bound queries still require theirs.
        let environment = value
            .binding_scope()
            .into_iter()
            .filter_map(|owner| {
                environment
                    .iter()
                    .find(|(candidate, _)| candidate.same_binding(&owner))
                    .cloned()
            })
            .collect::<Environment>();
        let scope = environment.iter().map(|(_, id)| *id).collect::<Vec<_>>();
        let occurrence = value.id();
        if let Some(imported) = self.memo.get(&occurrence) {
            return (imported.scope == scope).then_some(imported.node);
        }
        let node = self.graph.add(Type::Never, scope.clone());
        self.memo.insert(occurrence, ImportedNode { node, scope });
        pending.push((node, value, environment));
        Some(node)
    }

    fn edge(
        &mut self,
        child: AssignedValue,
        environment: &Environment,
        pending: &mut Pending,
    ) -> Option<usize> {
        let scope = environment.iter().map(|(_, id)| *id).collect::<Vec<_>>();
        let open = !child.binding_scope().is_empty();
        let target = self.include(child, environment, pending)?;
        let saved = &self.graph.nodes[target].scope;
        if !open || *saved == scope {
            return Some(target);
        }
        if !scope.starts_with(saved) {
            return None;
        }
        Some(self.graph.add(Type::Reference(target), scope))
    }
}
