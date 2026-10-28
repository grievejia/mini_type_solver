//! Compare fixed values without choosing parameters or changing assignments.
//!
//! A repeated comparison uses only the steps from its active parent chain.
//! Results from such a chain are not cached for use under another parent.

use std::collections::BTreeMap;
use std::vec::IntoIter;

use crate::frontend::problem::{ClassId, ClassVariance};

use super::super::ClassRelation;
use super::{Builder, Value, ValueNode};

#[derive(Debug, Clone, Copy)]
enum Edge {
    Ordinary,
    Constructor,
    Superclass,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Comparison(Value, Value);

#[derive(Debug)]
struct Child {
    comparison: Comparison,
    edge: Edge,
}

/// An empty All accepts; an empty Any rejects.
#[derive(Debug)]
enum Rule {
    All(Vec<Child>),
    Any(Vec<Child>),
}

#[derive(Debug)]
struct Frame {
    comparison: Comparison,
    incoming: Edge,
    all: bool,
    remaining: IntoIter<Child>,
}

struct Comparer<'a, 'b> {
    relation: &'a ClassRelation<'b>,
    ancestors: BTreeMap<(Value, ClassId), Value>,
}

fn children(values: Vec<Value>, other: &Value, reverse: bool) -> Vec<Child> {
    values
        .into_iter()
        .map(|value| Child {
            comparison: if reverse {
                Comparison(other.clone(), value)
            } else {
                Comparison(value, other.clone())
            },
            edge: Edge::Ordinary,
        })
        .collect()
}

impl Comparer<'_, '_> {
    fn rule(&mut self, comparison: &Comparison) -> Rule {
        let Comparison(lower, upper) = comparison;
        let lower_node = lower.node();
        let upper_node = upper.node();
        if let (
            ValueNode::Bound {
                owner: lower_owner,
                position: lower_position,
                ..
            },
            ValueNode::Bound {
                owner: upper_owner,
                position: upper_position,
                ..
            },
        ) = (&lower_node, &upper_node)
        {
            return if lower_owner.same_binding(upper_owner) && lower_position == upper_position {
                Rule::All(Vec::new())
            } else {
                Rule::Any(Vec::new())
            };
        }
        if lower == upper {
            return Rule::All(Vec::new());
        }
        match (&lower_node, &upper_node) {
            (ValueNode::Never, _)
            | (
                _,
                ValueNode::Class {
                    class: ClassId::OBJECT,
                    ..
                },
            ) => return Rule::All(Vec::new()),
            (ValueNode::Union(parts), _) => {
                return Rule::All(children(parts.clone(), upper, false));
            }
            (_, ValueNode::Union(parts)) => return Rule::Any(children(parts.clone(), lower, true)),
            (_, ValueNode::Intersection(parts)) => {
                return Rule::All(children(parts.clone(), lower, true));
            }
            (ValueNode::Intersection(parts), _) => {
                return Rule::Any(children(parts.clone(), upper, false));
            }
            _ => {}
        }
        self.constructors(lower, upper, lower_node, upper_node)
    }

    fn constructors(
        &mut self,
        lower: &Value,
        upper: &Value,
        lower_node: ValueNode,
        upper_node: ValueNode,
    ) -> Rule {
        let mut required = Vec::new();
        let productive = lower.contains_recursion() || upper.contains_recursion();
        let mut add = |lower: Value, upper: Value| {
            required.push(Child {
                comparison: Comparison(lower, upper),
                edge: if productive {
                    Edge::Constructor
                } else {
                    Edge::Ordinary
                },
            });
        };
        match (lower_node, upper_node) {
            (
                ValueNode::Class {
                    class: l,
                    arguments: lower,
                    ..
                },
                ValueNode::Class {
                    class: u,
                    arguments: upper,
                    ..
                },
            ) if l == u => {
                for ((lower, upper), parameter) in lower
                    .into_iter()
                    .zip(upper)
                    .zip(self.relation.declarations.class_parameters(l))
                {
                    if parameter.variance() != ClassVariance::Contravariant {
                        add(lower.clone(), upper.clone());
                    }
                    if parameter.variance() != ClassVariance::Covariant {
                        add(upper, lower);
                    }
                }
            }
            (ValueNode::Class { class: l, .. }, ValueNode::Class { class: u, .. }) => {
                let key = (lower.clone(), u);
                let ancestor = if let Some(ancestor) = self.ancestors.get(&key) {
                    ancestor.clone()
                } else {
                    let Some(template) = self.relation.ancestor_template(l, u) else {
                        return Rule::Any(Vec::new());
                    };
                    let mut builder = Builder::new(self.relation.declarations);
                    let root = builder.ancestor(lower, template);
                    let mut values = builder.finish(&[root]);
                    let Some(ancestor) = values.pop() else {
                        panic!("superclass construction lost its root");
                    };
                    self.ancestors.insert(key, ancestor.clone());
                    ancestor
                };
                return Rule::All(vec![Child {
                    comparison: Comparison(ancestor, upper.clone()),
                    edge: Edge::Superclass,
                }]);
            }
            (ValueNode::Tuple(lower), ValueNode::Tuple(upper)) if lower.len() == upper.len() => {
                for (lower, upper) in lower.into_iter().zip(upper) {
                    add(lower, upper);
                }
            }
            (ValueNode::Callable(lower), ValueNode::Callable(upper))
                if lower.params.len() == upper.params.len() =>
            {
                for (lower, upper) in lower.params.into_iter().zip(upper.params) {
                    add(upper, lower);
                }
                add(lower.ret, upper.ret);
            }
            _ => return Rule::Any(Vec::new()),
        }
        Rule::All(required)
    }
}

fn repeated(frames: &[Frame], comparison: &Comparison, incoming: Edge) -> Option<bool> {
    let start = frames
        .iter()
        .position(|frame| frame.comparison == *comparison)?;
    let edges = frames[start + 1..]
        .iter()
        .map(|frame| frame.incoming)
        .chain([incoming])
        .collect::<Vec<_>>();
    Some(
        edges.iter().any(|edge| matches!(edge, Edge::Constructor))
            && !edges.iter().any(|edge| matches!(edge, Edge::Superclass)),
    )
}

/// A cycle must contain a constructor step and no superclass step.
/// Only the active parent chain can establish that condition.
pub fn is_subtype(lower: &Value, upper: &Value, relation: &ClassRelation<'_>) -> bool {
    let mut comparer = Comparer {
        relation,
        ancestors: BTreeMap::new(),
    };
    let mut frames = Vec::new();
    let mut next = Some(Child {
        comparison: Comparison(lower.clone(), upper.clone()),
        edge: Edge::Ordinary,
    });
    let mut result = None;
    loop {
        if let Some(child) = next.take() {
            if let Some(accepted) = repeated(&frames, &child.comparison, child.edge) {
                result = Some(accepted);
            } else {
                let (all, children) = match comparer.rule(&child.comparison) {
                    Rule::All(children) => (true, children),
                    Rule::Any(children) => (false, children),
                };
                let mut remaining = children.into_iter();
                next = remaining.next();
                if next.is_none() {
                    result = Some(all);
                } else {
                    frames.push(Frame {
                        comparison: child.comparison,
                        incoming: child.edge,
                        all,
                        remaining,
                    });
                    continue;
                }
            }
        }
        let Some(accepted) = result.take() else {
            panic!("comparison has no child or result");
        };
        let Some(frame) = frames.last_mut() else {
            return accepted;
        };
        if accepted == frame.all {
            next = frame.remaining.next();
            if next.is_some() {
                continue;
            }
        }
        frames.pop();
        result = Some(accepted);
    }
}
