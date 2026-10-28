//! Rules for comparing class, tuple, and function types.
//!
//! Final checks use expressions with variables already replaced. These checks
//! leave the chosen values unchanged.

use crate::frontend::problem::{Callable, ClassId, ClassType, ClassVariance};

use super::super::super::ClassRelation;
use super::super::graph::{FactorNode, Graph, SFactor, SValue};
use super::super::identities::{ClassDirection, PathStep};
use super::{Child, Comparison, EdgeKind};

/// Return the extra checks required by two types.
/// The caller has already handled variables that stand alone.
/// Record a step that uses a superclass declaration before checking its arguments.
pub fn constructor_children(
    graph: &Graph,
    lower: &SFactor,
    upper: &SFactor,
    relation: &ClassRelation<'_>,
) -> Option<Vec<Child>> {
    if lower == upper || upper.node() == &FactorNode::Class(ClassType::OBJECT) {
        return Some(Vec::new());
    }
    let mut children = Vec::new();
    let mut add = |lower: &SValue, upper: &SValue, path: Vec<PathStep>| {
        children.push(Child {
            comparison: Comparison {
                lower: lower.clone(),
                upper: upper.clone(),
            },
            kind: EdgeKind::Constructor,
            path,
        });
    };
    match (lower.node(), upper.node()) {
        (FactorNode::Class(lower), FactorNode::Class(upper)) if lower.class == upper.class => {
            for (index, ((lower, upper), parameter)) in lower
                .arguments
                .iter()
                .zip(&upper.arguments)
                .zip(relation.declarations.class_parameters(lower.class))
                .enumerate()
            {
                if parameter.variance() != ClassVariance::Contravariant {
                    add(
                        lower,
                        upper,
                        vec![
                            PathStep::ClassArgument(index),
                            PathStep::ClassDirection(ClassDirection::Forward),
                        ],
                    );
                }
                if parameter.variance() != ClassVariance::Covariant {
                    add(
                        upper,
                        lower,
                        vec![
                            PathStep::ClassArgument(index),
                            PathStep::ClassDirection(ClassDirection::Reverse),
                        ],
                    );
                }
            }
        }
        (FactorNode::Class(lower), FactorNode::Class(upper)) => {
            if lower.class == ClassId::NEVER {
                return Some(Vec::new());
            }
            let template = relation.ancestor_template(lower.class, upper.class)?;
            let arguments = graph.ancestor_arguments(lower.class, template, &lower.arguments);
            children.push(Child {
                comparison: Comparison {
                    lower: graph.factor(FactorNode::Class(ClassType {
                        class: upper.class,
                        arguments,
                    })),
                    upper: graph.factor(FactorNode::Class(upper.clone())),
                },
                kind: EdgeKind::Superclass,
                path: Vec::new(),
            });
        }
        (FactorNode::Tuple(lower), FactorNode::Tuple(upper)) if lower.len() == upper.len() => {
            for (index, (lower, upper)) in lower.iter().zip(upper).enumerate() {
                add(lower, upper, vec![PathStep::Tuple(index)]);
            }
        }
        (
            FactorNode::Callable(Callable {
                params: lower,
                ret: lower_ret,
            }),
            FactorNode::Callable(Callable {
                params: upper,
                ret: upper_ret,
            }),
        ) if lower.len() == upper.len() => {
            for (index, (lower, upper)) in lower.iter().zip(upper).enumerate() {
                add(upper, lower, vec![PathStep::Parameter(index)]);
            }
            add(lower_ret, upper_ret, vec![PathStep::Return]);
        }
        (FactorNode::Ref(_), _) | (_, FactorNode::Ref(_)) => {
            panic!("live variable reached constructor comparison");
        }
        _ => return None,
    }
    Some(children)
}
