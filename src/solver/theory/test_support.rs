//! Finite type values used only to construct test expectations.

use std::collections::BTreeMap;
use std::iter;
use std::num::NonZeroU32;

use crate::frontend::problem::{BoundRef, Callable, ClassId, ClassType};

use super::closed::{Value, ValueNode};

/// One factor in a finite type expectation, without solver variables.
/// Bound references retain their coordinates within enclosing generic binders.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum ClosedAtom {
    Bound(BoundRef),
    Class(ClassType<DnfValue>),
    Tuple(Vec<DnfValue>),
    Callable(Box<Callable<DnfValue>>),
    Generic {
        parameters: NonZeroU32,
        body: Box<Callable<DnfValue>>,
    },
}

/// One non-empty intersection in a finite type expectation.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct DnfArm {
    first: ClosedAtom,
    rest: Vec<ClosedAtom>,
}

impl DnfArm {
    /// Construct one expectation arm containing a single factor.
    fn single(factor: ClosedAtom) -> Self {
        Self {
            first: factor,
            rest: Vec::new(),
        }
    }

    fn factors(&self) -> impl Iterator<Item = &ClosedAtom> {
        iter::once(&self.first).chain(&self.rest)
    }

    fn class_ids(&self) -> Vec<ClassId> {
        self.factors()
            .map(|factor| match factor {
                ClosedAtom::Class(application) if application.arguments.is_empty() => {
                    application.class
                }
                ClosedAtom::Bound(_)
                | ClosedAtom::Class(_)
                | ClosedAtom::Tuple(_)
                | ClosedAtom::Callable(_)
                | ClosedAtom::Generic { .. } => {
                    panic!("class-only test value contains a constructor")
                }
            })
            .collect()
    }
}

/// A tree used to build expectations and copy finite checked values.
///
/// An empty arm vector is bottom. This type does not normalize values.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct DnfValue {
    arms: Vec<DnfArm>,
}

impl DnfValue {
    /// Construct the closed bottom value.
    pub fn never() -> Self {
        Self { arms: Vec::new() }
    }

    pub fn class(id: ClassId) -> Self {
        if id == ClassId::NEVER {
            return Self::never();
        }
        Self {
            arms: vec![DnfArm::single(ClosedAtom::Class(ClassType::plain(id)))],
        }
    }

    pub fn tuple(elements: Vec<Self>) -> Self {
        Self {
            arms: vec![DnfArm::single(ClosedAtom::Tuple(elements))],
        }
    }

    pub fn class_arms(&self) -> Vec<Vec<ClassId>> {
        self.arms.iter().map(DnfArm::class_ids).collect()
    }

    /// Copy a finite checked value into the form used by test expectations.
    pub fn from_closed(value: &Value) -> Self {
        assert!(
            !value.contains_recursion(),
            "a recursive value has no finite tree"
        );
        let mut pending = vec![(value.clone(), false)];
        let mut values: BTreeMap<Value, DnfValue> = BTreeMap::new();
        while let Some((value, finished)) = pending.pop() {
            if values.contains_key(&value) {
                continue;
            }
            if !finished {
                pending.push((value.clone(), true));
                let children = match value.node() {
                    ValueNode::Class { arguments, .. } => arguments,
                    ValueNode::Tuple(children)
                    | ValueNode::Union(children)
                    | ValueNode::Intersection(children) => children,
                    ValueNode::Callable(body) | ValueNode::Generic { body, .. } => {
                        body.children().cloned().collect()
                    }
                    _ => Vec::new(),
                };
                pending.extend(children.into_iter().map(|child| (child, false)));
                continue;
            }
            let get = |value: &Value| values[value].clone();
            let factor = match value.node() {
                ValueNode::Never => {
                    values.insert(value, DnfValue::never());
                    continue;
                }
                ValueNode::Union(children) => {
                    let arms = children.iter().flat_map(|child| get(child).arms).collect();
                    values.insert(value, DnfValue { arms });
                    continue;
                }
                ValueNode::Intersection(children) => {
                    let mut factors = children
                        .iter()
                        .flat_map(|child| {
                            get(child)
                                .arms
                                .into_iter()
                                .flat_map(|arm| arm.factors().cloned().collect::<Vec<_>>())
                        })
                        .collect::<Vec<_>>();
                    let first = factors.remove(0);
                    values.insert(
                        value,
                        DnfValue {
                            arms: vec![DnfArm {
                                first,
                                rest: factors,
                            }],
                        },
                    );
                    continue;
                }
                ValueNode::Arbitrary => {
                    panic!("an arbitrary parameter has no closed finite form")
                }
                ValueNode::Bound { coordinate, .. } => ClosedAtom::Bound(coordinate),
                ValueNode::Class {
                    class, arguments, ..
                } => ClosedAtom::Class(ClassType {
                    class,
                    arguments: arguments.iter().map(get).collect(),
                }),
                ValueNode::Tuple(children) => ClosedAtom::Tuple(children.iter().map(get).collect()),
                ValueNode::Callable(body) => ClosedAtom::Callable(Box::new(body.map(get))),
                ValueNode::Generic { parameters, body } => {
                    let Some(parameters) = NonZeroU32::new(parameters) else {
                        panic!("normalized generic has parameters");
                    };
                    ClosedAtom::Generic {
                        parameters,
                        body: Box::new(body.map(get)),
                    }
                }
            };
            values.insert(
                value,
                DnfValue {
                    arms: vec![DnfArm::single(factor)],
                },
            );
        }
        values.remove(value).expect("the root was evaluated")
    }
}
