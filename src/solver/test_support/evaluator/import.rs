//! Copy public queries into the evaluator's own checked definitions.

mod classes;
mod model;
mod source;
mod types;

pub use classes::{class_rules, instantiate_arguments};

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::frontend::parse;
use crate::frontend::problem::{ClassId, MetaVarId};
use crate::frontend::test_support::{Declaration, Formula};
use crate::solver::{AssignedNodeId, Model, ModelValue};

use super::super::ModelInput;
use super::compare::model_is_subtype;
use super::{Graph, NEVER_INDEX, OBJECT_INDEX, Type};

struct ImportedNode {
    node: usize,
    scope: Vec<usize>,
}

/// The memo belongs to one graph. Each imported occurrence keeps its saved
/// scope, and repeated occurrences share one independent node.
struct ModelImport<'a> {
    graph: &'a mut Graph,
    classes: &'a BTreeMap<String, usize>,
    memo: HashMap<AssignedNodeId, ImportedNode>,
}

enum Condition {
    Compare(usize, usize),
    All(Vec<usize>),
    Any(Vec<usize>),
}

// Source conditions are appended after their children. Every condition belongs
// to a source root, so all children can be evaluated before their parent.
fn conditions_hold(graph: &mut Graph, conditions: &[Condition], roots: &[usize]) -> bool {
    let mut results = vec![false; conditions.len()];
    for (index, condition) in conditions.iter().enumerate() {
        results[index] = match condition {
            Condition::Compare(lower, upper) => model_is_subtype(graph, *lower, *upper),
            Condition::All(children) => children.iter().all(|child| results[*child]),
            Condition::Any(children) => children.iter().any(|child| results[*child]),
        };
    }
    roots.iter().all(|root| results[*root])
}

pub fn class_names(
    input: ModelInput<'_>,
    declarations: &[Declaration],
) -> Option<BTreeMap<String, usize>> {
    if matches!(input, ModelInput::Canonical { .. }) {
        assert_eq!(
            ClassId::OBJECT.index(),
            OBJECT_INDEX,
            "model evaluator object index differs from production ClassId constants"
        );
        assert_eq!(
            ClassId::NEVER.index(),
            NEVER_INDEX,
            "model evaluator never index differs from production ClassId constants"
        );
    }
    let mut classes = BTreeMap::from([
        (String::from("object"), OBJECT_INDEX),
        (String::from("never"), NEVER_INDEX),
    ]);
    for declaration in declarations {
        if let Declaration::Class(class) = declaration {
            let id = match input {
                ModelInput::Source(_) => classes.len(),
                ModelInput::Canonical { input, .. } => {
                    let id = input.declarations().lookup_class(&class.name.name)?;
                    id.index()
                }
            };
            if classes.insert(class.name.name.clone(), id).is_some() {
                return None;
            }
        }
    }
    Some(classes)
}

fn input_conditions(
    graph: &mut Graph,
    input: ModelInput<'_>,
    declarations: &[Declaration],
    classes: &BTreeMap<String, usize>,
    assignment: &BTreeMap<String, usize>,
    conditions: &mut Vec<Condition>,
) -> Option<(BTreeSet<String>, Vec<usize>)> {
    Some(match input {
        ModelInput::Canonical {
            input, formulas, ..
        } => {
            let mut variables: BTreeMap<MetaVarId, usize> = BTreeMap::new();
            for (id, name) in input.declarations().metavars() {
                variables.insert(id, *assignment.get(name)?);
            }
            let roots =
                types::canonical_conditions(graph, input, formulas, &variables, conditions)?;
            (
                input
                    .declarations()
                    .metavars()
                    .map(|(_, name)| name.to_owned())
                    .collect::<BTreeSet<_>>(),
                roots,
            )
        }
        ModelInput::Source(_) => {
            let formulas = declarations
                .iter()
                .filter_map(|declaration| match declaration {
                    Declaration::Assert(assertion) => Some(&assertion.formula),
                    _ => None,
                })
                .collect::<Vec<&Formula>>();
            let roots =
                types::source_conditions(graph, &formulas, classes, assignment, conditions)?;
            (
                declarations
                    .iter()
                    .filter_map(|declaration| match declaration {
                        Declaration::Metavar(variable) => Some(variable.name.name.clone()),
                        _ => None,
                    })
                    .collect(),
                roots,
            )
        }
    })
}

/// Check the public assignment without production comparison or normalization code.
pub fn model_holds(input: ModelInput<'_>, model: &Model) -> bool {
    let declarations = match input {
        ModelInput::Source(source) => source,
        ModelInput::Canonical { declarations, .. } => declarations,
    };
    let Ok(parsed) = parse(declarations) else {
        return false;
    };
    let Some(classes) = class_names(input, parsed.declarations()) else {
        return false;
    };
    let Some(rules) = class_rules(parsed.declarations(), &classes) else {
        return false;
    };
    let mut graph = Graph::new(rules);
    let mut importer = ModelImport {
        graph: &mut graph,
        classes: &classes,
        memo: HashMap::new(),
    };
    let mut assignment = BTreeMap::new();
    for entry in model.entries() {
        let value = match entry.value() {
            ModelValue::Assigned(value) => {
                let Some(value) = importer.assigned_value(value) else {
                    return false;
                };
                value
            }
            ModelValue::Unconstrained => importer.graph.add(Type::Never, Vec::new()),
        };
        if assignment
            .insert(entry.metavar().to_owned(), value)
            .is_some()
        {
            return false;
        }
    }
    let mut conditions = Vec::new();
    let Some((names, source)) = input_conditions(
        importer.graph,
        input,
        parsed.declarations(),
        importer.classes,
        &assignment,
        &mut conditions,
    ) else {
        return false;
    };
    let roots = assignment
        .values()
        .copied()
        .chain(conditions.iter().flat_map(|condition| match condition {
            Condition::Compare(lower, upper) => vec![*lower, *upper],
            _ => Vec::new(),
        }))
        .collect::<Vec<_>>();
    if assignment.keys().cloned().collect::<BTreeSet<_>>() != names || !importer.graph.valid(&roots)
    {
        return false;
    }
    conditions_hold(importer.graph, &conditions, &source)
}
