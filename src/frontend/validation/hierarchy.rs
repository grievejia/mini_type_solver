//! Hierarchy ordering, ancestor arguments, and variance checks.
//!
//! Checks preserve phase priority and source order before metadata is stored.

use std::collections::{BTreeMap, VecDeque};
use std::iter;

use super::super::diagnostic::{Diagnostic, DiagnosticKind, Span, diagnostic};
use super::classes::{Polarity, render, substitute};
use super::declarations::Variance;
use super::{
    BUILTIN_COUNT, ClassId, ClassType, Declarations, ResolvedClass, ResolvedFile, TemplateType,
    ValidatedFile,
};

/// Checked proper ancestor templates in C3 order for every user class.
#[derive(Debug, Clone)]
pub struct Hierarchy {
    classes: BTreeMap<ClassId, Vec<ClassType<TemplateType>>>,
}

impl Hierarchy {
    /// Built-ins have no proper ancestor templates. User identifiers belong to
    /// the declarations checked by hierarchy validation.
    #[must_use]
    pub fn ancestors(&self, id: ClassId) -> &[ClassType<TemplateType>] {
        if id.index() < BUILTIN_COUNT {
            &[]
        } else {
            &self.classes[&id]
        }
    }

    /// Read the class followed by its proper ancestors in C3 order.
    /// Built-in classes yield only their own identifier.
    pub fn linearization(&self, id: ClassId) -> impl Iterator<Item = ClassId> {
        iter::once(id).chain(self.ancestors(id).iter().map(|template| template.class))
    }
}

/// Check the hierarchy and publish proper ancestor templates in C3 order.
///
/// Direct self edges, hierarchy cycles, and C3 failures precede normalized
/// ancestor conflicts and variance errors. Each phase picks
/// its stated source order. Assertions move through untouched.
///
/// # Errors
///
/// Returns the first hierarchy [`Diagnostic`]: a self-edge at its
/// mention, a cycle at the declaration closing it, an inconsistent order at
/// its declaration, an ancestor-argument conflict at its direct superclass, or
/// a variance error at the first offending parameter use.
pub fn order(resolved: ResolvedFile) -> Result<ValidatedFile, Diagnostic> {
    let ResolvedFile {
        declarations,
        types,
        atoms,
        classes,
        assertions,
    } = resolved;
    check_self_edges(&classes, &declarations)?;
    check_cycles(&classes, &declarations)?;
    let dependency_order = dependency_order(&classes, declarations.class_count());
    let linearizations = linearize_all(&classes, &dependency_order, &declarations)?;
    let mut hierarchies =
        compose_ancestors(&classes, &dependency_order, linearizations, &declarations)?;
    check_variance(&classes, &declarations)?;
    // Composition needs an object record for base substitution. Published
    // hierarchy metadata contains user declarations only.
    hierarchies.remove(&ClassId::OBJECT);
    for class in &classes {
        assert!(
            hierarchies.contains_key(&class.id),
            "validated hierarchy has no completed class record: {:?}",
            class.id
        );
    }
    let hierarchy = Hierarchy {
        classes: hierarchies,
    };
    Ok(ValidatedFile {
        declarations,
        types,
        atoms,
        hierarchy,
        assertions,
    })
}

/// Reject classes listing themselves as superclasses, in source order.
fn check_self_edges(
    classes: &[ResolvedClass],
    declarations: &Declarations,
) -> Result<(), Diagnostic> {
    for record in classes {
        for superclass in &record.superclasses {
            if superclass.template.class == record.id {
                return Err(diagnostic(
                    superclass.name_span,
                    DiagnosticKind::SelfEdge {
                        name: declarations.class_name(record.id).to_owned(),
                    },
                ));
            }
        }
    }
    Ok(())
}

/// Reject cyclic hierarchies with depth-first search.
///
/// Roots and neighbors go in source order; the search is iterative so
/// deep hierarchies cannot overflow the stack. The blamed declaration
/// is the one whose edge closes the cycle, and the message names the
/// full path back to its start.
fn check_cycles(classes: &[ResolvedClass], declarations: &Declarations) -> Result<(), Diagnostic> {
    struct Frame {
        node: ClassId,
        next: usize,
    }
    let count = declarations.class_count();
    let mut adjacent: Vec<Vec<ClassId>> = vec![Vec::new(); count];
    // Built-in rows stay dummy: only user classes own edges, so a closing
    // edge always sources from a recorded declaration.
    let mut decl_spans = vec![Span::new(0, 0); count];
    for record in classes {
        adjacent[record.id.index()] = record
            .superclasses
            .iter()
            .map(|superclass| superclass.template.class)
            .collect();
        decl_spans[record.id.index()] = record.span;
    }
    let mut done = vec![false; count];
    let mut on_stack = vec![false; count];
    for record in classes {
        if done[record.id.index()] {
            continue;
        }
        on_stack[record.id.index()] = true;
        let mut stack = vec![Frame {
            node: record.id,
            next: 0,
        }];
        while let Some(frame) = stack.last_mut() {
            let node = frame.node;
            let neighbors = &adjacent[node.index()];
            if frame.next < neighbors.len() {
                let neighbor = neighbors[frame.next];
                frame.next += 1;
                if on_stack[neighbor.index()] {
                    let mut path: Vec<String> = stack
                        .iter()
                        .skip_while(|frame| frame.node != neighbor)
                        .map(|frame| declarations.class_name(frame.node).to_owned())
                        .collect();
                    path.push(declarations.class_name(neighbor).to_owned());
                    return Err(diagnostic(
                        decl_spans[node.index()],
                        DiagnosticKind::Cycle { path },
                    ));
                }
                if !done[neighbor.index()] {
                    on_stack[neighbor.index()] = true;
                    stack.push(Frame {
                        node: neighbor,
                        next: 0,
                    });
                }
            } else if let Some(finished) = stack.pop() {
                on_stack[finished.node.index()] = false;
                done[finished.node.index()] = true;
            }
        }
    }
    Ok(())
}

/// Order user classes after their declared bases, preserving queue order.
///
/// Direct hierarchy cycles have already been rejected. Ready classes enter the
/// queue in declaration order. Each base releases its dependents in that order.
fn dependency_order(classes: &[ResolvedClass], count: usize) -> Vec<usize> {
    let mut dependents = vec![Vec::new(); count];
    let mut pending = vec![0usize; classes.len()];
    for (sequence, class) in classes.iter().enumerate() {
        for base in &class.superclasses {
            if base.template.class != ClassId::OBJECT {
                dependents[base.template.class.index()].push(sequence);
                pending[sequence] += 1;
            }
        }
    }
    let mut queue = VecDeque::new();
    for (sequence, remaining) in pending.iter().enumerate() {
        if *remaining == 0 {
            queue.push_back(sequence);
        }
    }
    let mut order = Vec::with_capacity(classes.len());
    while let Some(sequence) = queue.pop_front() {
        order.push(sequence);
        for dependent in &dependents[classes[sequence].id.index()] {
            pending[*dependent] -= 1;
            if pending[*dependent] == 0 {
                queue.push_back(*dependent);
            }
        }
    }
    order
}

/// Compute C3 orders and report the first independent failure in declaration order.
///
/// Only successful orders enter the table. A missing base order taints its
/// dependent, which produces no additional diagnostic. The dependency order
/// places every user base before its dependents.
fn linearize_all(
    classes: &[ResolvedClass],
    dependency_order: &[usize],
    declarations: &Declarations,
) -> Result<BTreeMap<ClassId, Vec<ClassId>>, Diagnostic> {
    let mut linearizations = BTreeMap::from([(ClassId::OBJECT, vec![ClassId::OBJECT])]);
    let mut failures = Vec::new();
    'classes: for sequence in dependency_order {
        let record = &classes[*sequence];
        let mut bases = record
            .superclasses
            .iter()
            .map(|base| base.template.class)
            .collect::<Vec<_>>();
        if !bases.contains(&ClassId::OBJECT) {
            bases.push(ClassId::OBJECT);
        }
        let mut inputs = Vec::with_capacity(bases.len() + 1);
        for base in &bases {
            let Some(order) = linearizations.get(base) else {
                continue 'classes;
            };
            inputs.push(order.clone());
        }
        inputs.push(bases);
        if let Some(order) = merge_c3(inputs) {
            let mut full = vec![record.id];
            full.extend(order);
            linearizations.insert(record.id, full);
        } else {
            failures.push(*sequence);
        }
    }
    if let Some(first) = failures.into_iter().min() {
        let record = &classes[first];
        return Err(diagnostic(
            record.span,
            DiagnosticKind::InconsistentOrder {
                name: declarations.class_name(record.id).to_owned(),
            },
        ));
    }
    Ok(linearizations)
}

/// C3 merge: repeatedly take the first head appearing in no list tail.
///
/// Returns `None` when no head qualifies on some pass.
fn merge_c3(mut lists: Vec<Vec<ClassId>>) -> Option<Vec<ClassId>> {
    let mut merged = Vec::new();
    loop {
        lists.retain(|list| !list.is_empty());
        if lists.is_empty() {
            return Some(merged);
        }
        let mut progress = false;
        for candidate in 0..lists.len() {
            let head = lists[candidate][0];
            let blocked = lists.iter().enumerate().any(|(other, list)| {
                other != candidate && list.iter().skip(1).any(|id| *id == head)
            });
            if !blocked {
                for list in &mut lists {
                    if list.first() == Some(&head) {
                        list.remove(0);
                    }
                }
                merged.push(head);
                progress = true;
                break;
            }
        }
        if !progress {
            return None;
        }
    }
}

/// Compose paths and report the first independent conflict in declaration order.
///
/// Each class visits direct roots in source order, then each root's C3 ancestors.
/// Only completed records enter the table. A missing base record taints its
/// dependent, without adding a second diagnostic. Ancestor templates and C3
/// entries stay aligned when a completed record becomes a base.
fn compose_ancestors(
    classes: &[ResolvedClass],
    dependency_order: &[usize],
    mut linearizations: BTreeMap<ClassId, Vec<ClassId>>,
    declarations: &Declarations,
) -> Result<BTreeMap<ClassId, Vec<ClassType<TemplateType>>>, Diagnostic> {
    let mut hierarchies = BTreeMap::from([(ClassId::OBJECT, Vec::new())]);
    let mut failures = Vec::new();
    'classes: for sequence in dependency_order {
        let record = &classes[*sequence];
        let mut bases = record
            .superclasses
            .iter()
            .map(|base| (base.template.clone(), base.span))
            .collect::<Vec<_>>();
        if !bases.iter().any(|(base, _)| base.class == ClassId::OBJECT) {
            bases.push((ClassType::plain(ClassId::OBJECT), record.span));
        }
        // A failed base taints the whole class, even if an earlier valid base
        // would produce another conflict. Check all bases before composition.
        let Some(bases) = bases
            .iter()
            .map(|(base, span)| {
                hierarchies
                    .get(&base.class)
                    .map(|ancestors| (base, *span, ancestors))
            })
            .collect::<Option<Vec<_>>>()
        else {
            continue;
        };
        let mut table = BTreeMap::new();
        for (base, span, ancestors) in bases {
            if let Err(diagnostic) = compose_base(base, span, ancestors, &mut table, declarations) {
                failures.push((*sequence, diagnostic));
                continue 'classes;
            }
        }
        let Some(linearization) = linearizations.remove(&record.id) else {
            panic!("ancestor composition has no C3 order for its class");
        };
        // Composition visits exactly the bases and their proper ancestors.
        // C3 contains the same classes, with the current class first.
        let ancestors = linearization
            .into_iter()
            .skip(1)
            .map(|ancestor| {
                let Some(template) = table.remove(&ancestor) else {
                    panic!("composed ancestor table does not match C3 order");
                };
                template
            })
            .collect();
        hierarchies.insert(record.id, ancestors);
    }
    match failures.into_iter().min_by_key(|(sequence, _)| *sequence) {
        Some((_, diagnostic)) => Err(diagnostic),
        None => Ok(hierarchies),
    }
}

/// Report a conflicting path at the direct superclass's span.
fn compose_base(
    base: &ClassType<TemplateType>,
    span: Span,
    ancestors: &[ClassType<TemplateType>],
    table: &mut BTreeMap<ClassId, ClassType<TemplateType>>,
    declarations: &Declarations,
) -> Result<(), Diagnostic> {
    let inherited =
        iter::once((base.class, base.arguments.clone())).chain(ancestors.iter().map(|template| {
            (
                template.class,
                template
                    .arguments
                    .iter()
                    .map(|argument| substitute(argument, base.class, &base.arguments))
                    .collect(),
            )
        }));
    for (ancestor, arguments) in inherited {
        match table.get(&ancestor) {
            Some(previous) if previous.arguments != arguments => {
                return Err(diagnostic(
                    span,
                    DiagnosticKind::ConflictingAncestorArguments {
                        name: declarations.class_name(ancestor).to_owned(),
                        first: previous
                            .arguments
                            .iter()
                            .map(|argument| render(argument, declarations))
                            .collect(),
                        second: arguments
                            .iter()
                            .map(|argument| render(argument, declarations))
                            .collect(),
                    },
                ));
            }
            Some(_) => {}
            None => {
                table.insert(
                    ancestor,
                    ClassType {
                        class: ancestor,
                        arguments,
                    },
                );
            }
        }
    }
    Ok(())
}

/// Variance checks use surviving direct occurrences. Hierarchy failures have
/// priority; declarations and source spans determine the diagnostic order.
fn check_variance(
    classes: &[ResolvedClass],
    declarations: &Declarations,
) -> Result<(), Diagnostic> {
    for class in classes {
        let mut failures = Vec::new();
        for use_ in class
            .superclasses
            .iter()
            .flat_map(|base| &base.parameter_uses)
        {
            let Some(parameter) = declarations
                .class_parameters(class.id)
                .nth(use_.position as usize)
            else {
                panic!(
                    "template parameter position exceeds its declaration: {}",
                    use_.position
                );
            };
            if !matches!(
                (parameter.variance(), use_.polarity),
                (Variance::Invariant, _)
                    | (Variance::Covariant, Polarity::Positive)
                    | (Variance::Contravariant, Polarity::Negative)
            ) {
                failures.push(diagnostic(
                    use_.span,
                    DiagnosticKind::ClassParameterVariance {
                        name: parameter.name().to_owned(),
                    },
                ));
            }
        }
        if let Some(diagnostic) = failures
            .into_iter()
            .min_by_key(|diagnostic| diagnostic.span().start())
        {
            return Err(diagnostic);
        }
    }
    Ok(())
}
