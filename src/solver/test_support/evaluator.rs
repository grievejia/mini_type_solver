//! Independent graph checks for finite and recursive model values.
//!
//! This module reads public values and direct source declarations. It does not
//! call production comparison, hierarchy, or normalization code.

mod compare;
mod import;
#[cfg(test)]
mod tests;

use std::collections::{BTreeMap, BTreeSet};

use crate::frontend::parse;
use crate::frontend::problem::{Callable, ClassVariance};

use super::ModelInput;

pub use import::model_holds;

const OBJECT_INDEX: usize = 0;
const NEVER_INDEX: usize = 1;

type Selections = BTreeMap<usize, Vec<usize>>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Never,
    Bound {
        owner: usize,
        position: usize,
    },
    Class {
        class: usize,
        arguments: Vec<usize>,
    },
    Tuple(Vec<usize>),
    Callable(Callable<usize>),
    Generic {
        parameters: usize,
        body: Callable<usize>,
    },
    Reference(usize),
    Union(Vec<usize>),
    Intersection(Vec<usize>),
}

impl Type {
    fn children(&self) -> Vec<usize> {
        match self {
            Self::Never | Self::Bound { .. } => Vec::new(),
            Self::Class { arguments, .. } => arguments.clone(),
            Self::Tuple(children) | Self::Union(children) | Self::Intersection(children) => {
                children.clone()
            }
            Self::Callable(body) | Self::Generic { body, .. } => body.children().copied().collect(),
            Self::Reference(target) => vec![*target],
        }
    }

    fn constructor(&self) -> bool {
        matches!(
            self,
            Self::Class { .. } | Self::Tuple(_) | Self::Callable(_) | Self::Generic { .. }
        )
    }
}

#[derive(Debug, Clone)]
struct Node {
    kind: Type,
    scope: Vec<usize>,
}

/// Template identifiers belong to one class rule's separate arena.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct TemplateId(usize);

#[derive(Debug, Clone)]
enum Template {
    Parameter(usize),
    Class {
        class: usize,
        arguments: Vec<TemplateId>,
    },
    Tuple(Vec<TemplateId>),
    Callable(Callable<TemplateId>),
    Union(Vec<TemplateId>),
    Intersection(Vec<TemplateId>),
}

impl Template {
    fn children(&self) -> Vec<TemplateId> {
        match self {
            Self::Parameter(_) => Vec::new(),
            Self::Class { arguments, .. } => arguments.clone(),
            Self::Tuple(children) | Self::Union(children) | Self::Intersection(children) => {
                children.clone()
            }
            Self::Callable(body) => body.children().copied().collect(),
        }
    }
}

/// Direct superclass roots refer only to this rule's checked template arena.
/// Template parameters use the owning class's declaration positions.
#[derive(Debug, Clone)]
struct ClassRule {
    variances: Vec<ClassVariance>,
    templates: Vec<Template>,
    direct: Vec<(usize, Vec<TemplateId>)>,
}

#[derive(Debug, Clone)]
pub struct Graph {
    nodes: Vec<Node>,
    classes: Vec<ClassRule>,
}

impl Graph {
    fn new(classes: Vec<ClassRule>) -> Self {
        Self {
            nodes: Vec::new(),
            classes,
        }
    }

    fn add(&mut self, kind: Type, scope: Vec<usize>) -> usize {
        let id = self.nodes.len();
        self.nodes.push(Node { kind, scope });
        id
    }

    /// Keep intersection factors intact so source import retains parameter uses.
    ///
    /// Open children use the complete destination scope. Closed children can
    /// be shared. Callers supply at least one child.
    fn intersection(&mut self, children: Vec<usize>, scope: Vec<usize>) -> usize {
        match children.as_slice() {
            [only] => *only,
            _ => self.intern(Type::Intersection(children), scope),
        }
    }

    /// Template substitution reuses equal constructor nodes. Otherwise a finite
    /// superclass repeat could produce a new identifier on every visit.
    fn intern(&mut self, kind: Type, scope: Vec<usize>) -> usize {
        if let Some(id) = self
            .nodes
            .iter()
            .position(|node| node.kind == kind && node.scope == scope)
        {
            id
        } else {
            self.add(kind, scope)
        }
    }

    /// Invalid descriptions never become queryable graphs.
    pub fn checked(
        declarations: &str,
        description: &[(Type, Vec<usize>)],
        roots: &[usize],
    ) -> Option<Self> {
        let parsed = parse(declarations).ok()?;
        let names = import::class_names(ModelInput::Source(declarations), parsed.declarations())?;
        let classes = import::class_rules(parsed.declarations(), &names)?;
        let mut graph = Self {
            classes,
            nodes: description
                .iter()
                .map(|(kind, scope)| Node {
                    kind: kind.clone(),
                    scope: scope.clone(),
                })
                .collect(),
        };
        if !graph.valid(roots) {
            return None;
        }
        graph.live_parameters(roots);
        graph.valid(roots).then_some(graph)
    }

    fn valid(&self, roots: &[usize]) -> bool {
        if roots.iter().any(|id| *id >= self.nodes.len())
            || self.nodes.iter().any(|node| {
                node.kind
                    .children()
                    .iter()
                    .any(|child| *child >= self.nodes.len())
            })
        {
            return false;
        }
        for node in &self.nodes {
            if let Type::Class { class, arguments } = &node.kind
                && self
                    .classes
                    .get(*class)
                    .is_none_or(|class| class.variances.len() != arguments.len())
            {
                return false;
            }
            if node.scope.iter().any(|id| {
                !matches!(
                    self.nodes.get(*id).map(|node| &node.kind),
                    Some(Type::Generic { .. })
                )
            }) {
                return false;
            }
            if node
                .scope
                .iter()
                .enumerate()
                .any(|(position, owner)| self.nodes[*owner].scope != node.scope[..position])
            {
                return false;
            }
            if let Type::Bound { owner, position } = node.kind
                && (!node.scope.contains(&owner)
                    || !matches!(self.nodes.get(owner).map(|node| &node.kind), Some(Type::Generic { parameters, .. }) if position < *parameters))
            {
                return false;
            }
        }
        let free = self.free_parameters();
        if roots.iter().any(|id| !free[*id].is_empty()) {
            return false;
        }
        for (id, node) in self.nodes.iter().enumerate() {
            let mut scope = node.scope.clone();
            if matches!(node.kind, Type::Generic { .. }) {
                scope.push(id);
            }
            for child in node.kind.children() {
                if matches!(node.kind, Type::Reference(_)) {
                    if !free[child].is_empty() && !scope.starts_with(&self.nodes[child].scope) {
                        return false;
                    }
                } else if !free[child].is_empty() && scope != self.nodes[child].scope {
                    return false;
                }
            }
        }
        self.contractive()
    }

    fn free_parameters(&self) -> Vec<BTreeSet<usize>> {
        let mut free = vec![BTreeSet::new(); self.nodes.len()];
        loop {
            let mut changed = false;
            for (id, node) in self.nodes.iter().enumerate() {
                let mut next = match node.kind {
                    Type::Bound { owner, .. } => BTreeSet::from([owner]),
                    _ => node
                        .kind
                        .children()
                        .iter()
                        .flat_map(|child| free[*child].iter().copied())
                        .collect(),
                };
                if matches!(node.kind, Type::Generic { .. }) {
                    next.remove(&id);
                }
                if next != free[id] {
                    free[id] = next;
                    changed = true;
                }
            }
            if !changed {
                return free;
            }
        }
    }

    fn contractive(&self) -> bool {
        let mut incoming = vec![0; self.nodes.len()];
        for node in &self.nodes {
            if !node.kind.constructor() {
                for child in node.kind.children() {
                    incoming[child] += 1;
                }
            }
        }
        let mut pending = incoming
            .iter()
            .enumerate()
            .filter_map(|(id, count)| (*count == 0).then_some(id))
            .collect::<Vec<_>>();
        let mut removed = 0;
        while let Some(id) = pending.pop() {
            removed += 1;
            if !self.nodes[id].kind.constructor() {
                for child in self.nodes[id].kind.children() {
                    incoming[child] -= 1;
                    if incoming[child] == 0 {
                        pending.push(child);
                    }
                }
            }
        }
        removed == self.nodes.len()
    }

    pub fn is_subtype(&mut self, lower: usize, upper: usize) -> bool {
        compare::is_subtype(self, lower, upper)
    }

    fn live_parameters(&mut self, roots: &[usize]) {
        let mut live = BTreeSet::new();
        let mut pending = roots.to_vec();
        while let Some(id) = pending.pop() {
            if live.insert(id) {
                pending.extend(self.nodes[id].kind.children());
            }
        }
        let mut positions: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
        for id in &live {
            if let Type::Bound { owner, position } = self.nodes[*id].kind {
                positions.entry(owner).or_default().insert(position);
            }
        }
        let mut removed = BTreeSet::new();
        let mut maps = BTreeMap::new();
        for (id, node) in self.nodes.iter_mut().enumerate() {
            if let Type::Generic { body, .. } = &node.kind {
                let positions = positions.remove(&id).unwrap_or_default();
                let count = positions.len();
                maps.insert(
                    id,
                    positions
                        .into_iter()
                        .enumerate()
                        .map(|(new, old)| (old, new))
                        .collect::<BTreeMap<_, _>>(),
                );
                node.kind = if count == 0 {
                    removed.insert(id);
                    Type::Callable(body.clone())
                } else {
                    Type::Generic {
                        parameters: count,
                        body: body.clone(),
                    }
                };
            }
        }
        for (id, node) in self.nodes.iter_mut().enumerate() {
            node.scope.retain(|owner| !removed.contains(owner));
            // An unreachable bound occurrence must not keep a removed position
            // or refer to a binder that has become an ordinary function.
            if !live.contains(&id) && matches!(node.kind, Type::Bound { .. }) {
                node.kind = Type::Never;
            }
            if let Type::Bound { owner, position } = &mut node.kind
                && let Some(new) = maps.get(owner).and_then(|map| map.get(position))
            {
                *position = *new;
            }
        }
    }
}

/// Read declarations directly and check the supplied closed roots.
pub fn direct_query(
    declarations: &str,
    description: &[(Type, Vec<usize>)],
    lower: usize,
    upper: usize,
) -> Option<bool> {
    let mut graph = Graph::checked(declarations, description, &[lower, upper])?;
    Some(graph.is_subtype(lower, upper))
}

fn shape(kind: &Type) -> Option<(u8, usize)> {
    match kind {
        Type::Class { class, .. } if *class != OBJECT_INDEX => Some((0, 0)),
        Type::Tuple(children) => Some((1, children.len())),
        Type::Callable(body) | Type::Generic { body, .. } => Some((2, body.params.len())),
        _ => None,
    }
}

fn arm(graph: &Graph, factors: BTreeSet<usize>) -> Option<Vec<usize>> {
    let mut fixed = None;
    let mut result = Vec::new();
    for factor in factors {
        match graph.nodes[factor].kind {
            Type::Never
            | Type::Class {
                class: NEVER_INDEX, ..
            } => return None,
            Type::Class {
                class: OBJECT_INDEX,
                ..
            } => continue,
            _ => {}
        }
        if let Some(next) = shape(&graph.nodes[factor].kind) {
            if fixed.is_some_and(|old| old != next) {
                return None;
            }
            fixed = Some(next);
        }
        result.push(factor);
    }
    Some(result)
}

/// Apply selections before lattice expansion. Constructors keep their children
/// whole for later comparisons with the same selections. Return `None` if the
/// expansion repeats a node before reaching a constructor.
fn arms(graph: &Graph, root: usize, selections: &Selections) -> Option<Vec<Vec<usize>>> {
    let mut forms: BTreeMap<usize, BTreeSet<Vec<usize>>> = BTreeMap::new();
    let mut active = BTreeSet::new();
    let mut pending = vec![(root, false)];
    while let Some((id, finished)) = pending.pop() {
        if forms.contains_key(&id) {
            continue;
        }
        let kind = &graph.nodes[id].kind;
        let selected = if let Type::Bound { owner, position } = kind
            && let Some(arguments) = selections.get(owner)
        {
            Some(arguments[*position])
        } else {
            None
        };
        if !finished
            && (selected.is_some()
                || matches!(
                    kind,
                    Type::Reference(_) | Type::Union(_) | Type::Intersection(_)
                ))
        {
            if !active.insert(id) {
                return None;
            }
            pending.push((id, true));
            let children = selected.map_or_else(|| kind.children(), |child| vec![child]);
            pending.extend(children.into_iter().rev().map(|child| (child, false)));
            continue;
        }
        active.remove(&id);
        let mut result = if let Some(child) = selected {
            forms[&child].clone()
        } else {
            match kind {
                Type::Never => BTreeSet::new(),
                Type::Reference(child) => forms[child].clone(),
                Type::Union(children) => children
                    .iter()
                    .flat_map(|child| forms[child].iter().cloned())
                    .collect(),
                Type::Intersection(children) => {
                    let mut result = BTreeSet::from([Vec::new()]);
                    for child in children {
                        result = result
                            .iter()
                            .flat_map(|left| {
                                forms[child].iter().filter_map(|right| {
                                    arm(graph, left.iter().chain(right).copied().collect())
                                })
                            })
                            .collect();
                    }
                    result
                }
                _ => arm(graph, BTreeSet::from([id])).into_iter().collect(),
            }
        };
        if result.contains(&Vec::new()) {
            result = BTreeSet::from([Vec::new()]);
        }
        forms.insert(id, result);
    }
    forms.remove(&root).map(|forms| forms.into_iter().collect())
}
