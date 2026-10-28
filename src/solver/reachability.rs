//! Reachability queries for directed graphs with dense node indices.
//!
//! Callers decide which edges belong to each graph. Each edge is a child index.

use std::collections::BTreeSet;

/// Return the nodes that can reach a directed cycle.
///
/// Each child index must be less than `edges.len()`. A node is removed only
/// after all its children have been removed. The nodes left include each cycle
/// and every node that can reach a cycle. Repeated edges count separately in
/// both child counts and parent lists.
pub fn can_reach_cycle(edges: &[Vec<usize>]) -> BTreeSet<usize> {
    let mut remaining = edges.iter().map(Vec::len).collect::<Vec<_>>();
    let mut parents = vec![Vec::new(); edges.len()];
    for (id, children) in edges.iter().enumerate() {
        for child in children {
            parents[*child].push(id);
        }
    }
    let mut pending = remaining
        .iter()
        .enumerate()
        .filter_map(|(id, count)| (*count == 0).then_some(id))
        .collect::<Vec<_>>();
    let mut removed = BTreeSet::new();
    while let Some(id) = pending.pop() {
        removed.insert(id);
        for parent in &parents[id] {
            remaining[*parent] -= 1;
            if remaining[*parent] == 0 {
                pending.push(*parent);
            }
        }
    }
    (0..edges.len())
        .filter(|id| !removed.contains(id))
        .collect()
}

/// Return one label per node. Two nodes have the same label exactly when each
/// can reach the other. An isolated node uses its own index.
///
/// Each child index must be less than `edges.len()`. Every group label is the
/// smallest node index in that group.
pub fn groups(edges: &[Vec<usize>]) -> Vec<usize> {
    let mut reverse = vec![Vec::new(); edges.len()];
    for (id, children) in edges.iter().enumerate() {
        for child in children {
            reverse[*child].push(id);
        }
    }
    let mut seen = vec![false; edges.len()];
    let mut order = Vec::new();
    for start in 0..edges.len() {
        let mut pending = vec![(start, false)];
        while let Some((id, finished)) = pending.pop() {
            if finished {
                order.push(id);
            } else if !seen[id] {
                seen[id] = true;
                pending.push((id, true));
                pending.extend(edges[id].iter().map(|child| (*child, false)));
            }
        }
    }
    let mut groups = (0..edges.len()).collect::<Vec<_>>();
    seen.fill(false);
    for start in order.into_iter().rev() {
        if seen[start] {
            continue;
        }
        let mut pending = vec![start];
        let mut members = Vec::new();
        let mut minimum = start;
        while let Some(id) = pending.pop() {
            if !seen[id] {
                seen[id] = true;
                minimum = minimum.min(id);
                members.push(id);
                pending.extend(&reverse[id]);
            }
        }
        for id in members {
            groups[id] = minimum;
        }
    }
    groups
}
