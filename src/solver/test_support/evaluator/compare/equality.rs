//! Complete comparisons of equal factors for the independent evaluator.
//!
//! The type graphs are checked. Every type loop passes through a constructor.
//! These comparison rules do not choose parameter values or follow superclasses.
//! The Boolean rules can use equal factors to prove inclusion. A comparison
//! loop is valid if all its required comparisons outside the loop also pass.
//! Results are saved only after the complete graph has been checked. No saved
//! result depends on an unfinished parent check.

use std::collections::{BTreeMap, VecDeque};

use super::{Check, Child, Comparer, Goal, Rule};

enum Equation {
    Done(bool),
    All(Vec<usize>),
    Any(Vec<usize>),
}

impl Equation {
    fn children(&self) -> &[usize] {
        match self {
            Self::Done(_) => &[],
            Self::All(children) | Self::Any(children) => children,
        }
    }
}

/// Equal factors can prove a comparison without selecting parameter values.
/// Each check retains the parameter owners and matched parameter positions.
pub fn holds(comparer: &mut Comparer<'_>, context: &Goal) -> bool {
    // A selected parameter can refer to its own value without a constructor.
    // Such comparisons require the cycle check on the current parent path.
    if !context.selections.is_empty() {
        return false;
    }
    let mut root = context.clone();
    match &mut root.check {
        Check::Values(equal, ..)
        | Check::ArmToValue(equal, ..)
        | Check::Arms(equal, ..)
        | Check::ArmToFactor(equal, ..)
        | Check::Factors(equal, ..) => *equal = true,
        Check::GenericBodies(..) => {}
        Check::SelectedBody { .. } => return false,
    }
    comparer.saved_bindings(&mut root);
    if let Some(accepted) = comparer.equal.get(&root) {
        return *accepted;
    }
    let (goals, equations) = comparisons(comparer, root);
    let accepted = remove_failures(&equations);
    let result = accepted[0];
    comparer.equal.extend(goals.into_iter().zip(accepted));
    result
}

fn comparisons(comparer: &mut Comparer<'_>, root: Goal) -> (Vec<Goal>, Vec<Equation>) {
    let mut indices = BTreeMap::from([(root.clone(), 0)]);
    let mut goals = vec![root];
    let mut equations = Vec::new();
    while equations.len() < goals.len() {
        let goal = &goals[equations.len()];
        let rule = if let Some(accepted) = comparer.equal.get(goal) {
            Rule::Done(*accepted)
        } else {
            comparer.rule(goal)
        };
        let mut identify = |mut child: Child| {
            comparer.saved_bindings(&mut child.goal);
            let next = goals.len();
            *indices.entry(child.goal.clone()).or_insert_with(|| {
                goals.push(child.goal);
                next
            })
        };
        let equation = match rule {
            Rule::Done(accepted) => Equation::Done(accepted),
            Rule::All(children) => Equation::All(children.into_iter().map(&mut identify).collect()),
            Rule::Any(children) => Equation::Any(children.into_iter().map(&mut identify).collect()),
        };
        equations.push(equation);
    }
    (goals, equations)
}

// Start with all comparisons allowed. A failed child rejects an All comparison.
// An Any comparison fails only when every child has failed. The comparisons
// left at the end provide complete proofs, including constructor loops.
fn remove_failures(equations: &[Equation]) -> Vec<bool> {
    let mut parents = vec![Vec::new(); equations.len()];
    let mut remaining = Vec::with_capacity(equations.len());
    let mut accepted = vec![true; equations.len()];
    let mut failed = VecDeque::new();
    for (id, equation) in equations.iter().enumerate() {
        let children = equation.children();
        remaining.push(children.len());
        for child in children {
            parents[*child].push(id);
        }
        if matches!(equation, Equation::Done(false))
            || matches!(equation, Equation::Any(children) if children.is_empty())
        {
            accepted[id] = false;
            failed.push_back(id);
        }
    }
    while let Some(child) = failed.pop_front() {
        for parent in &parents[child] {
            if !accepted[*parent] {
                continue;
            }
            let reject = match &equations[*parent] {
                Equation::All(_) => true,
                Equation::Any(_) => {
                    remaining[*parent] -= 1;
                    remaining[*parent] == 0
                }
                Equation::Done(_) => false,
            };
            if reject {
                accepted[*parent] = false;
                failed.push_back(*parent);
            }
        }
    }
    accepted
}
