//! Name binders and recursive definitions only during a rendering call.
//!
//! Each open root starts with its complete saved outer scope. Child tasks keep
//! the active printing context. Public value handles keep no printing state.

use std::rc::Rc;

use crate::frontend::problem::Callable;

use super::super::theory::closed::{Value, ValueNode};
use super::{AssignedValue, DisplayNames};

#[derive(Clone)]
struct Binder {
    owner: Value,
    names: Vec<String>,
}

#[derive(Clone)]
struct Recursion {
    value: Value,
    name: String,
}

#[derive(Clone, Default)]
struct Context {
    binders: Vec<Binder>,
    recursive: Vec<Recursion>,
}

#[derive(Clone)]
struct RenderValue {
    value: Value,
    names: Rc<DisplayNames>,
    context: Rc<Context>,
    unfold: bool,
}

enum Print {
    Text(String),
    Value(RenderValue, bool),
}

pub fn value(root: &AssignedValue) -> String {
    let mut context = Context::default();
    for owner in root.value.binding_scope() {
        let ValueNode::Generic { parameters, .. } = owner.node() else {
            panic!("a checked saved scope must contain only generic owners");
        };
        let names = binder_names(&root.value, &root.names, &context, "T", parameters as usize);
        context.binders.push(Binder { owner, names });
    }
    let root = RenderValue {
        value: root.value.clone(),
        names: Rc::clone(&root.names),
        context: Rc::new(context),
        unfold: false,
    };
    let mut output = String::new();
    let mut tasks = vec![Print::Value(root, false)];
    while let Some(task) = tasks.pop() {
        match task {
            Print::Text(text) => output.push_str(&text),
            Print::Value(value, parentheses) => value.print(&mut tasks, parentheses),
        }
    }
    output
}

fn binder_names(
    value: &Value,
    names: &DisplayNames,
    context: &Context,
    prefix: &str,
    count: usize,
) -> Vec<String> {
    let mut result = Vec::new();
    let mut index = 0;
    while result.len() < count {
        let name = format!("{prefix}{index}");
        index += 1;
        if value.has_class_name(&name)
            || names.reserved.contains(&name)
            || context
                .binders
                .iter()
                .any(|binder| binder.names.contains(&name))
            || context.recursive.iter().any(|record| record.name == name)
        {
            continue;
        }
        result.push(name);
    }
    result
}

impl RenderValue {
    fn child(&self, value: Value) -> Self {
        Self {
            value,
            names: Rc::clone(&self.names),
            context: Rc::clone(&self.context),
            unfold: false,
        }
    }

    // A named definition stops the path check. A child with a separate loop
    // receives another name even when it also refers to an outer definition.
    fn print_recursion(&self, tasks: &mut Vec<Print>, parentheses: bool) -> bool {
        if self.unfold || !self.value.contains_recursion() {
            return false;
        }
        if let Some(record) = self
            .context
            .recursive
            .iter()
            .find(|record| record.value == self.value)
        {
            tasks.push(Print::Text(record.name.clone()));
            return true;
        }
        if !self
            .value
            .is_recursive_without(self.context.recursive.iter().map(|record| &record.value))
        {
            return false;
        }
        let name = binder_names(&self.value, &self.names, &self.context, "R", 1).remove(0);
        let mut context = self.context.as_ref().clone();
        context.recursive.push(Recursion {
            value: self.value.clone(),
            name: name.clone(),
        });
        if parentheses {
            tasks.push(Print::Text(String::from(")")));
        }
        let compound = matches!(
            self.value.node(),
            ValueNode::Union(_) | ValueNode::Intersection(_)
        );
        if compound {
            tasks.push(Print::Text(String::from(")")));
        }
        tasks.push(Print::Value(
            Self {
                value: self.value.clone(),
                names: Rc::clone(&self.names),
                context: Rc::new(context),
                unfold: true,
            },
            false,
        ));
        if compound {
            tasks.push(Print::Text(String::from("(")));
        }
        tasks.push(Print::Text(format!("mu {name}. ")));
        if parentheses {
            tasks.push(Print::Text(String::from("(")));
        }
        true
    }

    fn print(&self, tasks: &mut Vec<Print>, parentheses: bool) {
        if self.print_recursion(tasks, parentheses) {
            return;
        }
        match self.value.node() {
            ValueNode::Arbitrary => {
                panic!("an arbitrary parameter cannot escape into a public value")
            }
            ValueNode::Never => tasks.push(Print::Text(String::from("never"))),
            ValueNode::Bound {
                owner, position, ..
            } => {
                let Some(binder) = self
                    .context
                    .binders
                    .iter()
                    .rev()
                    .find(|binder| binder.owner.same_binding(&owner))
                else {
                    panic!("a checked model parameter must have a printed binder");
                };
                tasks.push(Print::Text(binder.names[position as usize].clone()));
            }
            ValueNode::Class {
                name, arguments, ..
            } => {
                if arguments.is_empty() {
                    tasks.push(Print::Text(name));
                } else {
                    let arguments = arguments
                        .into_iter()
                        .map(|child| self.child(child))
                        .collect();
                    print_list(tasks, &format!("{name}["), "]", arguments);
                }
            }
            ValueNode::Tuple(children) => {
                let children = children
                    .into_iter()
                    .map(|child| self.child(child))
                    .collect();
                print_list(tasks, "tuple[", "]", children);
            }
            ValueNode::Callable(body) => {
                print_callable(
                    tasks,
                    body.map(|child| self.child(child.clone())),
                    None,
                    parentheses,
                );
            }
            ValueNode::Generic { parameters, body } => {
                let names = binder_names(
                    &self.value,
                    &self.names,
                    &self.context,
                    "T",
                    parameters as usize,
                );
                let mut context = self.context.as_ref().clone();
                context.binders.push(Binder {
                    owner: self.value.clone(),
                    names: names.clone(),
                });
                let context = Rc::new(context);
                let body = body.map(|child| Self {
                    value: child.clone(),
                    names: Rc::clone(&self.names),
                    context: Rc::clone(&context),
                    unfold: false,
                });
                print_callable(tasks, body, Some(names), parentheses);
            }
            ValueNode::Union(children) => self.print_junction(tasks, children, " | ", parentheses),
            ValueNode::Intersection(children) => {
                self.print_junction(tasks, children, " & ", parentheses);
            }
        }
    }

    fn print_junction(
        &self,
        tasks: &mut Vec<Print>,
        children: Vec<Value>,
        separator: &str,
        parentheses: bool,
    ) {
        let compound = children.len() > 1;
        for (index, child) in children.into_iter().enumerate().rev() {
            tasks.push(Print::Value(self.child(child), compound || parentheses));
            if index != 0 {
                tasks.push(Print::Text(separator.to_owned()));
            }
        }
    }
}

fn print_list(tasks: &mut Vec<Print>, open: &str, close: &str, children: Vec<RenderValue>) {
    tasks.push(Print::Text(close.to_owned()));
    for (index, child) in children.into_iter().enumerate().rev() {
        tasks.push(Print::Value(child, false));
        if index != 0 {
            tasks.push(Print::Text(String::from(", ")));
        }
    }
    tasks.push(Print::Text(open.to_owned()));
}

fn print_callable(
    tasks: &mut Vec<Print>,
    body: Callable<RenderValue>,
    names: Option<Vec<String>>,
    parentheses: bool,
) {
    if parentheses {
        tasks.push(Print::Text(String::from(")")));
    }
    tasks.push(Print::Value(body.ret, false));
    print_list(tasks, "(", ") -> ", body.params);
    if let Some(names) = names {
        tasks.push(Print::Text(format!("forall {}. ", names.join(", "))));
    }
    if parentheses {
        tasks.push(Print::Text(String::from("(")));
    }
}
