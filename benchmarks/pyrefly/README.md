# Pyrefly-derived benchmarks

Each `.input` file distills the subtype constraints of one
[Pyrefly unit test](https://github.com/facebook/pyrefly/tree/96c352b915890e23d151909f9aaa88f66fd3885e/pyrefly/lib/test)
(revision `96c352b91`). The first line gives the verdict of this solver.
The header gives the source test, the Pyrefly result, and each approximation.
See the [third-party notices](../../THIRD_PARTY_NOTICES.md#pyrefly) for the
upstream license.

Scope: only nontrivial generic solving. A test qualifies when a choice
(union arm, overload branch, or constrained TypeVar value) changes the
solution, when a generic or overloaded function value is instantiated against
other generics or metavariables, or when the constraints on a type variable
interact through variance or in opposite directions.

## Encoding rules

- A call of a generic function gives each type parameter a fresh
  metavariable, as Pyrefly does. Each argument check is one assertion.
  Each upper bound is one assertion.
- A constrained type variable must equal one of its constraints. That
  choice is an `or` of equalities.
- An expected type (annotation, declared return, `assert_type`) is an upper
  bound on the call result.
- A container display takes its own type, so `[1]` is `list[int]`. Display
  typing against a hint is out of scope.
- A type variable of the enclosing function is a fixed unknown type inside
  that function. A fresh class below its bound models it.
- A constructor with a `self` annotation gives the type of the new object
  from that annotation.
- Class variance follows Pyrefly. Pyrefly skips `__init__` and `__new__`
  during variance inference and treats a parameter with no evidence as
  invariant.
- A generic function value (an argument, not the callee) keeps its `forall`.
  The solver selects its parameters.
- An overloaded call or overloaded argument is an `or` over its signatures.
  Python uses the first matching signature, and this language has no
  negative constraints. Thus an overload is used only where at most one
  signature fits the arguments. Each header states this check.
- Pyrefly union expansion at an overloaded call is written out: one
  assertion for each expanded argument list.
- When Pyrefly reveals an overloaded or re-generalized call result, each
  later call of that result gets its own metavariables.

## Files

| File | Source test | Verdict |
| --- | --- | --- |
| 01 | generic_restrictions.rs `test_arg_against_typevar_bound` | unsat |
| 02 | generic_restrictions.rs `test_constraint_subtyping` (Pyrefly bug) | unsat |
| 03 | constructors.rs `test_hint_and_bound_interaction` | sat |
| 04 | generic_restrictions.rs `test_bound_violation_in_union_member` | unsat |
| 05 | generic_basic.rs `test_nested_typevar` | sat |
| 06 | contextual.rs `test_concat_custom_vecs` | sat |
| 07 | higher_order.rs `test_overloaded_argument_branch_respects_upper_bound` | unsat |
| 08 | higher_order.rs `test_two_overloaded_callables_cross_product` | sat |
| 09 | higher_order.rs `test_overload_pruning_ignored_when_solved_before_materialization` (Pyrefly solve order) | sat |
| 10 | higher_order.rs `test_overload_pruning_commits_nested_generic_constraints` | sat |
| 11 | higher_order.rs `test_nested_higher_order_overload` | sat |
| 12 | constructors.rs `test_init_to_callable_generics` | sat |
| 13 | constructors.rs `test_overloaded_constructor_with_hint` | sat |
