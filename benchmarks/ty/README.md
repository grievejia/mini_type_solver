# ty-derived benchmarks

Each `.input` file distills the subtype constraints of one section of ty's
[mdtest suite](https://github.com/astral-sh/ruff/tree/1ae6552a9432d759218db172c22a007eddfcb40b/crates/ty_python_semantic/resources/mdtest)
(Ruff revision `1ae6552a94`). The first line gives the verdict of this solver.
The header gives the source section, the ty result, and each approximation.
Where a ty `TODO` says that ty is wrong today, the header gives both the
current and the intended result. The constraints follow the intended result.
See the [third-party notices](../../THIRD_PARTY_NOTICES.md#ruffty) for the
upstream license.

Scope: only nontrivial generic solving. A section qualifies when a choice
(union arm, intersection factor, overload branch, or constrained TypeVar
value) changes the solution, when a generic or overloaded function value is
instantiated against other generics or metavariables, or when the constraints
on a type variable interact through variance or in opposite directions.

## Encoding rules

The rules of the Pyrefly set apply ([Pyrefly benchmark set](../pyrefly/README.md)).
These points are specific to ty:

- ty infers literal types. A literal stays a literal (a subclass of its
  class) when the result depends on it. Otherwise it is widened, and the
  header says so.
- Variance follows ty: declared variance, or ty's inference from the members
  of a PEP 695 class.
- ty accepts an overloaded argument when some signature matches. That is an
  `or` over the signatures.
- A constraint set from a `ty_extensions` test is written directly: each type
  variable is a metavariable, and each bound is one assertion.

## Files

| File | Source section | Verdict |
| --- | --- | --- |
| 01 | type_properties/implies_subtype_of.md:1174 Transitivity should not introduce impossible constraints | unsat |
| 02 | generics/legacy/functions.md:2888 Inferring typevars in intersections | unsat |
| 03 | generics/pep695/functions.md:1636 Typevar inference is a unification problem (ty TODO) | unsat |
| 04 | overloads.md:453 Disjunctive generic receivers | sat |
| 05 | bidirectional.md:1961 Overload evaluation, `f9` (ty TODO) | sat |
| 06 | bidirectional.md:1133 Generic call argument inference, `two_lists` | sat |
| 07 | typed_dict.md:4498 Constructor inference from nested values (ty TODO) | sat |
| 08 | generics/pep695/functions.md:1406 Conflicting overloads against a constrained typevar | unsat |
| 09 | call/function.md:184 Generic overloaded callable constraints in constructors (ty TODO) | sat |
| 10 | generics/pep695/functions.md:1888 Passing generic functions to generic functions (ty TODO) | sat |
| 11 | generics/pep695/callables.md:1291 Multiple occurrences of a higher-order generic callable (ty TODO) | sat |
| 12 | dataclasses/dataclass_transform.md:2286 Converters, `duplicate` (ty TODO) | unsat |
