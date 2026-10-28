# mini_type_solver

`mini_type_solver` is an experimental solver for subtype constraints. You
express relationships between types, and it returns a checked assignment for
the unknown types or a set of conflicting assertions.

The type language includes classes, unions, intersections, tuples, and
callables, including generic callables. Three search engines share the same
type solver, so the project also serves as a testbed for Boolean search
strategies. The [design reference](docs/project_design.md) explains the type
rules and the solver's search contract.

## Quick start

With Rust and Cargo installed, create `example.input`:

```text
class Animal;
class Dog extends Animal;

metavar ?T;
metavar ?U;

assert Dog <: ?T;
assert ?T <: ?U;
assert ?U <: Animal;
```

`<:` means “is a subtype of.” Here, `?T` must include `Dog`, `?U` must include
whatever type is assigned to `?T`, and `?U` must stay below `Animal`.

Run from the repository root:

```sh
cargo run -- solve example.input
```

Output:

```text
satisfiable
model:
  ?T = Dog
  ?U = Dog
```

Both unknowns receive `Dog`, which satisfies the whole chain. A model is one
joint assignment: every occurrence of an unknown uses the same type. The solver
does not promise a least, greatest, or otherwise preferred assignment.

## Writing constraints

An input file contains declarations and assertions. `class` declares a named
type, `extends` gives its direct superclasses, and `metavar` declares an unknown
whose name starts with `?`. Names can be declared later in the file. Statements
end with `;`, and `#` starts a line comment.

Every `assert` must hold. Within an assertion, `and` requires both comparisons
and `or` allows either alternative. For example, with the quick-start classes:

```text
assert (Animal <: ?T) or (Dog <: ?T);
assert ?T <: Dog;
```

The first alternative fails because it would put `Animal` below `Dog` through
`?T`. The second works with `?T = Dog`. This is where Boolean search enters the
problem: the engine chooses comparisons, and the type solver checks whether
they can hold together. An unselected comparison adds no requirement; it does
not assert that the subtype relation is false.

Multiple assertions and one assertion joined with `and` impose the same
requirements:

```text
assert (Dog <: ?T) and (?T <: Animal);
```

## Types

### Unions, intersections, and built-in types

`object` is the top type and `never` is the bottom type. For every type `T`,
`never <: T` and `T <: object`.

`A | B` is a union: it includes both alternatives. `A & B` is an intersection:
it requires both factors. For example, an unknown that must include both `Dog`
and `Cat` can receive their union:

```text
class Dog;
class Cat;
metavar ?Pet;

assert Dog <: ?Pet;
assert Cat <: ?Pet;
```

The model assigns `?Pet = Dog | Cat`.

Unrelated class names can overlap. The input does not list every possible
subclass, so `Dog & Cat` can remain non-bottom even with no declared common
subclass. A missing subtype relation alone does not establish disjointness.

### Tuples

`tuple[Animal, Dog]` gives the type of each element; `tuple[]` is the empty
tuple. Subtyping requires matching lengths and compares elements in the normal
direction:

```text
tuple[Dog] <: tuple[Animal]
```

Constructors preserve their structure. For example,
`tuple[Dog] | tuple[Cat] <: tuple[Dog | Cat]` holds, but the reverse does not.
The solver does not distribute a tuple's arguments over unions or
intersections. The same principle applies to classes and callables; see the
[type rules](docs/project_design.md#constructors-preserve-structure-variance-controls-comparison).

### Callables

A callable lists positional parameter types before `->` and its return type
after it. The parameter list is always present, including for zero parameters:

```text
(Animal, Dog) -> Animal
() -> Animal
```

Parameter counts must match during subtype checks. Return types follow the
normal subtype direction, while parameter types use the reverse direction:

```text
(Animal) -> Dog <: (Dog) -> Animal
```

The left callable accepts every `Animal`, including every `Dog`. It returns a
`Dog`, which also fits `Animal`. This explains why a function with a broader
input type and a narrower result can replace the right callable.

Parameter and return types can themselves be tuples, unions, intersections,
classes, or callables. For example, `((Animal) -> Dog) -> (Dog) -> Animal` takes
a callable and returns another callable.

### Generic classes

Class parameters declare how argument subtyping affects the enclosing type:

```text
class Animal;
class Dog extends Animal;
class Box[+T];
class Consumer[-T];
class Inv[T];
class DogBox extends Box[Dog];

assert DogBox <: Box[Animal];
assert Consumer[Animal] <: Consumer[Dog];
```

`DogBox` inherits `Box[Dog]`; covariance then allows it to fit `Box[Animal]`.
`Consumer` uses the reverse direction, just like a callable parameter.

| Declaration | Variance | Requirement for `C[L] <: C[U]` |
| --- | --- | --- |
| `C[+T]` | Covariant | `L <: U` |
| `C[-T]` | Contravariant | `U <: L` |
| `C[T]` | Invariant | Both directions |

Every use of a generic class must supply all its arguments. A class without
parameters uses its name alone. Arguments can contain other type forms,
including metavariables and generic callables. Superclass arguments cannot
contain metavariables or generic callables.

Inheritance must be consistent, and the direct superclass graph must have no
cycle. Validation checks these requirements and declared variance before
solving assertions. Details of multiple inheritance and argument substitution
are in the
[design reference](docs/project_design.md#constructors-preserve-structure-variance-controls-comparison).

### Generic callables

A generic callable uses `forall` to introduce local type parameters. They
belong to that callable, while a metavariable is one unknown shared across
assertions. Parameters can be unrestricted, have an upper bound, or use a
finite exact set:

```text
forall X. (X) -> X                  # unrestricted
forall X <: Animal. (X) -> X        # X is below Animal
forall X in {Dog, Cat}. (X) -> X    # exact permitted types
```

A generic callable on the left of `<:` can satisfy a requirement by selecting
an instance:

```text
forall X. (X) -> X <: (Dog) -> Animal
```

Selecting `Dog` for `X` makes this comparison hold. All occurrences of `X` in
that body use the same selection. Separate requirements can use separate
instances of the generic callable.

On the right of `<:`, a generic callable requires the comparison to hold for an
arbitrary parameter value:

```text
(object) -> never <: forall X. (X) -> X
```

This holds because the left callable accepts every possible argument and
returns a subtype of every possible result. `(Dog) -> Dog` fails the same
requirement because it cannot handle arbitrary `X`.

Selections must be generic-free: their rewritten types contain no `forall`.
Metavariables can still receive generic callables. Nested binders have lexical
scope, so an inner callable can refer to an outer parameter.

Restrictions are part of the type's meaning. An upper bound replaces each use
of the parameter with its intersection with that bound. An exact set represents
an intersection of the permitted callable instances. Printed types use this
rewritten form, so their spelling can differ from the source. Restrictions
cannot contain metavariables, generic callables, or bound generic parameters;
exact sets must be non-empty. See
[parameter restrictions](docs/project_design.md#parameter-restrictions-reduce-to-ordinary-type-expressions)
for the rewrites and their consequences.

### Operator order

From tightest to loosest, operators bind in this order:

```text
&   |   ->   <:   and   or
```

The arrow associates to the right:

```text
A | B & C          means A | (B & C)
(A) -> B | C       means (A) -> (B | C)
(A) -> (B) -> C    means (A) -> ((B) -> C)
```

When a callable or generic callable is a factor of a union or intersection,
put parentheses around the complete callable, as in
`(forall X. (X) -> X) | ((Animal) -> Animal)`.
The [syntax reference](docs/project_design.md#input-syntax-reference) gives the
complete grammar and validation rules.

## Reading results

### Models

A satisfiable result has one model entry per declared metavariable, in
declaration order. Each constrained entry contains a complete type. Parameters
bound by `forall` and recursive references bound by `mu` are part of that type.
Different engines can return different valid assignments.

An entry prints `unconstrained` when the unknown appears in no selected
comparison after source rewriting and normalization. This includes unused
declarations and unknowns mentioned only in unselected branches. Such an entry
can receive any complete type without affecting the selected comparisons.
With only `assert ?T <: object;`, the result is `?T = never`: this is an active
requirement even though it allows any type below `object`.

Constraints can produce recursive types without explicit recursion syntax in
the input:

```text
metavar ?T;
assert tuple[?T] <: ?T;
```

Output:

```text
satisfiable
model:
  ?T = mu R0. tuple[R0]
```

`R0` names the complete tuple type; its element is that same type. The name is
local to the `mu` definition.

Printed output expands every occurrence of a shared subterm in full, so a
printed value can be exponentially larger than its input. The
[output contract](docs/project_design.md#a-model-is-one-checked-witness)
explains the format and its size implications.

### Conflicting assertions

Assertion labels make an unsatisfiable result easier to read:

```text
class Number;
class Text;
metavar ?T;

assert needs_number: Number <: ?T;
assert needs_text: ?T <: Text;
```

Output:

```text
unsatisfiable
core:
  needs_number
  needs_text
```

`unsatisfiable` means that the specified search exhausted its alternatives
without finding a model. The type search is not claimed to be complete over
all possible models.

The `core` reports assertions rejected together. It is subset-minimal: removing
any one reported item makes the remainder satisfiable under the same search,
with all declarations from the original file still in place. This does not
promise the smallest number of items, and other minimal cores can exist.
Unlabelled assertions are identified by source position; the
[core rules](docs/project_design.md#a-core-explains-an-exhausted-failure)
explain how compound assertions are split for reporting.

## Commands

Use `cargo run --` followed by a subcommand, or build once with `cargo build`
and run `target/debug/mini_type_solver`. For example:

```sh
target/debug/mini_type_solver solve --engine varisat example.input
```

| Subcommand | Purpose |
| --- | --- |
| `parse FILE` | Print the parsed syntax tree. |
| `validate FILE` | Check names, inheritance, and supported type forms. |
| `validate --show-mro FILE` | Also print each class's inherited lookup order. |
| `solve FILE` | Print a model or an unsatisfiable core. |

Use `-` as the file name to read standard input. For diagnostics and work
counters:

```sh
cargo run -- solve --log-level info --stats example.input
```

Results go to stdout; logs, statistics, warnings, and errors go to stderr. A
completed solve exits with status 0 for either verdict. Input or file errors
use status 1; command-line usage errors use status 2.

## Choosing a search engine

Use `solve --engine NAME` with `dnf`, `direct`, or `varisat` to choose how to
explore `and` and `or`. All three engines check their selected comparisons with
the same type solver and share the same verdict contract. Their models and
cores can differ because they can choose different branches. `direct` is the
default.

| Engine | Search strategy |
| --- | --- |
| `dnf` | Expand the formula into disjunctive normal form: a list of conjunctions to check in order. All groups are built before checking starts. |
| `direct` | Walk the formula tree, extending a partial choice and backing up when it fails. |
| `varisat` | Use varisat to solve the Boolean satisfiability (SAT) problem, then block selections rejected by the type solver. |

Every engine has exponential worst-case search. DNF also pays for storing all
expanded conjunctions. Use `--stats` to compare work counters as well as elapsed
time; the [design reference](docs/project_design.md#repeatable-output-and-measurable-search-costs)
defines the counters.

Some valid inputs can make type search run indefinitely. There is no default
time or work limit. The [scope](docs/project_design.md#scope) section describes
these limits and the supported feature set. The project models subtype
constraints; it has no source-language expression checking, class members,
structural protocols, or overload resolution.

## Development and benchmarks

Developed with Rust 1.98.1 and Cargo 1.98.1.

Run the repository checks with:

```sh
cargo test
cargo clippy --all-targets
cargo fmt --check
```

Benchmarks compare the engines on four input sets:

- [synthetic](benchmarks/synthetic): 40 cases covering type rules and Boolean search.
- [ty](benchmarks/ty/README.md): 12 cases derived from ty's mdtest suite.
- [Pyrefly](benchmarks/pyrefly/README.md): 13 cases derived from Pyrefly's tests.
- [recursive](benchmarks/recursive): 8 cases covering recursive constraints across
  constructors and generic scopes.

The derived sets encode subtype constraints in this project's language. Their
READMEs link to the original sources, and each input header states the
approximations used. Timings measure solving these encoded constraints.

Run all benchmarks, or filter by set, case, or engine:

```sh
cargo bench --bench solver
cargo bench --bench solver -- '^ty/'
cargo bench --bench solver -- synthetic/32_callable_variance_chain
cargo bench --bench solver -- '/direct$'
```

Each input states its expected verdict, which the runner checks before timing.
Timing includes solving, model construction or core reduction, and discarding
the result. Parsing, validation, and rendering are outside the timed work. To
check benchmark verdicts without collecting timings:

```sh
cargo test --benches
```

## Further reading

- [Project design](docs/project_design.md): type semantics, Boolean search,
  witness checking, output contracts, and the exact input grammar.
- [Rust coding guideline](docs/coding_guideline/index.md): code style and
  architecture rules for this repository.
- [Third-party notices](THIRD_PARTY_NOTICES.md): sources and licenses for copied
  documentation and adapted benchmarks.
