# AGENTS.md

Instructions for coding agents working in this repository.

## Sources of truth

- [README.md](README.md) — what this project is and where the docs live.
- [docs/project_design.md](docs/project_design.md) — living design reference.
  Follow it; do not invent behavior it does not specify unless explicitly asked.
- [docs/coding_guideline/index.md](docs/coding_guideline/index.md) — Rust coding guideline
  for all Rust code.

## Commands

- Build: `cargo build`
- Test: `cargo test`
- Lint: `cargo clippy --all-targets`
- Format check: `cargo fmt --check`

## Code Style Preferences

**Design philosophy**
- Explicit is better than implicit.
- Prefer "dumb", obvious code that static tooling (type checker, linter) can reason about. Avoid "smart" code built on macro-heavy designs or complex trait hierarchies.
- Prefer composition. Keep trait hierarchies flat and small.
- Prefer immutable data at boundaries, but use local mutation in function scopes. 
- Keep It Simple Stupid (KISS) by reducing the "Concept Count". That means, strive for fewer functions or methods, fewer helpers. If a helper is only called by a single callsite, then prefer to inline it when the caller stays short and clear. Keep or extract a named helper when inlining would make the caller too long or harder to follow. Split long functions into complete operations.
- At the same time, Don't Repeat Yourself (DRY). There is a tension between KISS and DRY. If DRY forces a new helper, first look for a way to remove the complicated work itself.
- If code has many conditionals, find a simpler way to do the same work.
- Design data models so that impossible states are unrepresentable by using Sum Types for "OR" logic, and Product Types only for "AND" logic. For example:
  - Avoid the "bag of optionals" anti-pattern. Do not pair a `bool` discriminator with optional fields. Use `None` for the "off" state, and a type that guarantees all fields are present.
  - Never use raw strings for bounded choices (unless for CLI arg parsing at the boundary).
  - Tie state directly to the presence of data. If a value exists only in some states, encode that in the type. Do not allow `None` where a value must always be present.

**Coding discipline**
- Try hard to avoid patterns that require `panic!`, `unreachable!`, `.unwrap()` or `.expect()`. Instead, try to encode those constraints in the type system. Accept verbose code or large refactors if they remove these calls. But when the type system cannot encode a constraint and you detect a programming bug, panic with a clear message instead of returning an error.
- Prefer let chains (`if let ... && ...`) and match guards over nested `if let`. They reduce indentation. At the end of a task, check for missed opportunities to use them.
- If you must suppress a Clippy lint, prefer `#[expect]` over `#[allow]`. If a lint reports dead code, delete the code instead.
- Do not use paths rooted at `std`, `crate`, `super`, or an external crate outside `use` statements. Paths through an imported module, associated items, enum variants, `Self`, and macros are allowed.
- Do not narrate code in comments. Use comments to explain invariants and why unusual code is written that way. Write for a first-time reader. Use plain language. Avoid jargon. Be verbose if the explanation needs it. 

**Visibility and module ownership**
- Use only `pub` and default private visibility in handwritten Rust. Do not use `pub(crate)`, `pub(super)`, `pub(self)`, or `pub(in ...)`.
- Design explicit public APIs between modules. Keep implementation modules and fields private by default. Keep invariant-bearing fields private. The owning module must control construction and mutation of checked types. Consumers must use operations that preserve those invariants and immutable queries.
- Adjust module or crate structure when an API boundary requires it. Do not expose storage or an unchecked constructor to work around a privacy error. Keep modules that own checked types small, because descendants can access their private items. Give each user-facing item one public path.

**Test discipline**
- When a test fails on a value you computed by hand, find which side is wrong before you edit. Fix the side that the derivation contradicts. Never change an expectation you cannot derive. Never weaken correct code to make a self-authored test pass.
- Hold a high bar for adding tests. Each test must pin a meaningful semantic decision. Never add a test for the sake of adding tests: no trivial tests, and no tests that only demonstrate what the current implementation does.

**Output discipline**
- Strictly separate data output (`stdout`) from logging/diagnostics/errors (`stderr`).

**Clean engineering**
- Document code with invariants. State what a function assumes about shared data and how it upholds those assumptions. Also document architecture invariants.
- Address prerequisites cleanly, don't hack around them. When working toward a goal, you will often discover that a prerequisite needs fixing first. Never hack around it to reach the goal faster. If you find an "asked for X, but need Y first, and that needs Z" situation, be loud: stop, describe the better-engineering detour and why it matters, and wait for approval before you start it.
- Always review your own code for correctness and better-engineering after a coding session is finished.

**Commit discipline**
- Leave the working tree uncommitted for the user to review; commit only when explicitly asked.
- Do not write a laundry list of implementation changes. Focus on:
  - **Why**: what problem or design gap motivated the change
  - **What**: the solution approach, not individual file edits
  - **Why it works**: the key mechanism that makes the solution correct
- A reader must understand the intent from the message alone. They must not need to read the code.

## Communication style

Use ASD-STE100 Simplified Technical English as a guideline for technical text, especially code comments, commit messages, and docs. STE is the controlled language that aerospace and defense manufacturers use for maintenance documentation. It exists so that a tired reader who is not a native English speaker cannot misread an instruction. Write short sentences. Use one word for one meaning. Remove hedges, filler, and decorative clauses. Write for that tired reader. Each sentence must survive one read.

Docs describe the current state only. Unless being explicitly asked, never use docs (including this file) as progress trackers: no status sections, roadmaps, or "not yet implemented" notes.
