# AGENTS.md

Conventions for AI agents working in this repo.

This project implements [Mal](https://github.com/kanaka/mal) in Lean 4.
Each step (`step0_repl`, …, `stepA_mal`) is a `lean_exe`; shared library
code lives in `MalLean4/`; tests run via `tests/run.sh`.

## Module layout

Library and step files follow different conventions.

|                    | Library files | Step files |
|--------------------|---------------|------------|
| Examples           | `Types.lean`, `Env.lean`, `Core.lean`, `Reader.lean`, `Printer.lean` | `Step0Repl.lean`, `Step1ReadPrint.lean`, … |
| File header        | `module`      | (none)     |
| Namespace          | `namespace X … end X` | flat |
| Default visibility | private       | public     |
| `main`             | n/a           | required, at root namespace |

`main` must live at the root namespace — the linker won't find it inside
any `namespace` block — which is what forces step files to stay flat (no
namespace, no opting into the new module system).

## Public surface

Mark only what's actually called from outside the file as `public`. New
declarations start private; promote `private → public` when an external
caller appears, demote when the last caller goes away.

Every `public` declaration in the library needs a doc comment, enforced by
`linter.missingDocs` (configured in `lakefile.toml`, library scope only).
Silence the linter by writing the docstring, never by toggling it off.

## Imports

Use `public import X` when names from X appear in your module's public
signatures. The new module system enforces this — a public declaration
referencing a privately-imported name fails to compile, with the suggested
fix in the error message. Use plain `import X` for purely internal
dependencies.

In step files, import only the immediate entry-points you call (e.g.
`Reader`, `Printer`, `Core`). Each library module's `public import` chain
carries the underlying types (`MalVal`, `MalFn`, `Env`) along — don't
repeat what other imported modules already re-export.

## `partial`

Default to `def`. Only add `partial` when Lean's termination checker
rejects the function, and distinguish the two cases when it does:

- **Truly non-terminating** (e.g., the REPL `loop`, which recurses with no
  decreasing argument): `partial` is correct.
- **Terminating but proof-evading** (e.g., `tokenize` recursing through
  `List.dropWhile`, where the decrease isn't visible at the call site):
  `partial` is the pragmatic choice; switch to `termination_by` if a manual
  proof is tractable.

The checker handles more than you might expect, including nested recursion
through `List.map`/`List.mapM` over structural subterms. Don't preemptively
mark `partial`.

## Match arms

Align `=>` within a single match by padding patterns with spaces so all
arrows sit at the same column.

**Exception:** the catch-all `| _ => …` always stays as `| _ => …` — a
wildcard is visually distinct enough that padding it out to match its
longer siblings adds noise without aiding the scan:

```
| .sym k :: rhs :: rest => do
  let v ← eval env rhs
  env.set k v
| _ => throw "let*: bindings must be sym/expr pairs"
```

Bodies that fit inline go after `=>`. Multi-line bodies either continue
on the `=>` line with a body-starting keyword (`do`, `let`, `if`) and
indent 2 spaces under the case's `|` column, or break to a new line at
the same +2 indent. Prefer the same-line form when there's just one
keyword; break to a new line for nested `match` so the inner `|` cases
don't visually clash with the outer ones.

Skip the alignment entirely for a match where one pattern is so much
longer than its peers that padding would create comically wide gaps —
readability beats mechanical consistency.

## Known leaks

The `Atoms.store` (`IO.Ref (Array (IO.Ref MalVal))` in `Atoms.lean`) holds
every atom for the lifetime of the process. Atoms allocated in transient
scopes (e.g. `(let* (a (atom 0)) (do-something-without-returning-a))`)
don't get freed even when their `MalVal.atom` handle is unreferenced.

This is structural, not a bug: Lean's strict positivity rejects
`Atom : IO.Ref MalVal → MalVal` directly, so we indirect through a `Nat`
id into an external table. The table is the storage that keeps the cells
alive past their use.

Real fixes considered and rejected:
- `unsafe inductive` for the atom case — contagious `unsafe` keyword across
  every `MalVal`-touching def. Same tradeoff we declined for closures.
- `opaque Cell : Type` with FFI-backed `IO.Ref MalVal` underneath — gets
  proper RC, but requires C glue and shifts the project from "Lean only"
  to "Lean + FFI."
- Periodic compaction of the table — requires walking live values to
  compute liveness, substantial work.

The leak is bounded by atom-creation count within a single process. The
test harness uses fresh processes per step, so tests don't observe it.
An interactive session that defines a thousand atoms accumulates ~hundreds
of KB; this is acceptable for the project's scope.
