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

## External-table indirection

`MalVal.atom n` and `Lambda.outerEnvId` both index into external tables
(`Atoms.store` in `Atoms.lean`, `Env.store` in `Env.lean`) instead of
holding the referent directly. The indirection is structural, not a
bug: Lean's strict positivity rejects `MalVal.atom : IO.Ref MalVal → MalVal`
and `Lambda { outerEnv : Env }` directly (because `Env` chains back
through `MalVal`), so each constructor holds a `Nat` id and the table
stores the actual data.

Real fixes considered and rejected:
- `unsafe inductive` for the atom and env cases — contagious `unsafe`
  keyword across every `MalVal`-touching def.
- `opaque Cell : Type` with FFI-backed `IO.Ref MalVal` underneath — gets
  proper RC, but requires C glue and shifts the project from "Lean only"
  to "Lean + FFI."

## Garbage collection

`GC.lean` implements mark-and-sweep over the two tables: walk every value
reachable from the root env (lists/vectors/maps/meta wrappers descend
into their children, lambdas mark their `outerEnvId` and recurse into
that env's bindings, atoms mark their id and recurse into the cell's
value), then `none`-out unreached slots in both stores. The array itself
still grows by one `Option` slot per allocation; the heavy payload (the
captured frame's `HashMap` and the values it pinned) becomes collectable.

`GC.maybeRun` fires at two host-safe points: (1) the REPL loop between
top-level expressions and (2) between sequenced forms inside `evalDo`'s
`x :: xs` case. The trigger threshold is ~1000 new `Env.store`
registrations since the last sweep.

`evalDo`-between-forms is safe because the previous form's result has
been bound to `_` (discarded), the remaining `xs` are unevaluated AST
(no live closures), and walking `env` catches everything that's still
live. This covers script-mode self-host: both mal-in-mal's main REPL
loop and its `EVAL` body are `(do …)` sequences, so GC fires once per
mal-level expression even though our host REPL loop never gets a turn.

Other "between sub-evaluations" spots aren't safe — `evalLet` would
need to walk from `letEnv` instead of `env` (the new bindings aren't
reachable from `env` yet), and `evalCall` mid-args has partially built
values on the host stack that aren't in any env. No `(gc)` builtin is
exposed for the same reason: user code can't reliably tell whether
it's at a host-safe point.

## Closures and lexical scope

`Lambda` stores `outerEnvId : Nat` instead of capturing free variables by
value. At `fn*` time, `Env.register env` files the current env in
`Env.store` and the id goes into the lambda. At `apply` time, we
`Env.lookup l.outerId` to retrieve the env and create the closure's
binding frame as its child — not as a child of the caller's env.

This matters for two things:
- **Lexical scope**: `(let* (x 3) (a))` where `a` was defined at top
  level with body referencing `x` sees the top-level `x`, not the let's.
- **Live updates**: `(def! x 1) (def! f (fn* () x)) (def! x 2) (f)`
  returns 2, because the closure looks `x` up in the captured env at
  call time.

`Env.findLocal?` and a separate `FreeVars` analysis used to live here for
value-snapshot capture — both are gone now that the id-based approach
makes them unnecessary.

## Metadata

`MalVal.withMeta value meta` is a wrapping constructor. The printer,
equality, and every type predicate transparently strip the wrapper via
`MalVal.strip`; only `meta` and `with-meta` (and `apply` when deciding
whether the head is callable) see it. Construction sites in the reader
(`^meta value` reader macro) and the runtime (`with-meta` builtin) are
the only places that produce `.withMeta`.
