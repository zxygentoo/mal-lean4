# mal-lean4

A [Make-A-Lisp](https://github.com/kanaka/mal) implementation in Lean 4.

## Quickstart

### Dependencies

- **Lean 4** — version pinned in `lean-toolchain` (currently
  `leanprover/lean4:v4.29.1`; required for the new module system). Install
  via [elan](https://github.com/leanprover/elan); the right toolchain is
  fetched automatically on first `lake build`.
- **Python 3** — for the mal test harness at `tests/runtest.py`. Standard
  library only; no `pip install` needed.

```sh
lake build                       # build all step binaries
lake exe step2_eval              # run a step interactively
tests/run.sh                     # run the mal test harness on all steps
tests/run.sh step2_eval          # run tests for one step
```

## Project layout

```
MalLean4/
  Types.lean         MalVal + MalFn
  Env.lean           evaluation environment
  Core.lean          arithmetic builtins + initial env
  Reader.lean        tokenizer + parser (hand-written, no regex)
  Printer.lean       pretty-printer
  Step*.lean         one file per step's executable

tests/
  runtest.py         mal harness (verbatim from upstream)
  step*_*.mal        test cases (verbatim from upstream)
  run.sh             wrapper that builds and invokes runtest.py
```

## Status

| Step             | Executable          | Required tests |
|------------------|---------------------|----------------|
| 0 — REPL         | `step0_repl`        | 4 / 4          |
| 1 — read & print | `step1_read_print`  | 23 / 23        |
| 2 — eval         | `step2_eval`        | 9 / 9          |

Counts cover the spec-required cases only. Deferrable and optional cases
(strings, nil/true/false, reader macros, vectors, hash-maps, quoting)
come online with their assigned later steps.

See [AGENTS.md](AGENTS.md) for project conventions.
