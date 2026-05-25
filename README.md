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
tests/run.sh lib                 # run lib tests against stepA_mal
```

## Project layout

```
MalLean4/
  Types.lean         MalVal (incl. vec/map/keyword/withMeta wrapper) + Fn + Lambda
  Env.lean           env frames + global env registry (`Env.store`, indexed by Nat)
  Atoms.lean         atom registry (mal's explicit mutable cells)
  Core.lean          builtins + initialEnv + Context (private)
  Debug.lean         DEBUG-EVAL trace hook
  GC.lean            mark-and-sweep over `Env.store` and `Atoms.store`
  Reader.lean        tokenizer + parser (hand-written, no regex)
  Printer.lean       pretty-printer
  Step*.lean         one file per step's executable
  StepAMal.lean      final step: macros + try* + quasi + variadic + *host-language*

tests/
  runtest.py         mal harness (verbatim from upstream)
  step*_*.mal        test cases (verbatim from upstream)
  run.sh             wrapper that builds and invokes runtest.py
  test.txt, *.mal    fixtures for step 6 (slurp / load-file targets)
```

## Status

All 863 step tests pass — required, deferrable, and optional:

| Step              | Executable          | Tests           |
|-------------------|---------------------|-----------------|
| 0 — REPL          | `step0_repl`        | 4 / 4           |
| 1 — read & print  | `step1_read_print`  | 64 / 64         |
| 2 — eval          | `step2_eval`        | 12 / 12         |
| 3 — environments  | `step3_env`         | 38 / 38         |
| 4 — if/fn/do      | `step4_if_fn_do`    | 199 / 199       |
| 5 — TCO           | `step5_tco`         | 8 / 8           |
| 6 — file/eval     | `step6_file`        | 71 / 71         |
| 7 — quote         | `step7_quote`       | 124 / 124       |
| 8 — macros        | `step8_macros`      | 61 / 61         |
| 9 — try/catch     | `step9_try`         | 173 / 173       |
| A — mal           | `stepA_mal`         | 113 / 113       |

The upstream library tests (`tests/lib/*.mal`) also pass: 168 / 169
against `stepA_mal`. The single failure is `memoize.mal`, which runs
naïve `(fib 32)` (~5M calls, exponential — TCO doesn't help shape, just
depth). Our interpreter is fast enough to handle ~1M iterations in 7.5s,
so fib(32) needs roughly 40s and times out at the harness limit.

`stepA_mal` has real TCO — `eval` is a `while true` loop with mutable
`env`/`ast`; tail-position forms (`let*` body, `do` last, `if` branch,
lambda application body, `quasiquote` rewrite, bare `try*`) update the
locals and continue. Native deep tail recursion runs 10M-deep without
stack growth; self-host (`stepA_mal stepA_mal.mal` from upstream
`impls/mal/`) runs ~10k user-level recursions in seconds and ~50k in a
few minutes — bounded by interpretation throughput, not stack. Step5–9
still use recursive eval (Lean's compiler optimizes monadic tail calls
well enough for their native test cases); propagating the loop shape
back is mechanical follow-up.

## Follow-ups

- **Self-host throughput.** ~5 ms per mal-level iteration through
  mal-in-mal. Most of that is mal-in-mal's `EVAL` doing dispatch in mal,
  not host overhead. Compile-time macros (`(def! and ^{:inline? true}
  and)` etc.) and a faster builtin-lookup path would help.
- **Propagate TCO to step5–9.** Mechanical translation of stepA's loop
  shape.

See [AGENTS.md](AGENTS.md) for project conventions.
