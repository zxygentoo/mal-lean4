# mal-lean4

A [Make-A-Lisp](https://github.com/kanaka/mal) implementation in Lean 4.

## Quickstart

### Dependencies

- **Lean 4** — version pinned in `lean-toolchain` (currently
  `leanprover/lean4:v4.29.1`; required for the new module system). Install
  via [elan](https://github.com/leanprover/elan); the right toolchain is
  fetched automatically on first `lake build`.
- **Python 3** — for upstream's `runtest.py` (in the `mal/` submodule).
  Standard library only; no `pip install` needed.

### Clone repo

Canonical tests, library files, and `runtest.py` live in upstream's
[`mal`](https://github.com/kanaka/mal) repo, vendored as the `mal/`
submodule. Clone with submodules in one go:

```sh
git clone --recurse-submodules https://github.com/zxygentoo/mal-lean4.git
cd mal-lean4
```

Or initialize submodules after a plain clone:

```sh
git clone https://github.com/zxygentoo/mal-lean4.git
cd mal-lean4
git submodule update --init
```

### Build & test

```sh
make                             # alias for `make build`
make build                       # `lake build` (all step exes)
make test                        # all step suites (no deferrable / no optional)
make test^step5_tco              # one step's suite
make test^stepA-full             # stepA with deferrable + optional flags on
make test^lib                    # all canonical lib tests against stepA
make test^lib^memoize            # one lib test
make test^mal                    # all mal-in-mal step suites hosted on stepA
make test^mal^step4_if_fn_do     # one mal-in-mal step
make test^mal-full               # mal-in-mal stepA with deferrable + optional
make bench                       # fib(25) x 3 and fib(28) x 3
make repl                        # interactive stepA
make repl^mal                    # interactive mal-in-mal stepA on stepA host
make clean                       # `lake clean`
```

Tests use upstream's `runtest.py` via `--rundir mal/tests/`, so paths
like `(load-file "../lib/perf.mal")` resolve against the upstream tree.
The same rundir lets `mal-in-mal`'s `(load-file "../mal/env.mal")` find
`mal/impls/mal/env.mal` (because `mal/tests` is itself a symlink to
`mal/impls/tests`, so `..` resolves into `mal/impls/`).

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

The upstream library tests (`mal/tests/lib/*.mal`) also pass: 168 / 169
against `stepA_mal`. The single failure is `memoize.mal`, which runs
naïve `(fib 32)` (~5M calls, exponential — TCO doesn't help shape, just
depth). Our interpreter is fast enough to handle ~1M iterations in 7.5s,
so fib(32) needs roughly 40s and times out at the harness limit.

Mal-in-mal (`make test^mal`): all 10 hosted-step suites pass (step5_tco
is skipped — mal-in-mal doesn't ship one, TCO is the host's job). The
full `make test^mal-full` (stepA deferrable + optional) also passes —
113 / 113 — confirming our stepA can host mal-in-mal's mal-language
interpreter without divergence.

`stepA_mal` has real TCO — `eval` is a `while true` loop with mutable
`env`/`ast`; tail-position forms (`let*` body, `do` last, `if` branch,
lambda application body, `quasiquote` rewrite, bare `try*`) update the
locals and continue. Native deep tail recursion runs 10M-deep without
stack growth; mal-in-mal hosting (see `make repl^mal`) runs ~10k
user-level recursions in seconds, bounded by interpretation throughput
rather than stack. Step5–9 still use recursive eval — Lean's compiler
optimizes their monadic tail calls well enough for the native test
cases.

See [AGENTS.md](AGENTS.md) for project conventions.
