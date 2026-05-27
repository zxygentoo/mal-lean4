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
make test                        # all step suites (deferrable + optional on)
make test^step5_tco              # one step's suite
make test^lib                    # all canonical lib tests against stepA
make test^lib^memoize            # one lib test
make test^mal                    # all mal-in-mal step suites hosted on stepA
make test^mal^step4_if_fn_do     # one mal-in-mal step
make bench                       # fib(25) x 3 and fib(28) x 3
make repl                        # interactive stepA
make repl^mal                    # interactive mal-in-mal stepA on stepA host
make clean                       # `lake clean`
```

Tests run with deferrable + optional enabled — same default as upstream
`make test^<impl>`. For a quick partial pass during dev, override:
`make test OPTS="--no-deferrable --no-optional"`.

Tests use upstream's `runtest.py` via `--rundir mal/tests/`, so paths
like `(load-file "../lib/perf.mal")` resolve against the upstream tree.
The same rundir lets `mal-in-mal`'s `(load-file "../mal/env.mal")` find
`mal/impls/mal/env.mal` (because `mal/tests` is itself a symlink to
`mal/impls/tests`, so `..` resolves into `mal/impls/`).

## Implementation notes

- **GC registries grow unbounded.** Captured envs and atoms live in two
  append-only tables (`Env.store`, `Atoms.store`) that `MalVal.atom` /
  `Lambda` index into by `Nat` (a strict-positivity workaround). The
  mark-and-sweep in `GC.lean` reclaims the *payloads* — the captured
  `HashMap`s and atom cells — by nulling unreachable slots, but the tables
  themselves never shrink; they grow one `Option` slot per allocation for
  the life of the process.

- **Tail calls.** `stepA_mal`'s `eval` is a `while true` trampoline with
  mutable `env`/`ast`; tail-position forms (`let*` body, `do` last, `if`
  branch, lambda-application body, `quasiquote` rewrite, bare `try*`) rebind
  the locals and continue instead of recursing on the host stack — native
  deep tail recursion runs 10M-deep without stack growth, and `stepA` can
  host mal-in-mal without divergence. Steps 5–9 keep a recursive `eval`;
  Lean optimizes their monadic tail calls well enough for the test cases.

- **`time-ms` returns real monotonic milliseconds** (no forced tick), so
  `run-fn-for`/`perf3` and other benchmarks measure real elapsed time. The
  trade: the upstream *optional* `time-ms` test asserts time advanced right
  after sub-millisecond work, which can't hold at integer-ms resolution, so
  it soft-fails on fast machines. We take honest perf numbers over a +1 ms
  tick that passes that test but caps `perf3` at a constant.

See [AGENTS.md](AGENTS.md) for project conventions.
