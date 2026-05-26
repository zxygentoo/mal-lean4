# tests/

Impl-specific test overrides (currently empty).

Canonical mal tests, library tests, and `runtest.py` live in the
[`mal/`](../mal/) git submodule. `make test` drives them automatically.

This directory exists for cases where we need to override or augment an
upstream test — same convention as upstream's `impls/<lang>/tests/`
(e.g. ocaml's `step5_tco.mal` skipping the 100K-recursion case). If you
need to add one, name it after the step (`stepN_<feature>.mal`) and wire
it into the `Makefile`'s test rule.
