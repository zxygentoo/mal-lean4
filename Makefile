# mal-lean4 test/build orchestration. Canonical tests + lib live in the
# `mal/` git submodule; this Makefile drives upstream's runtest.py against
# our `lake`-built binaries via the root `run` launcher.
#
# Usage:
#   make                          # alias for `make build`
#   make build                    # `lake build` (all step exes)
#   make test                     # all step suites, no-deferrable / no-optional
#   make test^step5_tco           # one step's suite
#   make test^stepA-full          # stepA with deferrable+optional enabled
#   make test^lib                 # all tests/lib/*.mal against stepA
#   make test^lib^memoize         # one lib test
#   make test^mal                 # all mal-in-mal step suites hosted on stepA
#   make test^mal^step4_if_fn_do  # one mal-in-mal step
#   make test^mal-full            # mal-in-mal stepA with deferrable+optional
#   make bench                    # fib(25) x 3 and fib(28) x 3
#   make repl                     # interactive stepA
#   make repl^mal                 # interactive mal-in-mal stepA on stepA host
#   make clean                    # `lake clean`

LAKE     := lake
MAL      := mal
RUN      := $(abspath run)
RUNTEST  := python3 -W ignore::SyntaxWarning $(abspath $(MAL)/runtest.py)
RUNDIR   := $(abspath $(MAL)/tests)

STEPS    := step0_repl step1_read_print step2_eval step3_env step4_if_fn_do \
            step5_tco step6_file step7_quote step8_macros step9_try stepA_mal

# Mal-in-mal step files. Step5 is omitted: mal-in-mal doesn't ship a
# `step5_tco.mal` since TCO is supplied by the host language anyway.
MIM_STEPS    := step0_repl step1_read_print step2_eval step3_env step4_if_fn_do \
                step6_file step7_quote step8_macros step9_try stepA_mal

LIB_TESTS := $(notdir $(basename $(wildcard $(MAL)/tests/lib/*.mal)))

STEP_TARGETS := $(STEPS:%=test^%)
LIB_TARGETS  := $(LIB_TESTS:%=test^lib^%)
MIM_TARGETS  := $(MIM_STEPS:%=test^mal^%)

# Mal-in-mal is interpretation on top of interpretation; double the
# default timeouts so even the slower steps finish.
MIM_TIMEOUT  := --start-timeout 60 --test-timeout 180

# Pass extra args through: `make test^step5_tco OPTS="--hard"`.
OPTS         ?=
DEFAULT_OPTS := --no-deferrable --no-optional

.PHONY: all build test test^lib test^stepA-full test^mal test^mal-full bench \
        repl repl^mal clean check-submodule \
        $(STEP_TARGETS) $(LIB_TARGETS) $(MIM_TARGETS)

all: build

check-submodule:
	@test -f $(MAL)/runtest.py || { \
	  echo 'mal/ submodule not initialized. Run: git submodule update --init'; \
	  exit 1; }

build: check-submodule
	$(LAKE) build

test: $(STEP_TARGETS)

# Static pattern rule (vs. plain `test^%:`) so .PHONY actually applies to
# the listed targets — GNU make won't dispatch a phony name through a
# bare pattern rule. `STEP=$*` matches upstream's `env STEP=…` convention
# so the `run` launcher selects the correct binary (it defaults to
# stepA_mal otherwise).
$(STEP_TARGETS): test^%: build
	@echo '=== $* ==='
	STEP=$* $(RUNTEST) --rundir $(RUNDIR) $(DEFAULT_OPTS) $(OPTS) $*.mal -- $(RUN)

# stepA with deferrable+optional flags on (full conformance).
test^stepA-full: build
	@echo '=== stepA_mal (deferrable + optional) ==='
	$(RUNTEST) --rundir $(RUNDIR) $(OPTS) stepA_mal.mal -- $(RUN)

test^lib: $(LIB_TARGETS)

# Lib tests always run against stepA_mal (no STEP override).
$(LIB_TARGETS): test^lib^%: build
	@echo '=== lib/$* ==='
	$(RUNTEST) --rundir $(RUNDIR) $(OPTS) lib/$*.mal -- $(RUN)

# Mal-in-mal: our stepA_mal binary loads `mal/impls/mal/$*.mal`, which
# implements a mal interpreter in mal. The canonical tests then drive
# that two-level stack via stdin/stdout. STEP is unset so `run` defaults
# to stepA_mal (the host); the guest step is selected by the file path.
test^mal: $(MIM_TARGETS)

$(MIM_TARGETS): test^mal^%: build
	@echo '=== mal/$* (mal-in-mal hosted on stepA_mal) ==='
	$(RUNTEST) --rundir $(RUNDIR) $(MIM_TIMEOUT) $(DEFAULT_OPTS) $(OPTS) \
	  $*.mal -- $(RUN) $(abspath $(MAL)/impls/mal/$*.mal)

# Mal-in-mal stepA with deferrable+optional flags on. Same caveats as
# test^stepA-full: slow, but the conformance gold standard.
test^mal-full: build
	@echo '=== mal/stepA_mal (mal-in-mal, deferrable + optional) ==='
	$(RUNTEST) --rundir $(RUNDIR) $(MIM_TIMEOUT) $(OPTS) \
	  stepA_mal.mal -- $(RUN) $(abspath $(MAL)/impls/mal/stepA_mal.mal)

bench: build
	@cd $(MAL)/tests && for N in 25 28; do \
	  echo "=== fib($$N) x 3 ==="; \
	  $(RUN) fib.mal $$N 3; \
	done

repl: build
	$(RUN)

# Interactive mal-in-mal REPL: our stepA hosts mal-in-mal's stepA_mal.mal
# as the interpreter.
repl^mal: build
	$(RUN) $(abspath $(MAL)/impls/mal/stepA_mal.mal)

clean:
	$(LAKE) clean
