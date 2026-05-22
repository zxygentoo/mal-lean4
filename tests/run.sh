#!/usr/bin/env bash
# Run mal step tests against our Lean implementations.
#
# Usage:
#   tests/run.sh                       # run all configured steps
#   tests/run.sh step0_repl            # run a single step (any of:
#   tests/run.sh step0_repl.mal        # step0_repl, step0_repl.mal,
#   tests/run.sh tests/step0_repl.mal  # or tests/step0_repl.mal)
#   tests/run.sh step1_read_print --no-deferrable
#
# Extra args after the step are forwarded to runtest.py.

set -e

cd "$(dirname "$0")/.."

# step name -> extra runtest.py flags
declare -A STEP_OPTS=(
  [step0_repl]=""
  [step1_read_print]="--no-deferrable --no-optional"
  [step2_eval]="--no-deferrable --no-optional"
  [step3_env]="--no-deferrable --no-optional"
  [step4_if_fn_do]="--no-deferrable --no-optional"
  [step5_tco]="--no-deferrable --no-optional"
  [step6_file]="--no-deferrable --no-optional"
  [step7_quote]="--no-deferrable --no-optional"
)

normalize() {
  local arg="$1"
  arg="${arg#tests/}"
  arg="${arg%.mal}"
  echo "$arg"
}

run_one() {
  local step
  step="$(normalize "$1")"; shift
  if [[ -z "${STEP_OPTS[$step]+x}" ]]; then
    echo "Unknown step: $step" >&2
    echo "Available: ${!STEP_OPTS[*]}" >&2
    exit 1
  fi
  local extra="${STEP_OPTS[$step]}"
  echo "=== $step (opts: ${extra:-none}) ==="
  lake build "$step" >/dev/null
  python3 -W ignore::SyntaxWarning tests/runtest.py $extra "$@" "tests/${step}.mal" -- "$(pwd)/.lake/build/bin/$step"
}

if [[ $# -eq 0 ]]; then
  for step in "${!STEP_OPTS[@]}"; do
    run_one "$step"
  done
else
  step="$1"; shift
  run_one "$step" "$@"
fi
