module

public import MalLean4.Env
public import MalLean4.Printer

set_option linter.missingDocs true

open Types

namespace Debug

/-- mal's `DEBUG-EVAL` trace hook: if the symbol `DEBUG-EVAL` is bound to a
truthy value (anything other than `nil` / `false`), print `EVAL: <ast>` to
stdout before evaluation continues. Step `eval` functions call this at the
top of each iteration so users can trace recursion at the mal level.

Fast path: `Env.debugEvalMaybeBound` short-circuits the env walk when
nothing has ever bound `DEBUG-EVAL`, which is the common benchmark case.
The flag is one-way (set by `Env.set` on the first such binding, never
cleared) — once `true`, the env walk takes over and correctly returns
`none` for the not-currently-bound case. -/
public def trace (env : Env) (ast : MalVal) : IO Unit := do
  unless ← Env.debugEvalMaybeBound.get do return
  match ← env.find? "DEBUG-EVAL" with
  | some v =>
    if v.isTruthy then
      IO.println s!"EVAL: {← Printer.prStr ast}"
  | none => return ()

end Debug
