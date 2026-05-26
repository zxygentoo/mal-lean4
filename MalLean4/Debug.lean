module

public import MalLean4.Env
public import MalLean4.Printer

set_option linter.missingDocs true

open Types

namespace Debug

/-- mal's `DEBUG-EVAL` trace hook: if the symbol `DEBUG-EVAL` is bound to a
truthy value (anything other than `nil` / `false`), print `EVAL: <ast>` to
stdout before evaluation continues. Step `eval` functions call this at the
top of each iteration so users can trace recursion at the mal level. -/
public def trace (env : Env) (ast : MalVal) : IO Unit := do
  match ← env.find? "DEBUG-EVAL" with
  | some v =>
    if v.isTruthy then
      IO.println s!"EVAL: {← Printer.prStr ast}"
  | none => return ()

end Debug
