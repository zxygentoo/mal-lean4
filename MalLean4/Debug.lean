module

public import MalLean4.Env
public import MalLean4.Printer

open Types

namespace Debug

-- mal's `DEBUG-EVAL` trace hook: prints `EVAL: <ast>` before evaluation
-- when the symbol is bound to a truthy value. The
-- `debugEvalMaybeBound` short-circuit skips the env walk entirely in
-- the common benchmark case where nothing ever binds `DEBUG-EVAL`.
public def trace (env : Env) (ast : MalVal) : IO Unit := do
  unless ← Env.debugEvalMaybeBound.get do return
  match ← env.find? "DEBUG-EVAL" with
  | some v =>
    if v.isTruthy then
      IO.println s!"EVAL: {← Printer.prStr ast}"
  | none => return ()

end Debug
