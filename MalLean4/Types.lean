module

namespace Types

/-- The eval monad: IO for builtins like `prn`, with String-typed errors. -/
public abbrev MalIO := ExceptT String IO

mutual

/-- The mal abstract syntax tree. Every value the interpreter manipulates
— read from input, produced by `eval`, formatted by the printer — is one
of these constructors. -/
public inductive MalVal where
  | nil
  | bool : Bool → MalVal
  | int  : Int → MalVal
  | str  : String → MalVal
  | sym  : String → MalVal
  | list : List MalVal → MalVal
  | fn   : Fn → MalVal
  | atom : Nat → MalVal

/-- A callable: either a `builtin` (resolved by name via `Core.callBuiltin`)
or a `lambda` from `fn*`. `lambda` is closure-converted — it stores params,
body, and a snapshot of free variables captured at `fn*` time. No `Env` is
stored; unresolved names defer to the caller's env at apply time. -/
public inductive Fn where
  | builtin : String → Fn
  | lambda  (params : List String) (body : MalVal) (captures : List (String × MalVal)) : Fn

end

/-- Mal's truthiness: only `nil` and `false` are falsy. Everything else
(including 0, the empty list, and the empty string) is truthy. -/
public def MalVal.isTruthy : MalVal → Bool
  | .nil        => false
  | .bool false => false
  | _           => true

end Types
