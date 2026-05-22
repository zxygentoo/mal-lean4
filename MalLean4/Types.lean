module

namespace Types

/-- The eval monad: IO for builtins like `prn`, with String-typed errors. -/
public abbrev MalIO := ExceptT String IO

mutual

/-- The mal abstract syntax tree.

Every value the interpreter manipulates — read from input, produced by
`eval`, formatted by the printer — is one of these constructors. Functions
share a single `fn` constructor that wraps `Fn`; the value type carries no
indirection through a registry.
-/
public inductive MalVal where
  | nil
  | bool : Bool → MalVal
  | int  : Int → MalVal
  | str  : String → MalVal
  | sym  : String → MalVal
  | list : List MalVal → MalVal
  | fn   : Fn → MalVal
  | atom : Nat → MalVal

/-- A callable: either a Lean-implemented `builtin` (looked up by name in
`Core.builtinTable`) or a user-defined `lambda` from `fn*`.

`lambda` is closure-converted: it stores its parameter names, its body AST,
and a snapshot of free variables captured at `fn*` time. There is **no**
captured `Env` — top-level lookups defer to the caller's env at apply time,
which gives mal's "closures see later `def!`s" semantics while keeping the
value type free of cycles.
-/
public inductive Fn where
  | builtin : String → Fn
  | lambda  (params : List String) (body : MalVal) (captures : List (String × MalVal)) : Fn

end

end Types
