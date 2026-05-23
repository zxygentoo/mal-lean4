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
or a `lambda` from `fn*` (see `Lambda`). -/
public inductive Fn where
  | builtin : String → Fn
  | lambda  : Lambda → Fn

/-- A closure-converted user function. Holds params, body, and a snapshot
of free variables captured at `fn*` time. No `Env` is stored; unresolved
names defer to the caller's env at apply time. -/
public structure Lambda where
  public mk ::
  public isMacro  : Bool := false
  public params   : List String
  public body     : MalVal
  /-- Free-variable snapshot taken at `fn*` time: `(name, value)` pairs. -/
  public snapshot : List (String × MalVal)

end

/-- Mal's truthiness: only `nil` and `false` are falsy. Everything else
(including 0, the empty list, and the empty string) is truthy. -/
public def MalVal.isTruthy : MalVal → Bool
  | .nil        => false
  | .bool false => false
  | _ => true

/-- Structural equality on `MalVal`. Lists compare element-wise; atoms by
identity (Nat id), so two `(atom 0)` calls produce non-equal values. -/
public partial def MalVal.equal : MalVal → MalVal → Bool
  | .nil,         .nil         => true
  | .bool a,      .bool b      => a == b
  | .int a,       .int b       => a == b
  | .sym a,       .sym b       => a == b
  | .str a,       .str b       => a == b
  | .atom a,      .atom b      => a == b
  | .list xs,     .list ys     => listEqual xs ys
  | _,            _            => false
where
  listEqual : List MalVal → List MalVal → Bool
    | [],      []      => true
    | x :: xs, y :: ys => MalVal.equal x y && listEqual xs ys
    | _,       _       => false

end Types
