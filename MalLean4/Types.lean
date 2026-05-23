module

namespace Types

mutual

/-- The mal abstract syntax tree. Every value the interpreter manipulates
— read from input, produced by `eval`, formatted by the printer — is one
of these constructors. -/
public inductive MalVal where
  | nil
  | bool : Bool → MalVal
  | int  : Int → MalVal
  | str  : String → MalVal
  | kw   : String → MalVal
  | sym  : String → MalVal
  | list : List MalVal → MalVal
  | vec  : List MalVal → MalVal
  | map  : List (MalVal × MalVal) → MalVal
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
  /-- True when bound via `defmacro!`; eval expands macro calls before
  applying. -/
  public isMacro  : Bool := false
  /-- Positional parameter names. -/
  public params   : List String
  /-- Optional rest-parameter name bound by `&` to a list of remaining args. -/
  public restParam : Option String := none
  /-- Unevaluated body form; `apply` evaluates this against the call-time env. -/
  public body     : MalVal
  /-- Free-variable snapshot taken at `fn*` time: `(name, value)` pairs. -/
  public snapshot : List (String × MalVal)

end

/-- The eval monad: IO for builtins like `prn`, with `MalVal`-typed errors
so user-thrown values (from `throw`) can be caught structurally by `try*`. -/
public abbrev MalIO := ExceptT MalVal IO

/-- Auto-coerce `String` to `MalVal` so existing `throw (.str "...")` sites keep
working after the error channel switched from `String` to `MalVal`. -/
public instance : Coe String MalVal := ⟨MalVal.str⟩

/-- Mal's truthiness: only `nil` and `false` are falsy. Everything else
(including 0, the empty list, and the empty string) is truthy. -/
public def MalVal.isTruthy : MalVal → Bool
  | .nil        => false
  | .bool false => false
  | _ => true

/-- Structural equality on `MalVal`. Lists and vectors compare element-wise
and are equal across constructors; maps compare as unordered key-value sets;
atoms by identity (Nat id), so two `(atom 0)` calls produce non-equal values. -/
public partial def MalVal.equal : MalVal → MalVal → Bool
  | .nil,         .nil         => true
  | .bool a,      .bool b      => a == b
  | .int a,       .int b       => a == b
  | .sym a,       .sym b       => a == b
  | .str a,       .str b       => a == b
  | .kw a,        .kw b        => a == b
  | .atom a,      .atom b      => a == b
  | .list xs,     .list ys     => listEqual xs ys
  | .vec xs,      .vec ys      => listEqual xs ys
  | .list xs,     .vec ys      => listEqual xs ys
  | .vec xs,      .list ys     => listEqual xs ys
  | .map xs,      .map ys      => mapEqual xs ys
  | _,            _            => false
where
  listEqual : List MalVal → List MalVal → Bool
    | [],      []      => true
    | x :: xs, y :: ys => MalVal.equal x y && listEqual xs ys
    | _,       _       => false
  mapEqual (xs ys : List (MalVal × MalVal)) : Bool :=
    xs.length == ys.length
      && xs.all fun (k, v) =>
        match ys.find? (fun (k', _) => MalVal.equal k k') with
        | some (_, v') => MalVal.equal v v'
        | none         => false

/-- True if `v` is a sequence (list or vector). -/
public def MalVal.isSequential : MalVal → Bool
  | .list _ => true
  | .vec _  => true
  | _       => false

/-- Extract the underlying elements of a list or vector. -/
public def MalVal.toList? : MalVal → Option (List MalVal)
  | .list xs => some xs
  | .vec xs  => some xs
  | _        => none

/-- Public accessor: true if `l` is bound as a macro. The new module system
keeps structure field projections private even when fields are declared
`public`, so cross-module callers reach for this wrapper. -/
public def Lambda.isMacro? (l : Lambda) : Bool := l.isMacro

end Types
