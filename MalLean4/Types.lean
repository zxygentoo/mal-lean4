module

set_option linter.missingDocs true

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
  /-- `withMeta value meta`: tags `value` with metadata. The printer, type
  predicates, equality, and most operations transparently strip this
  wrapper; only `meta` and `with-meta` see it. -/
  | withMeta : MalVal → MalVal → MalVal

/-- A callable: either a `builtin` (resolved by name via `Core.callBuiltin`)
or a `lambda` from `fn*` (see `Lambda`). -/
public inductive Fn where
  | builtin : String → Fn
  | lambda  : Lambda → Fn

/-- A user function created by `fn*`. The body resolves free names against
the env stored at `fn*` time (an external `Nat` id into `Env.store`), so
lookups follow lexical scope and `def!` updates in the closure's env
propagate to later calls — both impossible with a value snapshot. The
external table breaks `MalVal`'s strict-positivity cycle the same way
`Atoms.store` does for `MalVal.atom`. -/
public structure Lambda where
  public mk ::
  /-- True when bound via `defmacro!`; eval expands macro calls before
  applying. -/
  public isMacro  : Bool := false
  /-- Positional parameter names. -/
  public params   : List String
  /-- Optional rest-parameter name bound by `&` to a list of remaining args. -/
  public restParam : Option String := none
  /-- Unevaluated body form; `apply` evaluates this against a fresh frame
  whose outer chain leads to `outerEnvId`. -/
  public body     : MalVal
  /-- Id of the env at `fn*` time, looked up via `Env.lookup outerEnvId`. -/
  public outerEnvId : Nat

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

/-- Structural equality on `MalVal`. Strips meta wrappers from both sides.
Lists and vectors compare element-wise and are equal across constructors;
maps compare as unordered key-value sets; atoms by identity (Nat id), so
two `(atom 0)` calls produce non-equal values. -/
public partial def MalVal.equal (a b : MalVal) : Bool :=
  match a, b with
  | .withMeta v _, _ => MalVal.equal v b
  | _, .withMeta v _ => MalVal.equal a v
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

/-- Strip the outermost (`withMeta`) wrapper if present, otherwise return
`v` unchanged. Most operations call this before pattern-matching the value
so that metadata is invisible to them. -/
public def MalVal.strip : MalVal → MalVal
  | .withMeta v _ => v.strip
  | v             => v

/-- Return the metadata attached to `v`, or `nil` if none. -/
public def MalVal.getMeta : MalVal → MalVal
  | .withMeta _ m => m
  | _             => .nil

/-- True if `v` is a sequence (list or vector). -/
public def MalVal.isSequential : MalVal → Bool
  | .list _ => true
  | .vec _  => true
  | .withMeta v _ => v.isSequential
  | _       => false

/-- Extract the underlying elements of a list or vector. -/
public def MalVal.toList? : MalVal → Option (List MalVal)
  | .list xs       => some xs
  | .vec xs        => some xs
  | .withMeta v _  => v.toList?
  | _              => none

/-- Public accessor: true if `l` is bound as a macro. The new module system
keeps structure field projections private even when fields are declared
`public`, so cross-module callers reach for this wrapper. -/
public def Lambda.isMacro? (l : Lambda) : Bool := l.isMacro

/-- Public accessor: id of the env captured at `fn*` time. -/
public def Lambda.outerId (l : Lambda) : Nat := l.outerEnvId

/-- A default `MalVal` so partial list operations (`getLast!`, `head!`) can
type-check. The contents are irrelevant — these operations are only called
on lists we've already checked to be non-empty. -/
public instance : Inhabited MalVal := ⟨.nil⟩

/-- Deduplicate hash-map entries, last-write-wins. Used to keep map literals
and `hash-map`/`assoc` results free of duplicate keys. -/
public def MalVal.dedupMap (pairs : List (MalVal × MalVal)) :
    List (MalVal × MalVal) :=
  pairs.foldl (fun acc (k, v) =>
    if acc.any (fun (k', _) => MalVal.equal k k') then
      acc.map fun (k', v') => if MalVal.equal k k' then (k', v) else (k', v')
    else
      acc ++ [(k, v)]) []

end Types
