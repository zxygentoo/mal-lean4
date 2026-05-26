module

namespace Types

mutual

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
  -- The printer, equality, and type predicates strip this wrapper via
  -- `MalVal.strip`; only `meta`, `with-meta`, and `apply` see it.
  | withMeta : MalVal → MalVal → MalVal

public inductive Fn where
  | builtin : String → Fn
  | lambda  : Lambda → Fn

-- `outerEnvId` is a `Nat` id into `Env.store`, not a direct `Env`: Lean's
-- strict positivity rejects `Lambda { outerEnv : Env }` because `Env`
-- chains back through `MalVal`. The indirection also gives us lexical
-- scope and live `def!` updates that a value snapshot couldn't.
public structure Lambda where
  public mk ::
  public isMacro  : Bool := false
  public params   : List String
  public restParam : Option String := none
  public body     : MalVal
  public outerEnvId : Nat

end

-- `EIO MalVal` not `ExceptT MalVal IO`: one-layer error shape halves
-- per-bind dispatch cost. `MalVal`-typed errors let `try*` catch
-- user-thrown values structurally.
public abbrev MalIO := EIO MalVal

public instance : Coe String MalVal := ⟨MalVal.str⟩

public instance : MonadLift IO MalIO where
  monadLift m := EIO.adapt (fun e => MalVal.str s!"{e}") m

-- Only `nil` and `false` are falsy; 0, "", and `()` are truthy.
public def MalVal.isTruthy : MalVal → Bool
  | .nil        => false
  | .bool false => false
  | _ => true

-- Strips meta from both sides. Lists and vectors compare equal across
-- constructors; maps as unordered key-value sets; atoms by id.
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

public def MalVal.strip : MalVal → MalVal
  | .withMeta v _ => v.strip
  | v             => v

public def MalVal.getMeta : MalVal → MalVal
  | .withMeta _ m => m
  | _             => .nil

public def MalVal.isSequential : MalVal → Bool
  | .list _ => true
  | .vec _  => true
  | .withMeta v _ => v.isSequential
  | _       => false

public def MalVal.toList? : MalVal → Option (List MalVal)
  | .list xs       => some xs
  | .vec xs        => some xs
  | .withMeta v _  => v.toList?
  | _              => none

-- The new module system keeps structure field projections private even
-- when fields are declared `public`, so cross-module callers need these
-- wrappers.
public def Lambda.isMacro? (l : Lambda) : Bool := l.isMacro
public def Lambda.outerId (l : Lambda) : Nat := l.outerEnvId

-- Needed so partial list operations (`getLast!`, `head!`) type-check;
-- value irrelevant.
public instance : Inhabited MalVal := ⟨.nil⟩

-- Last-write-wins. Keeps map literals and `hash-map`/`assoc` results
-- free of duplicate keys.
public def MalVal.dedupMap (pairs : List (MalVal × MalVal)) :
    List (MalVal × MalVal) :=
  pairs.foldl (fun acc (k, v) =>
    if acc.any (fun (k', _) => MalVal.equal k k') then
      acc.map fun (k', v') => if MalVal.equal k k' then (k', v) else (k', v')
    else
      acc ++ [(k, v)]) []

end Types
