module

public import MalLean4.Types
public import Std.Data.HashMap.Basic

open Types

/-- A mal evaluation environment: a chain of frames, each holding a mutable
`HashMap` of bindings. `def!` updates the innermost frame in place via the
`IO.Ref`. -/
public structure Env where
  current : IO.Ref (Std.HashMap String MalVal)
  outer   : Option Env

namespace Env

/-- Backing store for env handles. `Lambda.outerEnvId` indexes into this
table so the env reference doesn't appear directly inside `MalVal` (which
would break strict positivity, same shape as `Atoms.store`). -/
initialize store : IO.Ref (Array Env) ← IO.mkRef #[]

/-- Stash `env` in the registry and return its handle. -/
public def register (env : Env) : IO Nat := do
  let arr ← store.get
  store.set (arr.push env)
  return arr.size

/-- Look up the env at `id`. Errors with a clear panic if the id is unknown
— this can only happen if a `Lambda` outlives its registry slot, which the
current implementation never does (the registry grows monotonically). -/
public partial def lookup (id : Nat) : IO Env := do
  let arr ← store.get
  match arr[id]? with
  | some env => return env
  | none     => panic! s!"Env.lookup: invalid id {id} (table size {arr.size})"

/-- A root environment with no bindings. -/
public def empty : IO Env := do
  let r ← IO.mkRef ∅
  return { current := r, outer := none }

/-- A new nested env whose lookups fall through to `parent`. Called at
every `let*` and lambda apply to introduce a fresh binding frame. -/
public def new (parent : Env) : IO Env := do
  let r ← IO.mkRef ∅
  return { current := r, outer := some parent }

/-- Bind `k` to `v` in the innermost frame (shadows any outer binding). -/
public def set (env : Env) (k : String) (v : MalVal) : IO Unit :=
  env.current.modify (·.insert k v)

/-- Look up `k` walking the entire chain. -/
public partial def find? (env : Env) (k : String) : IO (Option MalVal) := do
  let data ← env.current.get
  match data[k]? with
  | some v => return some v
  | none   =>
    match env.outer with
    | some o => o.find? k
    | none   => return none

/-- The root frame (`outer = none`). `(eval …)` and `(load-file …)` use
this to evaluate in the root env regardless of call site. -/
public partial def root (env : Env) : Env :=
  match env.outer with
  | none   => env
  | some o => o.root

end Env
