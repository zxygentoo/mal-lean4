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
would break strict positivity, same shape as `Atoms.store`). Entries
become `none` after `GC.run` collects them. -/
public initialize store : IO.Ref (Array (Option Env)) ← IO.mkRef #[]

/-- Registrations since the last `GC.run`. Incremented by `register`,
reset by the GC after each sweep. `GC.maybeRun`'s hot-path check is just
a `Nat` read + compare; nothing reads the bigger `store` array unless we
actually sweep. -/
public initialize sinceLastSweep : IO.Ref Nat ← IO.mkRef 0

/-- Stash `env` in the registry and return its handle. -/
public def register (env : Env) : IO Nat := do
  let arr ← store.get
  store.set (arr.push (some env))
  sinceLastSweep.modify (· + 1)
  return arr.size

/-- Look up the env at `id`. Panics if the id was either never registered
or was swept by `GC.run`; reaching either case means a `Lambda` outlived a
reference the GC didn't see, which is a bug. -/
public partial def lookup (id : Nat) : IO Env := do
  let arr ← store.get
  match arr[id]? with
  | some (some env) => return env
  | some none       => panic! s!"Env.lookup: id {id} was garbage collected"
  | none            => panic! s!"Env.lookup: invalid id {id} (table size {arr.size})"

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
