module

public import MalLean4.Types
public import Std.Data.HashMap.Basic

set_option linter.missingDocs true

open Types

/-- A mal evaluation environment: a chain of frames, each holding a mutable
`HashMap` of bindings. `def!` updates the innermost frame in place via the
`IO.Ref`. `idRef` is set to `some n` once the env is `register`-ed (so
`GC.markEnv` can mark `n` as reachable when it walks the env); transient
envs created by `Env.new` and never captured by a `fn*` keep it as
`none`. -/
public structure Env where
  current : IO.Ref (Std.HashMap String MalVal)
  outer   : Option Env
  idRef   : IO.Ref (Option Nat)

namespace Env

/-- Backing store for env handles. `Lambda.outerEnvId` indexes into this
table so the env reference doesn't appear directly inside `MalVal` (which
would break strict positivity, same shape as `Atoms.store`). Entries
become `none` after `GC.run` collects them. -/
public initialize store : IO.Ref (Array (Option Env)) ← IO.mkRef #[]

/-- `store.size` at the most recent sweep. -/
public initialize lastSweepSize : IO.Ref Nat ← IO.mkRef 0

/-- Set to `true` when `register` notices we've accumulated more than
`threshold` new entries since `lastSweepSize`; cleared after `GC.run`.
`maybeRun`'s hot path is just a `Bool` read. -/
public initialize shouldSweep : IO.Ref Bool ← IO.mkRef false

/-- Number of new `store` entries between automatic sweeps. -/
public def threshold : Nat := 1000

/-- Stash `env` in the registry and return its handle. Also writes the
assigned id into `env.idRef` so `GC.markEnv` can mark the slot reachable
when it walks `env` (or any env that chains to it). The post-push
delta-vs-`lastSweepSize` check sets `shouldSweep` once per cycle; most
registrations are a read + compare, no write. -/
public def register (env : Env) : IO Nat := do
  let arr ← store.get
  let id := arr.size
  env.idRef.set (some id)
  store.set (arr.push (some env))
  if id + 1 - (← lastSweepSize.get) > threshold then
    shouldSweep.set true
  return id

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
  let i ← IO.mkRef none
  return { current := r, outer := none, idRef := i }

/-- A new nested env whose lookups fall through to `parent`. Called at
every `let*` and lambda apply to introduce a fresh binding frame. -/
public def new (parent : Env) : IO Env := do
  let r ← IO.mkRef ∅
  let i ← IO.mkRef none
  return { current := r, outer := some parent, idRef := i }

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
