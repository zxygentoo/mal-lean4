module

public import MalLean4.Types
public import Std.Data.HashMap.Basic

open Types

-- A chain of frames, each holding a mutable `HashMap`. `def!` updates
-- the innermost frame in place. `idRef` is set once the env is
-- `register`-ed so `GC.markEnv` can mark its slot reachable; transient
-- envs from `Env.new` never captured by a `fn*` stay `none`.
public structure Env where
  current : IO.Ref (Std.HashMap String MalVal)
  outer   : Option Env
  idRef   : IO.Ref (Option Nat)

namespace Env

-- `Lambda.outerEnvId` indexes here instead of holding an `Env`
-- directly — same strict-positivity workaround as `Atoms.store`.
-- Entries become `none` after `GC.run` collects them.
public initialize store : IO.Ref (Array (Option Env)) ← IO.mkRef #[]

public initialize lastSweepSize : IO.Ref Nat ← IO.mkRef 0

-- Set by `register` once we've accumulated more than `threshold` new
-- entries since `lastSweepSize`; cleared by `GC.run`. Keeps
-- `maybeRun`'s hot path to a single `Bool` read.
public initialize shouldSweep : IO.Ref Bool ← IO.mkRef false

public def threshold : Nat := 1000

-- One-way flag: `true` once anything has ever bound `DEBUG-EVAL`. While
-- `false`, `Debug.trace` skips the env walk entirely — an O(depth) win
-- on every `evalLoop` iteration in benchmark code that never trips the
-- hook. Never cleared: the env walk takes over and correctly returns
-- `none` for an out-of-scope `DEBUG-EVAL` binding.
public initialize debugEvalMaybeBound : IO.Ref Bool ← IO.mkRef false

-- Files `env` in the registry, writes the id into `env.idRef` (so
-- `GC.markEnv` can mark the slot reachable), and trips `shouldSweep`
-- once per cycle when the threshold is crossed.
public def register (env : Env) : IO Nat := do
  let arr ← store.get
  let id := arr.size
  env.idRef.set (some id)
  store.set (arr.push (some env))
  if id + 1 - (← lastSweepSize.get) > threshold then
    shouldSweep.set true
  return id

-- Panics if the id was never registered or was swept — either means a
-- `Lambda` outlived a reference the GC didn't see, which is a bug.
public partial def lookup (id : Nat) : IO Env := do
  let arr ← store.get
  match arr[id]? with
  | some (some env) => return env
  | some none       => panic! s!"Env.lookup: id {id} was garbage collected"
  | none            => panic! s!"Env.lookup: invalid id {id} (table size {arr.size})"

public def empty : IO Env := do
  let r ← IO.mkRef ∅
  let i ← IO.mkRef none
  return { current := r, outer := none, idRef := i }

public def new (parent : Env) : IO Env := do
  let r ← IO.mkRef ∅
  let i ← IO.mkRef none
  return { current := r, outer := some parent, idRef := i }

-- Seeds the frame in one ref allocation instead of the N `current.modify`
-- calls a fresh `Env.new` + repeated `set` would cost. Used by
-- `bindLambdaArgs`. Same `DEBUG-EVAL` flag invariant as `set`.
public def newWithBindings (parent : Env)
    (bindings : Std.HashMap String MalVal) : IO Env := do
  let r ← IO.mkRef bindings
  let i ← IO.mkRef none
  if bindings.contains "DEBUG-EVAL" then debugEvalMaybeBound.set true
  return { current := r, outer := some parent, idRef := i }

-- Trips `debugEvalMaybeBound` on `DEBUG-EVAL` so `Debug.trace` switches
-- off its fast-path skip.
public def set (env : Env) (k : String) (v : MalVal) : IO Unit := do
  env.current.modify (·.insert k v)
  if k == "DEBUG-EVAL" then debugEvalMaybeBound.set true

public partial def find? (env : Env) (k : String) : IO (Option MalVal) := do
  let data ← env.current.get
  match data[k]? with
  | some v => return some v
  | none   =>
    match env.outer with
    | some o => o.find? k
    | none   => return none

public partial def root (env : Env) : Env :=
  match env.outer with
  | none   => env
  | some o => o.root

end Env
