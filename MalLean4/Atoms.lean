module

public import MalLean4.Types

open Types

namespace Atoms

-- `MalVal.atom n` indexes here; each slot is an `IO.Ref` so atom
-- contents are user-mutable via `reset!`/`swap!`. The indirection
-- works around strict positivity (an `IO.Ref MalVal` inside `MalVal`
-- isn't allowed). Entries become `none` after `GC.run`.
public initialize store : IO.Ref (Array (Option (IO.Ref MalVal))) ← IO.mkRef #[]

public def new (v : MalVal) : IO Nat := do
  let cell ← IO.mkRef v
  let arr ← store.get
  store.set (arr.push (some cell))
  return arr.size

public def deref (n : Nat) : IO (Option MalVal) := do
  let arr ← store.get
  match arr[n]? with
  | some (some cell) => some <$> cell.get
  | _                => return none

public def reset (n : Nat) (v : MalVal) : IO (Option MalVal) := do
  let arr ← store.get
  match arr[n]? with
  | some (some cell) => do cell.set v; return some v
  | _                => return none

end Atoms
