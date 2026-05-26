module

public import MalLean4.Types

set_option linter.missingDocs true

open Types

namespace Atoms

/-- Backing storage for mal atoms. `MalVal.atom n` indexes into this array;
each slot is an `IO.Ref` so the atom's contents are user-mutable via
`reset!` / `swap!`. Entries become `none` after `GC.run` collects them. -/
public initialize store : IO.Ref (Array (Option (IO.Ref MalVal))) ← IO.mkRef #[]

/-- Allocate a fresh atom holding `v`, return its index. -/
public def new (v : MalVal) : IO Nat := do
  let cell ← IO.mkRef v
  let arr ← store.get
  store.set (arr.push (some cell))
  return arr.size

/-- Read the current contents of atom `n`. Returns `none` if the slot was
swept by `GC.run` or the id is out of range. -/
public def deref (n : Nat) : IO (Option MalVal) := do
  let arr ← store.get
  match arr[n]? with
  | some (some cell) => some <$> cell.get
  | _                => return none

/-- Replace the contents of atom `n` with `v`. Returns `v` on success,
`none` if the slot has been collected or the id is out of range. -/
public def reset (n : Nat) (v : MalVal) : IO (Option MalVal) := do
  let arr ← store.get
  match arr[n]? with
  | some (some cell) => do cell.set v; return some v
  | _                => return none

end Atoms
