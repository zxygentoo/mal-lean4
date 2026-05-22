module

public import MalLean4.Types

open Types

/-- Backing storage for mal atoms. `MalVal.atom n` indexes into this array;
each slot is an `IO.Ref` so the atom's contents are user-mutable via
`reset!` / `swap!`. -/
private initialize store : IO.Ref (Array (IO.Ref MalVal)) ← IO.mkRef #[]

namespace Atoms

/-- Allocate a fresh atom holding `v`, return its index. -/
public def new (v : MalVal) : IO Nat := do
  let cell ← IO.mkRef v
  let arr ← store.get
  store.set (arr.push cell)
  return arr.size

/-- Read the current contents of atom `n`. -/
public def deref (n : Nat) : IO (Option MalVal) := do
  let arr ← store.get
  match arr[n]? with
  | some cell => some <$> cell.get
  | none      => return none

/-- Replace the contents of atom `n` with `v`. Returns `v` on success. -/
public def reset (n : Nat) (v : MalVal) : IO (Option MalVal) := do
  let arr ← store.get
  match arr[n]? with
  | some cell => do cell.set v; return some v
  | none      => return none

end Atoms
