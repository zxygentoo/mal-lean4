module

public import MalLean4.Types

open Types

/-- Backing storage for mal atoms.

Each `MalVal.atom n` indexes into this array. The slot holds an `IO.Ref` so
the atom's contents can change after creation — that's what makes atoms
*atoms* in mal/Clojure (explicit, user-visible mutable cells, in contrast
to mal's otherwise mostly-immutable values).

The mutation here is fundamentally different from the closure registry we
removed: closures *can* be pure data (we proved this with closure
conversion), so the registry was a workaround for kernel positivity. Atoms
*cannot* be pure data — mutation is part of their semantics. So one
`IO.Ref` registry is the right shape for them.
-/
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
