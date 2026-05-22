module

public import MalLean4.Types

open Types

/-- The function table backing `MalVal.fn`. Registered `MalFn`s live here
indexed by `Fn.id`; `Fn.apply` looks one up and invokes it.

This indirection exists because Lean's strict positivity check forbids a
`MalFn → MalVal` constructor (the function's argument list mentions
`MalVal`, putting it under a `→` and tripping positivity). Storing a `Nat`
handle and looking up the actual `MalFn` here sidesteps the check while
preserving first-class semantics — closures capture by registering a fresh
Lean closure, builtins register at startup, and both are dispatched
identically via `Fn.apply` (or the `CoeFun` syntax `f args`).
-/
private initialize registry : IO.Ref (Array MalFn) ← IO.mkRef #[]

namespace Types.Fn

/-- Register a callable and return its `Fn` handle. Used by `Core.initialEnv`
for builtins and by `fn*` evaluation for user-defined closures. -/
public def register (impl : MalFn) : IO Fn := do
  let arr ← registry.get
  registry.set (arr.push impl)
  return ⟨arr.size⟩

/-- Invoke the callable behind an `Fn` handle. Errors if the handle is
unknown, which shouldn't happen for ids produced by `Fn.register`. -/
public def apply (f : Fn) (args : List MalVal) : MalIO MalVal := do
  let arr ← registry.get
  match arr[f.id]? with
  | some impl => impl args
  | none      => throw s!"invalid Fn handle #{f.id}"

end Types.Fn
