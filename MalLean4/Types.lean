module

namespace Types

/-- The eval monad: IO so builtins like `prn` can print, with String-typed
errors via `ExceptT`.

We pick `ExceptT String IO` over `EIO String` (Lean's native "IO with typed
error") because `IO` actions auto-lift in cleanly here — the underlying
`IO.Error` channel is orthogonal to our `String` error channel. With
`EIO String`, every call to `IO.println`/`stdin.getLine`/etc. would need an
explicit `IO.Error → String` mapping at the boundary.
-/
public abbrev MalIO := ExceptT String IO

/-- A handle to a callable registered with `Fn.register` (see `Fn.lean`).

We'd write `fn : MalFn → MalVal` directly if Lean's strict positivity check
allowed it (it doesn't — `MalVal` would appear under a `→` and the kernel
rejects the inductive). The `Nat` id indirects through a process-wide
registry; users interact via `Fn.register`/`Fn.apply` and a `CoeFun`
instance, so the id is an implementation detail.
-/
public structure Fn where
  id : Nat

/-- The mal abstract syntax tree.

Every value the interpreter manipulates — read from input, produced by
`eval`, formatted by the printer — is one of these constructors. Functions
(builtins and user-defined `fn*` closures alike) share the single `fn`
constructor.
-/
public inductive MalVal where
  | nil
  | bool : Bool → MalVal
  | int  : Int → MalVal
  | sym  : String → MalVal
  | str  : String → MalVal
  | list : List MalVal → MalVal
  | fn   : Fn → MalVal

/-- The shape of a mal callable: receive already-evaluated arguments and
return a result (or an error) in `MalIO`. -/
public abbrev MalFn := List MalVal → MalIO MalVal

end Types
