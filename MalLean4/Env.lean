module

public import MalLean4.Types
public import Std.Data.HashMap.Basic

open Types

/-- The mal evaluation environment: a chain of frames mapping symbol names
to their bound values.

The innermost frame is mutable (an `IO.Ref` to a `Std.HashMap`); the outer
pointer is plain and never changes. Mutation is required so that closures
which capture an env later observe `def!`s into that env — see step 4 of
the mal guide.
-/
public structure Env where
  current : IO.Ref (Std.HashMap String MalVal)
  outer   : Option Env

namespace Env

/-- A fresh root environment with no bindings. -/
public def empty : IO Env := do
  let r ← IO.mkRef ∅
  return { current := r, outer := none }

/-- A fresh child env whose lookups fall through to `parent` on miss. -/
public def child (parent : Env) : IO Env := do
  let r ← IO.mkRef ∅
  return { current := r, outer := some parent }

/-- Bind `k` to `v` in the innermost frame. Shadows any outer binding. -/
public def set (env : Env) (k : String) (v : MalVal) : IO Unit :=
  env.current.modify (·.insert k v)

/-- Look up `k`, walking parent frames on miss. -/
public partial def find? (env : Env) (k : String) : IO (Option MalVal) := do
  let data ← env.current.get
  match data[k]? with
  | some v => return some v
  | none =>
    match env.outer with
    | some p => p.find? k
    | none   => return none

end Env
