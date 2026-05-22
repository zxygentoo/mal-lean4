module

public import MalLean4.Types
open Types

/-- The mal evaluation environment: a chain of frames mapping symbol names to
their bound values.

`let*` extends an env with a child frame; lookup walks outward to the parent
on miss. Bindings are stored in the innermost frame and shadow any outer
binding of the same name.
-/
public inductive Env where
  | mk (outer : Option Env) (data : List (String × MalVal))

namespace Env

/-- The empty (root) environment. -/
public def empty : Env := .mk none []

/-- Create a child env whose lookups fall through to `parent` on miss. -/
public def child (parent : Env) : Env := .mk (some parent) []

/-- Bind `name` to `v` in the innermost frame, shadowing any outer binding. -/
public def set : Env → String → MalVal → Env
  | .mk o d, k, v => .mk o ((k, v) :: d)

/-- Look up `name`, walking parent frames on miss. -/
public def find? : Env → String → Option MalVal
  | .mk none d, k     => d.find? (·.1 == k) |>.map (·.2)
  | .mk (some o) d, k =>
    match d.find? (·.1 == k) with
    | some (_, v) => some v
    | none        => o.find? k

end Env
