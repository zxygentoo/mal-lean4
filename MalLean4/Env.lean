module

public import MalLean4.Types
public import Std.Data.HashMap.Basic

open Types

/-- A mal evaluation environment: a chain of frames, each frame holding a
mutable `HashMap` of bindings.

This mirrors the OCaml impl's `{ current : t M.t ref; outer : env option }`
shape. Mutability is via `IO.Ref`, which lets `def!` update bindings
in-place and propagates `(eval (def! …))` to the top env through the shared
ref without `replaceTop` plumbing.

Closures still don't store an `Env` — they store snapshots (see `Fn.lambda`
captures), so the cycle that would otherwise trip Lean's RC never forms.
That's where the GC property of the closure-conversion design lives; the
env being mutable is orthogonal.
-/
public structure Env where
  current : IO.Ref (Std.HashMap String MalVal)
  outer   : Option Env

namespace Env

/-- A root environment with no bindings. -/
public def empty : IO Env := do
  let r ← IO.mkRef ∅
  return { current := r, outer := none }

/-- A new nested env whose lookups fall through to `parent`. Called at
every `let*` and lambda apply to introduce a fresh binding frame. -/
public def new (parent : Env) : IO Env := do
  let r ← IO.mkRef ∅
  return { current := r, outer := some parent }

/-- Bind `k` to `v` in the innermost frame (shadows any outer binding). -/
public def set (env : Env) (k : String) (v : MalVal) : IO Unit :=
  env.current.modify (·.insert k v)

/-- Look up `k` walking the entire chain. -/
public partial def find? (env : Env) (k : String) : IO (Option MalVal) := do
  let data ← env.current.get
  match data[k]? with
  | some v => return some v
  | none =>
    match env.outer with
    | some o => o.find? k
    | none   => return none

/-- Look up `k` walking only *local* frames, stopping before the top frame
(the one with `outer = none`). Used at `fn*` time to decide which free
variables to snapshot into the closure's captures and which to defer to
call-time lookup. -/
public partial def findLocal? (env : Env) (k : String) : IO (Option MalVal) := do
  match env.outer with
  | none   => return none
  | some o =>
    let data ← env.current.get
    match data[k]? with
    | some v => return some v
    | none   => o.findLocal? k

/-- The root frame (the one with `outer = none`). For `(eval …)` and
`(load-file …)` — they evaluate in the root env regardless of where
they're called from. Pure walk; the env at the end is the same
`IO.Ref`-backed frame the rest of the chain points at, so mutations are
visible. -/
public partial def root (env : Env) : Env :=
  match env.outer with
  | none   => env
  | some o => o.root

end Env
