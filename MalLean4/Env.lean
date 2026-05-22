module

public import MalLean4.Types
public import Std.Data.HashMap.Basic

open Types

/-- A mal evaluation environment: a chain of frames, each holding a mutable
`HashMap` of bindings. `def!` updates the innermost frame in place via the
`IO.Ref`; closures don't store an `Env` directly (they snapshot — see
`Fn.lambda`), so no env/closure cycle ever forms. -/
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

/-- Look up `k` walking only *local* frames (stops before the root). Used
at `fn*` time to pick which free variables to snapshot into the closure
vs. defer to call-time lookup. -/
public partial def findLocal? (env : Env) (k : String) : IO (Option MalVal) := do
  match env.outer with
  | none   => return none
  | some o =>
    let data ← env.current.get
    match data[k]? with
    | some v => return some v
    | none   => o.findLocal? k

/-- The root frame (`outer = none`). `(eval …)` and `(load-file …)` use
this to evaluate in the root env regardless of call site. -/
public partial def root (env : Env) : Env :=
  match env.outer with
  | none   => env
  | some o => o.root

end Env
