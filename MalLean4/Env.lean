module

public import MalLean4.Types
open Types

/-- A mal evaluation environment: a chain of frames mapping symbol names to
their bound values.

Immutable. `def!` creates a new env with the updated current frame; `let*`
adds a child frame whose `outer` points at its parent. The outermost frame
(the one with `outer = none`) is the "top env" by convention; this lets us
distinguish "local names a closure can snapshot at `fn*` time" from
"top-level names that should be looked up at call time" without an extra
flag.
-/
public structure Env where
  current : List (String × MalVal)
  outer   : Option Env

namespace Env

/-- A root environment with no bindings. -/
public def empty : Env := ⟨[], none⟩

/-- A child env whose lookups fall through to `parent`. -/
public def child (parent : Env) : Env := ⟨[], some parent⟩

/-- Bind `k` to `v` in the innermost frame (shadows any outer binding). -/
public def set (env : Env) (k : String) (v : MalVal) : Env :=
  { env with current := (k, v) :: env.current }

/-- Look up `k` walking the entire chain. -/
public partial def find? (env : Env) (k : String) : Option MalVal :=
  match env.current.find? (·.1 == k) with
  | some (_, v) => some v
  | none =>
    match env.outer with
    | some o => find? o k
    | none   => none

/-- Look up `k` walking only *local* frames, stopping before the top frame
(the one with `outer = none`). Used at `fn*` time to decide which free
variables to snapshot into the closure's captures and which to defer to
call-time lookup. -/
public partial def findLocal? (env : Env) (k : String) : Option MalVal :=
  match env.outer with
  | none   => none
  | some o =>
    match env.current.find? (·.1 == k) with
    | some (_, v) => some v
    | none        => findLocal? o k

/-- The outermost frame (the one with `outer = none`). For `(eval …)` and
`(load-file …)` — they evaluate in the top env regardless of where they're
called from. -/
public partial def top (env : Env) : Env :=
  match env.outer with
  | none   => env
  | some o => o.top

/-- Rebuild `env`'s chain with `newTop` substituted for the outermost frame.
Used to propagate `def!` updates that happen *inside* `(eval …)` back up
through nested scopes, so subsequent expressions see them. -/
public partial def replaceTop (env : Env) (newTop : Env) : Env :=
  match env.outer with
  | none   => newTop
  | some o => { env with outer := some (o.replaceTop newTop) }

end Env
