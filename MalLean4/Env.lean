module

public import MalLean4.Types
open Types

/-- The mal evaluation environment: an associative list mapping symbol names
to their bound functions.

Step 3 will introduce nested scopes and bindings for non-function values; for
step 2 a flat list of builtins suffices.
-/
public abbrev Env := List (String × MalFn)

namespace Env

def empty : Env := []

/-- Look up `name` in the environment, returning its bound function if any. -/
public def get? (env : Env) (name : String) : Option MalFn :=
  env.find? (·.1 == name) |>.map (·.2)

def set (env : Env) (name : String) (f : MalFn) : Env :=
  (name, f) :: env

end Env
