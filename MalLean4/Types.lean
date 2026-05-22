module

namespace Types

/-- The mal abstract syntax tree.

Every value the interpreter manipulates — read from input, produced by `EVAL`,
formatted by the printer — is one of these constructors.

`builtin` tags a function by name; the actual Lean implementation is looked
up by `Core.apply`. Storing functions directly would put `MalVal` in a
negative position under a `→` and fail strict positivity.
-/
public inductive MalVal where
  | int     : Int → MalVal
  | sym     : String → MalVal
  | list    : List MalVal → MalVal
  | builtin : String → MalVal

/-- The shape of a mal builtin: receive a list of already-evaluated arguments
and return either a result value or an error message. -/
public abbrev MalFn := List MalVal → Except String MalVal

end Types
