module

namespace Types

/-- The mal abstract syntax tree.

Every value the interpreter manipulates — read from input, produced by `EVAL`,
formatted by the printer — is one of these constructors.
-/
public inductive MalVal where
  | int  : Int → MalVal
  | sym  : String → MalVal
  | list : List MalVal → MalVal

/-- The shape of a mal builtin: receive a list of already-evaluated arguments
and return either a result value or an error message. -/
public abbrev MalFn := List MalVal → Except String MalVal

end Types
