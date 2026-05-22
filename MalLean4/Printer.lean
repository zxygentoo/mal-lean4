module

public import MalLean4.Types
open Types

namespace Printer

/-- Format a `MalVal` back to its mal surface syntax. Inverse of the reader. -/
public def prStr : MalVal → String
  | .int n   => toString n
  | .sym s   => s
  | .list xs => "(" ++ " ".intercalate (xs.map prStr) ++ ")"

end Printer
