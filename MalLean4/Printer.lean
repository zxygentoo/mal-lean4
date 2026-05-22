module

public import MalLean4.Types
open Types

namespace Printer

/-- Format a `MalVal` back to its mal surface syntax. Inverse of the reader,
except for builtins which the reader can't produce. -/
public def prStr : MalVal → String
  | .int n       => toString n
  | .sym s       => s
  | .list xs     => "(" ++ " ".intercalate (xs.map prStr) ++ ")"
  | .builtin _   => "#<fn>"

end Printer
