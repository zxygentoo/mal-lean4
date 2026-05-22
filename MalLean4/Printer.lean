module

public import MalLean4.Types
open Types

namespace Printer

/-- Format a `MalVal` back to its mal surface syntax. Inverse of the reader,
except for `fn` values which the reader can't produce. -/
public def prStr : MalVal → String
  | .nil         => "nil"
  | .bool true   => "true"
  | .bool false  => "false"
  | .int n       => toString n
  | .sym s       => s
  | .str s       => "\"" ++ s ++ "\""
  | .list xs     => "(" ++ " ".intercalate (xs.map prStr) ++ ")"
  | .fn _        => "#<fn>"

end Printer
