module

public import MalLean4.Types
public import MalLean4.Atoms

open Types

namespace Printer

/-- Re-escape mal's string-literal escapes for output (readable form).
Inverse of the reader's `unescape`. -/
private def escapeStr (s : String) : String :=
  s.toList.foldl
    (fun acc c =>
      acc ++ (match c with
        | '\\' => "\\\\"
        | '"'  => "\\\""
        | '\n' => "\\n"
        | c    => String.singleton c))
    ""

/-- Format a `MalVal` to its mal surface syntax. In `IO` so `.atom` can
deref its cell — atoms render as `(atom <current-contents>)`. -/
public partial def prStr : MalVal → IO String
  | .nil         => return "nil"
  | .bool true   => return "true"
  | .bool false  => return "false"
  | .int n       => return (toString n)
  | .sym s       => return s
  | .str s       => return "\"" ++ escapeStr s ++ "\""
  | .list xs     => do
    let strs ← xs.mapM prStr
    return "(" ++ " ".intercalate strs ++ ")"
  | .fn _        => return "#<fn>"
  | .atom n      => do
    match ← Atoms.deref n with
    | some v => return s!"(atom {← prStr v})"
    | none   => return s!"(atom #invalid:{n})"

end Printer
