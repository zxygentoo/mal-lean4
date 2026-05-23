module

public import MalLean4.Types
public import MalLean4.Atoms

open Types

namespace Printer

/-- Re-escape mal's string-literal escapes for output (readable form).
Inverse of the reader's `unescape`. -/
def escapeStr (s : String) : String :=
  s.toList.foldl
    (fun acc c =>
      acc ++ (match c with
        | '\\' => "\\\\"
        | '"'  => "\\\""
        | '\n' => "\\n"
        | c    => String.singleton c))
    ""

/-- Core formatter parameterized by string-rendering mode. With `readably`
true, strings are quoted and escaped (round-trip form); with false, they
render as raw contents. Non-string values render identically either way. -/
partial def prStrAux (readably : Bool) : MalVal → IO String
  | .nil          => return "nil"
  | .bool true    => return "true"
  | .bool false   => return "false"
  | .int n        => return (toString n)
  | .sym s        => return s
  | .kw s         => return s!":{s}"
  | .str s        => return (if readably then "\"" ++ escapeStr s ++ "\"" else s)
  | .list xs      => do
    let strs ← xs.mapM (prStrAux readably)
    return "(" ++ " ".intercalate strs ++ ")"
  | .vec xs       => do
    let strs ← xs.mapM (prStrAux readably)
    return "[" ++ " ".intercalate strs ++ "]"
  | .map pairs    => do
    let parts ← pairs.mapM fun (k, v) => do
      let ks ← prStrAux readably k
      let vs ← prStrAux readably v
      return s!"{ks} {vs}"
    return "{" ++ " ".intercalate parts ++ "}"
  | .fn _         => return "#<fn>"
  | .atom n       => do
    match ← Atoms.deref n with
    | some v => return s!"(atom {← prStrAux readably v})"
    | none   => return s!"(atom #invalid:{n})"
  | .withMeta v _ => prStrAux readably v

/-- Readable rendering: strings quoted+escaped. Used by `pr-str`/`prn` and
the REPL's printed output. -/
public def prStr : MalVal → IO String := prStrAux true

/-- Unreadable rendering: strings as raw contents. Used by `str`/`println`. -/
public def prStrUnreadably : MalVal → IO String := prStrAux false

end Printer
