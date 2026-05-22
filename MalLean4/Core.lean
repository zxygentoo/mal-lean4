module

public import MalLean4.Types
public import MalLean4.Env
open Types

namespace Core

private def intBinop (op : Int → Int → Int) : MalFn
  | [.int a, .int b] => .ok (.int (op a b))
  | _                => .error "expected two integers"

private def builtins : List (String × MalFn) :=
  [ ("+", intBinop (· + ·)),
    ("-", intBinop (· - ·)),
    ("*", intBinop (· * ·)),
    ("/", intBinop (· / ·)) ]

/-- The starting environment for the mal REPL.

Contains the four arithmetic builtins `+`, `-`, `*`, `/` over integers, each
bound as a `MalVal.builtin` tag that `apply` resolves to its Lean
implementation.
-/
public def initialEnv : Env :=
  builtins.foldl (fun env (name, _) => env.set name (.builtin name)) Env.empty

/-- Apply a callable `MalVal` to its already-evaluated arguments. -/
public def apply : MalVal → List MalVal → Except String MalVal
  | .builtin name, args =>
    match builtins.find? (·.1 == name) with
    | some (_, f) => f args
    | none        => .error s!"unknown builtin '{name}'"
  | _, _ => .error "first item in list is not callable"

end Core
