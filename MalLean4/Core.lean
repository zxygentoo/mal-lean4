module

public import MalLean4.Types
public import MalLean4.Env
open Types

namespace Core

def intBinop (op : Int → Int → Int) : MalFn
  | [.int a, .int b] => .ok (.int (op a b))
  | _                => .error "expected two integers"

/-- The starting environment for the mal REPL.

Contains the four arithmetic builtins `+`, `-`, `*`, `/` over integers.
Each is a two-argument function that errors on any other argument shape.
-/
public def initialEnv : Env :=
  [ ("+", intBinop (· + ·)),
    ("-", intBinop (· - ·)),
    ("*", intBinop (· * ·)),
    ("/", intBinop (· / ·)) ]

end Core
