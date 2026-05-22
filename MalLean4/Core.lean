module

public import MalLean4.Types
public import MalLean4.Env
public import MalLean4.Fn
import MalLean4.Printer

open Types

namespace Core

/-- Structural equality on `MalVal`. Lists compare element-wise; functions
compare by handle id; mixed-type comparisons return `false`. -/
public partial def malEqual : MalVal → MalVal → Bool
  | .nil,         .nil         => true
  | .bool a,      .bool b      => a == b
  | .int a,       .int b       => a == b
  | .sym a,       .sym b       => a == b
  | .str a,       .str b       => a == b
  | .fn ⟨a⟩,      .fn ⟨b⟩      => a == b
  | .list xs,     .list ys     => listEqual xs ys
  | _,            _            => false
where
  listEqual : List MalVal → List MalVal → Bool
    | [],      []      => true
    | x :: xs, y :: ys => malEqual x y && listEqual xs ys
    | _,       _       => false

private def intBinop (op : Int → Int → Int) : MalFn
  | [.int a, .int b] => return .int (op a b)
  | _                => throw "expected two integers"

private def compOp (op : Int → Int → Bool) : MalFn
  | [.int a, .int b] => return .bool (op a b)
  | _                => throw "expected two integers"

private def eqOp : MalFn
  | [a, b] => return .bool (malEqual a b)
  | _      => throw "=: expected two arguments"

private def listOp : MalFn := fun args => return .list args

private def listQ : MalFn
  | [.list _] => return .bool true
  | [_]       => return .bool false
  | _         => throw "list?: expected one argument"

private def emptyQ : MalFn
  | [.list xs] => return .bool xs.isEmpty
  | [_]        => return .bool false
  | _          => throw "empty?: expected one argument"

private def countOp : MalFn
  | [.list xs] => return .int xs.length
  | [_]        => return .int 0
  | _          => throw "count: expected one argument"

private def prn : MalFn := fun args => do
  IO.println (" ".intercalate (args.map Printer.prStr))
  return .nil

private def builtins : List (String × MalFn) :=
  [ ("+",  intBinop (· + ·)),
    ("-",  intBinop (· - ·)),
    ("*",  intBinop (· * ·)),
    ("/",  intBinop (· / ·)),
    ("<",  compOp (· < ·)),
    ("<=", compOp (· ≤ ·)),
    (">",  compOp (· > ·)),
    (">=", compOp (· ≥ ·)),
    ("=",  eqOp),
    ("list",   listOp),
    ("list?",  listQ),
    ("empty?", emptyQ),
    ("count",  countOp),
    ("prn",    prn) ]

/-- The starting environment for the mal REPL.

Each builtin is registered as a `Fn` and bound by name. Builtins and
user-defined closures share the single `MalVal.fn` representation, so
`apply` is one dispatch in the evaluator.
-/
public def initialEnv : IO Env := do
  let env ← Env.empty
  for (name, impl) in builtins do
    let f ← Fn.register impl
    env.set name (.fn f)
  return env

end Core
