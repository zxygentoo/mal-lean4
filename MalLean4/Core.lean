module

public import MalLean4.Types
public import MalLean4.Env
public import MalLean4.Atoms
import MalLean4.Printer
import MalLean4.Reader

open Types

namespace Core

/-- Structural equality on `MalVal`. Lists compare element-wise; atoms by
identity (Nat id), so two `(atom 0)` calls produce non-equal values. -/
public partial def malEqual : MalVal → MalVal → Bool
  | .nil,         .nil         => true
  | .bool a,      .bool b      => a == b
  | .int a,       .int b       => a == b
  | .sym a,       .sym b       => a == b
  | .str a,       .str b       => a == b
  | .atom a,      .atom b      => a == b
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
  let strs ← args.mapM fun v => (Printer.prStr v : IO String)
  IO.println (" ".intercalate strs)
  return .nil

private def readString : MalFn
  | [.str s] =>
    match Reader.readStr s with
    | .ok (some ast) => return ast
    | .ok none       => return .nil
    | .error e       => throw e
  | _ => throw "read-string: expected one string argument"

private def slurp : MalFn
  | [.str path] => do
    let content ← IO.FS.readFile path
    return .str content
  | _ => throw "slurp: expected one string argument"

private def atom : MalFn
  | [v] => do
    let id ← Atoms.new v
    return .atom id
  | _ => throw "atom: expected one argument"

private def atomQ : MalFn
  | [.atom _] => return .bool true
  | [_]       => return .bool false
  | _         => throw "atom?: expected one argument"

private def deref : MalFn
  | [.atom n] => do
    match ← Atoms.deref n with
    | some v => return v
    | none   => throw s!"deref: invalid atom #{n}"
  | _ => throw "deref: expected one atom argument"

private def resetBang : MalFn
  | [.atom n, v] => do
    match ← Atoms.reset n v with
    | some r => return r
    | none   => throw s!"reset!: invalid atom #{n}"
  | _ => throw "reset!: expected (reset! atom value)"

private def table : List (String × MalFn) :=
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
    ("prn",    prn),
    ("read-string", readString),
    ("slurp",       slurp),
    ("atom",        atom),
    ("atom?",       atomQ),
    ("deref",       deref),
    ("reset!",      resetBang) ]

/-- Look up a pure builtin's implementation by name. `eval`, `load-file`,
and `swap!` are *not* here — they need env/internal-eval access and are
handled by the step's `apply`. -/
public def builtin? (name : String) : Option MalFn :=
  table.find? (·.1 == name) |>.map (·.2)

/-- The names of step-6 stateful builtins. Bound to `.fn (.builtin name)` so
they live in the env as values; the step's `apply` matches on the name to
dispatch to env-aware code. -/
public def step6StatefulNames : List String := ["eval", "load-file", "swap!"]

/-- The starting environment for the mal REPL. Builtins (pure and stateful)
are all bound by name to `.fn (.builtin name)`. -/
public def initialEnv : Env :=
  let pureBindings := table.map (fun (name, _) => (name, MalVal.fn (.builtin name)))
  let statefulBindings := step6StatefulNames.map (fun name =>
    (name, MalVal.fn (.builtin name)))
  { current := pureBindings ++ statefulBindings, outer := none }

end Core
