module

public import MalLean4.Types
public import MalLean4.Env
import MalLean4.Atoms
import MalLean4.Printer
import MalLean4.Reader

open Types

namespace Core

/-- Runtime context passed to every builtin. Holds the env at the call
site plus the step's `eval`/`apply` callbacks (`apply` is partially applied
with `env`). Constructed inside `callBuiltin`. -/
structure Context where
  env   : Env
  eval  : Env → MalVal → MalIO MalVal
  apply : MalVal → List MalVal → MalIO MalVal

/-- A mal builtin. Most builtins ignore the context (`fun _ args => …`);
env-aware ones reach into it for `ctx.eval`, `ctx.apply`, or
`ctx.env.root`. -/
abbrev MalFn := Context → List MalVal → MalIO MalVal

def intBinop (op : Int → Int → Int) : MalFn := fun _ => fun
  | [.int a, .int b] => return .int (op a b)
  | _ => throw "expected two integers"

def compOp (op : Int → Int → Bool) : MalFn := fun _ => fun
  | [.int a, .int b] => return .bool (op a b)
  | _ => throw "expected two integers"

def eq : MalFn := fun _ => fun
  | [a, b] => return .bool (a.equal b)
  | _ => throw "=: expected two arguments"

def list : MalFn := fun _ args => return .list args

def list? : MalFn := fun _ => fun
  | [.list _] => return .bool true
  | [_]       => return .bool false
  | _ => throw "list?: expected one argument"

def empty? : MalFn := fun _ => fun
  | [.list xs] => return .bool xs.isEmpty
  | [_]        => return .bool false
  | _ => throw "empty?: expected one argument"

def count : MalFn := fun _ => fun
  | [.list xs] => return .int xs.length
  | [_]        => return .int 0
  | _ => throw "count: expected one argument"

def cons : MalFn := fun _ => fun
  | [x, .list xs] => return .list (x :: xs)
  | _ => throw "cons: expected (cons value list)"

def concat : MalFn := fun _ args => do
  let lists ← args.mapM fun
    | .list xs => return xs
    | _ => throw "concat: expected list arguments"
  return .list lists.flatten

def prn : MalFn := fun _ args => do
  let strs ← args.mapM fun v => (Printer.prStr v : IO String)
  IO.println (" ".intercalate strs)
  return .nil

def println : MalFn := fun _ args => do
  let strs ← args.mapM fun v => (Printer.prStrUnreadably v : IO String)
  IO.println (" ".intercalate strs)
  return .nil

def prStrFn : MalFn := fun _ args => do
  let strs ← args.mapM fun v => (Printer.prStr v : IO String)
  return .str (" ".intercalate strs)

def str : MalFn := fun _ args => do
  let strs ← args.mapM fun v => (Printer.prStrUnreadably v : IO String)
  return .str ("".intercalate strs)

def readString : MalFn := fun _ => fun
  | [.str s] =>
    match Reader.readStr s with
    | .ok (some ast) => return ast
    | .ok none       => return .nil
    | .error e       => throw e
  | _ => throw "read-string: expected one string argument"

def slurp : MalFn := fun _ => fun
  | [.str path] => do
    let content ← IO.FS.readFile path
    return .str content
  | _ => throw "slurp: expected one string argument"

def atom : MalFn := fun _ => fun
  | [v] => do
    let id ← Atoms.new v
    return .atom id
  | _ => throw "atom: expected one argument"

def atom? : MalFn := fun _ => fun
  | [.atom _] => return .bool true
  | [_]       => return .bool false
  | _ => throw "atom?: expected one argument"

def deref : MalFn := fun _ => fun
  | [.atom n] => do
    match ← Atoms.deref n with
    | some v => return v
    | none   => throw s!"deref: invalid atom #{n}"
  | _ => throw "deref: expected one atom argument"

def reset! : MalFn := fun _ => fun
  | [.atom n, v] => do
    match ← Atoms.reset n v with
    | some r => return r
    | none   => throw s!"reset!: invalid atom #{n}"
  | _ => throw "reset!: expected (reset! atom value)"

def eval : MalFn := fun ctx => fun
  | [ast] => ctx.eval ctx.env.root ast
  | _ => throw "eval: expected one argument"

def loadFile : MalFn := fun ctx => fun
  | [.str path] => do
    let content ← IO.FS.readFile path
    match Reader.readStr s!"(do {content}\nnil)" with
    | .ok (some ast) => do
      let _ ← ctx.eval ctx.env.root ast
      return .nil
    | .ok none       => return .nil
    | .error e       => throw e
  | _ => throw "load-file: expected one string argument"

def swap! : MalFn := fun ctx => fun
  | .atom n :: fnArg :: rest => do
    match ← Atoms.deref n with
    | some current => do
      let newV ← ctx.apply fnArg (current :: rest)
      let _ ← Atoms.reset n newV
      return newV
    | none         => throw s!"swap!: invalid atom #{n}"
  | _ => throw "swap!: expected (swap! atom fn args...)"

def table : List (String × MalFn) :=
  [ ("+",  intBinop (· + ·)),
    ("-",  intBinop (· - ·)),
    ("*",  intBinop (· * ·)),
    ("/",  intBinop (· / ·)),
    ("<",  compOp (· < ·)),
    ("<=", compOp (· ≤ ·)),
    (">",  compOp (· > ·)),
    (">=", compOp (· ≥ ·)),
    ("=",           eq),
    ("list",        list),
    ("list?",       list?),
    ("empty?",      empty?),
    ("count",       count),
    ("cons",        cons),
    ("concat",      concat),
    ("prn",         prn),
    ("println",     println),
    ("pr-str",      prStrFn),
    ("str",         str),
    ("read-string", readString),
    ("slurp",       slurp),
    ("atom",        atom),
    ("atom?",       atom?),
    ("deref",       deref),
    ("reset!",      reset!),
    ("eval",        eval),
    ("load-file",   loadFile),
    ("swap!",       swap!) ]

/-- Dispatch a builtin by `name` with the step's `eval`/`apply` callbacks
(`apply` should be partially applied with the caller's env). Errors if
`name` is not a registered builtin. -/
public def callBuiltin
    (name : String)
    (env : Env)
    (eval : Env → MalVal → MalIO MalVal)
    (apply : MalVal → List MalVal → MalIO MalVal)
    (args : List MalVal)
    : MalIO MalVal := do
  match table.find? (·.1 == name) with
  | some (_, impl) => impl { env, eval, apply } args
  | none           => throw s!"unknown builtin '{name}'"

/-- The starting environment for the mal REPL, with every builtin bound by
name. -/
public def initialEnv : IO Env := do
  let env ← Env.empty
  for (name, _) in table do
    env.set name (.fn (.builtin name))
  return env

end Core
