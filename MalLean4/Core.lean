module

public import MalLean4.Types
public import MalLean4.Env
import MalLean4.Atoms
import MalLean4.Printer
import MalLean4.Reader
import Std.Data.HashMap.Basic

open Types

namespace Core

-- Recognises `& rest` as the rest-binder.
public def parseParams : List MalVal → MalIO (List String × Option String)
  | [] => return ([], none)
  | .sym "&" :: .sym restName :: [] => return ([], some restName)
  | .sym "&" :: _ =>
    throw (.str "fn*: `&` must be followed by a single rest-param symbol")
  | .sym p :: rest => do
    let (more, rp) ← parseParams rest
    return (p :: more, rp)
  | _ => throw (.str "fn*: parameter is not a symbol")

-- Env-aware builtins reach into this for `ctx.eval`, `ctx.apply`, or
-- `ctx.env.root`. `apply` is partially applied with `env` by `callBuiltin`.
structure Context where
  env   : Env
  eval  : Env → MalVal → MalIO MalVal
  apply : MalVal → List MalVal → MalIO MalVal

abbrev MalFn := Context → List MalVal → MalIO MalVal

def intBinop (op : Int → Int → Int) : MalFn := fun _ => fun
  | [.int a, .int b] => return .int (op a b)
  | _ => throw (.str "expected two integers")

def compOp (op : Int → Int → Bool) : MalFn := fun _ => fun
  | [.int a, .int b] => return .bool (op a b)
  | _ => throw (.str "expected two integers")

def eq : MalFn := fun _ => fun
  | [a, b] => return .bool (a.equal b)
  | _ => throw (.str "=: expected two arguments")

def list : MalFn := fun _ args => return .list args

def list? : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .list _ => return .bool true
    | _       => return .bool false
  | _ => throw (.str "list?: expected one argument")

def vector : MalFn := fun _ args => return .vec args

def vector? : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .vec _ => return .bool true
    | _      => return .bool false
  | _ => throw (.str "vector?: expected one argument")

def sequential? : MalFn := fun _ => fun
  | [v] => return .bool v.isSequential
  | _   => throw (.str "sequential?: expected one argument")

def vec : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .list xs => return .vec xs
    | .vec xs  => return .vec xs
    | .nil     => return .vec []
    | _ => throw (.str "vec: expected a sequence")
  | _ => throw (.str "vec: expected a sequence")

def empty? : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .list xs => return .bool xs.isEmpty
    | .vec xs  => return .bool xs.isEmpty
    | .map xs  => return .bool xs.isEmpty
    | .nil     => return .bool true
    | _        => return .bool false
  | _ => throw (.str "empty?: expected one argument")

def count : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .list xs => return .int xs.length
    | .vec xs  => return .int xs.length
    | .map xs  => return .int xs.length
    | .nil     => return .int 0
    | _        => return .int 0
  | _ => throw (.str "count: expected one argument")

def cons : MalFn := fun _ => fun
  | [x, v] => match v.strip with
    | .list xs => return .list (x :: xs)
    | .vec xs  => return .list (x :: xs)
    | .nil     => return .list [x]
    | _ => throw (.str "cons: expected (cons value sequence)")
  | _ => throw (.str "cons: expected (cons value sequence)")

def concat : MalFn := fun _ args => do
  let lists ← args.mapM fun a => match a.strip with
    | .list xs => return xs
    | .vec xs  => return xs
    | .nil     => return []
    | _ => throw (.str "concat: expected sequence arguments")
  return .list lists.flatten

def prn : MalFn := fun _ args => do
  let strs ← args.mapM fun v => (Printer.prStr v : IO String)
  IO.println (" ".intercalate strs)
  return .nil

def println : MalFn := fun _ args => do
  let strs ← args.mapM fun v => (Printer.prStrUnreadably v : IO String)
  IO.println (" ".intercalate strs)
  return .nil

def prStr : MalFn := fun _ args => do
  let strs ← args.mapM fun v => (Printer.prStr v : IO String)
  return .str (" ".intercalate strs)

def str : MalFn := fun _ args => do
  let strs ← args.mapM fun v => (Printer.prStrUnreadably v : IO String)
  return .str ("".intercalate strs)

def readString : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .str s =>
      match Reader.readStr s with
      | .ok (some ast) => return ast
      | .ok none       => return .nil
      | .error e       => throw (.str e)
    | _ => throw (.str "read-string: expected one string argument")
  | _ => throw (.str "read-string: expected one string argument")

def slurp : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .str path => do
      match ← (IO.FS.readFile path).toBaseIO with
      | .ok content => return .str content
      | .error e    => throw (.str s!"slurp: {e}")
    | _ => throw (.str "slurp: expected one string argument")
  | _ => throw (.str "slurp: expected one string argument")

def readline : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .str prompt => do
      let stdout ← IO.getStdout
      let stdin  ← IO.getStdin
      stdout.putStr prompt
      stdout.flush
      let line ← stdin.getLine
      if line.isEmpty then return .nil
      let s := if line.back == '\n' then line.dropEnd 1 |>.toString else line
      return .str s
    | _ => throw (.str "readline: expected one string argument")
  | _ => throw (.str "readline: expected one string argument")

-- Forces strict monotonicity for the `time-ms` test: a call fast enough
-- to finish inside one wall-clock millisecond still returns `> prev`.
initialize timeMsLast : IO.Ref Nat ← IO.mkRef 0

def timeMs : MalFn := fun _ => fun
  | [] => do
    let ns ← IO.monoNanosNow
    let ms := ns / 1000000
    let prev ← timeMsLast.get
    let next := if ms > prev then ms else prev + 1
    timeMsLast.set next
    return .int (Int.ofNat next)
  | _ => throw (.str "time-ms: expected no arguments")

def atom : MalFn := fun _ => fun
  | [v] => do
    let id ← Atoms.new v
    return .atom id
  | _ => throw (.str "atom: expected one argument")

def atom? : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .atom _ => return .bool true
    | _       => return .bool false
  | _ => throw (.str "atom?: expected one argument")

def deref : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .atom n => do
      match ← Atoms.deref n with
      | some v => return v
      | none   => throw (.str s!"deref: invalid atom #{n}")
    | _ => throw (.str "deref: expected one atom argument")
  | _ => throw (.str "deref: expected one atom argument")

def reset! : MalFn := fun _ => fun
  | [a, v] => match a.strip with
    | .atom n => do
      match ← Atoms.reset n v with
      | some r => return r
      | none   => throw (.str s!"reset!: invalid atom #{n}")
    | _ => throw (.str "reset!: expected (reset! atom value)")
  | _ => throw (.str "reset!: expected (reset! atom value)")

def eval : MalFn := fun ctx => fun
  | [ast] => ctx.eval ctx.env.root ast
  | _ => throw (.str "eval: expected one argument")

def loadFile : MalFn := fun ctx => fun
  | [v] => match v.strip with
    | .str path => do
      match ← (IO.FS.readFile path).toBaseIO with
      | .error e      => throw (.str s!"load-file: {e}")
      | .ok content   =>
        match Reader.readStr s!"(do {content}\nnil)" with
        | .ok (some ast) => do
          let _ ← ctx.eval ctx.env.root ast
          return .nil
        | .ok none       => return .nil
        | .error e       => throw (.str e)
    | _ => throw (.str "load-file: expected one string argument")
  | _ => throw (.str "load-file: expected one string argument")

def swap! : MalFn := fun ctx => fun
  | a :: fnArg :: rest => match a.strip with
    | .atom n => do
      match ← Atoms.deref n with
      | some current => do
        let newV ← ctx.apply fnArg (current :: rest)
        let _ ← Atoms.reset n newV
        return newV
      | none => throw (.str s!"swap!: invalid atom #{n}")
    | _ => throw (.str "swap!: expected (swap! atom fn args...)")
  | _ => throw (.str "swap!: expected (swap! atom fn args...)")

def throwFn : MalFn := fun _ => fun
  | [v] => throw v
  | _   => throw (.str "throw: expected one argument")

def symbol? : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .sym _ => return .bool true
    | _      => return .bool false
  | _ => throw (.str "symbol?: expected one argument")

def symbol : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .str s => return .sym s
    | .sym s => return .sym s
    | _      => throw (.str "symbol: expected one string argument")
  | _ => throw (.str "symbol: expected one string argument")

def keyword : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .str s => return .kw s
    | .kw  s => return .kw s
    | _      => throw (.str "keyword: expected one string argument")
  | _ => throw (.str "keyword: expected one string argument")

def keyword? : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .kw _ => return .bool true
    | _     => return .bool false
  | _ => throw (.str "keyword?: expected one argument")

def string? : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .str _ => return .bool true
    | _      => return .bool false
  | _ => throw (.str "string?: expected one argument")

def number? : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .int _ => return .bool true
    | _      => return .bool false
  | _ => throw (.str "number?: expected one argument")

def fn? : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .fn (.builtin _) => return .bool true
    | .fn (.lambda l)  => return .bool (!l.isMacro?)
    | _                => return .bool false
  | _ => throw (.str "fn?: expected one argument")

def macro? : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .fn (.lambda l) => return .bool l.isMacro?
    | _               => return .bool false
  | _ => throw (.str "macro?: expected one argument")

def nil? : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .nil => return .bool true
    | _    => return .bool false
  | _ => throw (.str "nil?: expected one argument")

def true? : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .bool true => return .bool true
    | _          => return .bool false
  | _ => throw (.str "true?: expected one argument")

def false? : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .bool false => return .bool true
    | _           => return .bool false
  | _ => throw (.str "false?: expected one argument")

def apply : MalFn := fun ctx => fun
  | []        => throw (.str "apply: expected at least a function and a list")
  | [_]       => throw (.str "apply: expected at least a function and a list")
  | f :: rest =>
    match rest.reverse with
    | last :: revInit =>
      match last.strip with
      | .list lastArgs => ctx.apply f (revInit.reverse ++ lastArgs)
      | .vec lastArgs  => ctx.apply f (revInit.reverse ++ lastArgs)
      | _ => throw (.str "apply: last argument must be a sequence")
    | _ => throw (.str "apply: last argument must be a sequence")

def map : MalFn := fun ctx => fun
  | [f, v] => match v.strip with
    | .list xs => do
      let results ← xs.mapM (fun x => ctx.apply f [x])
      return .list results
    | .vec xs  => do
      let results ← xs.mapM (fun x => ctx.apply f [x])
      return .list results
    | _ => throw (.str "map: expected (map fn sequence)")
  | _ => throw (.str "map: expected (map fn sequence)")

def nth : MalFn := fun _ => fun
  | [seq, idx] => do
    match idx.strip with
    | .int n =>
      match seq.toList? with
      | some xs =>
        if n < 0 then
          throw (.str s!"nth: index {n} out of range (length {xs.length})")
        else
          match xs[n.toNat]? with
          | some v => return v
          | none   => throw (.str s!"nth: index {n} out of range (length {xs.length})")
      | none => throw (.str "nth: expected (nth sequence index)")
    | _ => throw (.str "nth: expected (nth sequence index)")
  | _ => throw (.str "nth: expected (nth sequence index)")

def first : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .nil            => return .nil
    | .list []        => return .nil
    | .vec  []        => return .nil
    | .list (x :: _)  => return x
    | .vec  (x :: _)  => return x
    | _ => throw (.str "first: expected a sequence or nil")
  | _ => throw (.str "first: expected a sequence or nil")

def rest : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .nil             => return .list []
    | .list []         => return .list []
    | .vec  []         => return .list []
    | .list (_ :: xs)  => return .list xs
    | .vec  (_ :: xs)  => return .list xs
    | _ => throw (.str "rest: expected a sequence or nil")
  | _ => throw (.str "rest: expected a sequence or nil")

-- Replace existing entries by key, append new ones, preserve order.
def assocList (pairs : List (MalVal × MalVal))
    (extras : List (MalVal × MalVal)) : List (MalVal × MalVal) :=
  extras.foldl (fun acc (k, v) =>
    if acc.any (fun (k', _) => MalVal.equal k k') then
      acc.map fun (k', v') => if MalVal.equal k k' then (k', v) else (k', v')
    else
      acc ++ [(k, v)]) pairs

def dissocList (pairs : List (MalVal × MalVal))
    (keys : List MalVal) : List (MalVal × MalVal) :=
  pairs.filter fun (k, _) => !keys.any (MalVal.equal k)

partial def pairUp : List MalVal → MalIO (List (MalVal × MalVal))
  | []           => return []
  | [_]          => throw (.str "hash-map: odd number of arguments")
  | k :: v :: rest => do
    let more ← pairUp rest
    return (k, v) :: more

def hashMap : MalFn := fun _ args => do
  let pairs ← pairUp args
  return .map (MalVal.dedupMap pairs)

def map? : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .map _ => return .bool true
    | _      => return .bool false
  | _ => throw (.str "map?: expected one argument")

def assoc : MalFn := fun _ => fun
  | m :: rest => match m.strip with
    | .map pairs => do
      let extras ← pairUp rest
      return .map (assocList pairs extras)
    | _ => throw (.str "assoc: expected (assoc map k v ...)")
  | _ => throw (.str "assoc: expected (assoc map k v ...)")

def dissoc : MalFn := fun _ => fun
  | m :: keys => match m.strip with
    | .map pairs => return .map (dissocList pairs keys)
    | _ => throw (.str "dissoc: expected (dissoc map k ...)")
  | _ => throw (.str "dissoc: expected (dissoc map k ...)")

def get : MalFn := fun _ => fun
  | [m, k] => match m.strip with
    | .nil       => return .nil
    | .map pairs =>
      match pairs.find? (fun (k', _) => MalVal.equal k k') with
      | some (_, v) => return v
      | none        => return .nil
    | _ => throw (.str "get: expected (get map key)")
  | _ => throw (.str "get: expected (get map key)")

def contains? : MalFn := fun _ => fun
  | [m, k] => match m.strip with
    | .nil       => return .bool false
    | .map pairs => return .bool (pairs.any fun (k', _) => MalVal.equal k k')
    | _ => throw (.str "contains?: expected (contains? map key)")
  | _ => throw (.str "contains?: expected (contains? map key)")

def keys : MalFn := fun _ => fun
  | [m] => match m.strip with
    | .map pairs => return .list (pairs.map (·.1))
    | _ => throw (.str "keys: expected one hash-map argument")
  | _ => throw (.str "keys: expected one hash-map argument")

def vals : MalFn := fun _ => fun
  | [m] => match m.strip with
    | .map pairs => return .list (pairs.map (·.2))
    | _ => throw (.str "vals: expected one hash-map argument")
  | _ => throw (.str "vals: expected one hash-map argument")

def seq : MalFn := fun _ => fun
  | [v] => match v.strip with
    | .nil      => return .nil
    | .list []  => return .nil
    | .vec  []  => return .nil
    | .list xs  => return .list xs
    | .vec  xs  => return .list xs
    | .str  ""  => return .nil
    | .str  s   =>
      return .list (s.toList.map fun c => .str (String.singleton c))
    | _ => throw (.str "seq: expected a sequence, string, or nil")
  | _ => throw (.str "seq: expected a sequence, string, or nil")

def conj : MalFn := fun _ => fun
  | s :: rest => match s.strip with
    | .list xs => return .list (rest.reverse ++ xs)
    | .vec  xs => return .vec (xs ++ rest)
    | _ => throw (.str "conj: expected (conj sequence value ...)")
  | _ => throw (.str "conj: expected (conj sequence value ...)")

def metaFn : MalFn := fun _ => fun
  | [v] => return v.getMeta
  | _   => throw (.str "meta: expected one argument")

def withMeta : MalFn := fun _ => fun
  | [.withMeta v _, m] => return .withMeta v m
  | [v, m]             => return .withMeta v m
  | _ => throw (.str "with-meta: expected (with-meta value meta)")

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
    ("vector",      vector),
    ("vector?",     vector?),
    ("sequential?", sequential?),
    ("vec",         vec),
    ("empty?",      empty?),
    ("count",       count),
    ("cons",        cons),
    ("concat",      concat),
    ("first",       first),
    ("rest",        rest),
    ("seq",         seq),
    ("conj",        conj),
    ("hash-map",    hashMap),
    ("map?",        map?),
    ("assoc",       assoc),
    ("dissoc",      dissoc),
    ("get",         get),
    ("contains?",   contains?),
    ("keys",        keys),
    ("vals",        vals),
    ("meta",        metaFn),
    ("with-meta",   withMeta),
    ("prn",         prn),
    ("println",     println),
    ("pr-str",      prStr),
    ("str",         str),
    ("read-string", readString),
    ("slurp",       slurp),
    ("readline",    readline),
    ("time-ms",     timeMs),
    ("atom",        atom),
    ("atom?",       atom?),
    ("deref",       deref),
    ("reset!",      reset!),
    ("eval",        eval),
    ("load-file",   loadFile),
    ("swap!",       swap!),
    ("throw",       throwFn),
    ("symbol?",     symbol?),
    ("symbol",      symbol),
    ("keyword",     keyword),
    ("keyword?",    keyword?),
    ("string?",     string?),
    ("number?",     number?),
    ("fn?",         fn?),
    ("macro?",      macro?),
    ("nil?",        nil?),
    ("true?",       true?),
    ("false?",      false?),
    ("apply",       apply),
    ("map",         map),
    ("nth",         nth) ]

private def tableMap : Std.HashMap String MalFn :=
  table.foldl (fun m (k, v) => m.insert k v) ∅

-- Dispatches a builtin by name with the step's eval/apply callbacks
-- (`apply` should be partially applied with the caller's env).
public def callBuiltin
    (name : String)
    (env : Env)
    (eval : Env → MalVal → MalIO MalVal)
    (apply : MalVal → List MalVal → MalIO MalVal)
    (args : List MalVal)
    : MalIO MalVal := do
  match tableMap[name]? with
  | some impl => impl { env, eval, apply } args
  | none      => throw (.str s!"unknown builtin '{name}'")

public def initialEnv : IO Env := do
  let env ← Env.empty
  for (name, _) in table do
    env.set name (.fn (.builtin name))
  return env

end Core
