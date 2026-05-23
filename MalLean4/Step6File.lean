import MalLean4.Core
import MalLean4.FreeVars
import MalLean4.Reader
import MalLean4.Printer

open Types

mutual
  partial def eval (env : Env) : MalVal → MalIO MalVal
    | .list []                    => return .list []
    | .list (.sym "def!" :: rest) => evalDef env rest
    | .list (.sym "let*" :: rest) => evalLet env rest
    | .list (.sym "do"   :: rest) => evalDo  env rest
    | .list (.sym "if"   :: rest) => evalIf  env rest
    | .list (.sym "fn*"  :: rest) => evalFn  env rest
    | .list (head :: args)        => evalCall head args
    | .sym s                      => lookupSym s
    | other                       => return other
  where
    evalCall (head : MalVal) (args : List MalVal) : MalIO MalVal := do
      let head' ← eval env head
      let args' ← args.mapM (eval env)
      apply env head' args'
    lookupSym (s : String) : MalIO MalVal := do
      match ← env.find? s with
      | some v => return v
      | none   => throw s!"'{s}' not found"

  partial def apply (callerEnv : Env) (head : MalVal)
      (args : List MalVal) : MalIO MalVal := do
    match head with
    | .fn (.builtin name) =>
      Core.callBuiltin name callerEnv eval (apply callerEnv) args
    | .fn (.lambda l)     =>
      if l.params.length ≠ args.length then
        throw s!"arity mismatch: expected {l.params.length}, got {args.length}"
      let closureEnv ← callerEnv.new
      for (k, v) in l.snapshot do
        closureEnv.set k v
      for (p, a) in l.params.zip args do
        closureEnv.set p a
      eval closureEnv l.body
    | _ => throw "first item in list is not callable"

  partial def evalDef (env : Env) : List MalVal → MalIO MalVal
    | [.sym name, expr] => do
      let v ← eval env expr
      env.set name v
      return v
    | _ => throw "def!: expected (def! name expr)"

  partial def evalLet (env : Env) : List MalVal → MalIO MalVal
    | [.list bindings, body] => do
      let letEnv ← env.new
      bindLet letEnv bindings
      eval letEnv body
    | _ => throw "let*: expected (let* (bindings) body)"

  partial def bindLet (env : Env) : List MalVal → MalIO Unit
    | []                    => return ()
    | .sym k :: rhs :: rest => do
      let v ← eval env rhs
      env.set k v
      bindLet env rest
    | _ => throw "let*: bindings must be symbol/expr pairs"

  partial def evalDo (env : Env) : List MalVal → MalIO MalVal
    | []      => return .nil
    | [last]  => eval env last
    | x :: xs => do
      let _ ← eval env x
      evalDo env xs

  partial def evalIf (env : Env) : List MalVal → MalIO MalVal
    | [pred, thn]      => do
      if (← eval env pred).isTruthy then eval env thn else return .nil
    | [pred, thn, els] => do
      if (← eval env pred).isTruthy then eval env thn else eval env els
    | _ => throw "if: expected (if pred then) or (if pred then else)"

  partial def evalFn (env : Env) : List MalVal → MalIO MalVal
    | [.list params, body] => do
      let paramNames ← params.mapM fun
        | .sym s => return s
        | _ => throw "fn*: parameter is not a symbol"
      let frees := FreeVars.unique paramNames body
      let pairs ← frees.mapM fun name => do
        return (← env.findLocal? name).map (Prod.mk name)
      let snapshot := pairs.filterMap id
      return .fn (.lambda { params := paramNames, body, snapshot })
    | _ => throw "fn*: expected (fn* (params) body)"
end

def READ  (s : String)   : Except String (Option MalVal) := Reader.readStr s
def PRINT (ast : MalVal) : IO String                     := Printer.prStr ast

def rep (env : Env) (s : String) : IO (Option String) := do
  match READ s with
  | .ok none       => return none
  | .ok (some ast) =>
    match ← (eval env ast).run with
    | .ok v    => return some (← PRINT v)
    | .error e => return some s!"Error: {e}"
  | .error e       => return some s!"Error: {e}"

partial def loop (env : Env) (stdin stdout : IO.FS.Stream) : IO Unit := do
  stdout.putStr "user> "
  stdout.flush
  let line ← stdin.getLine
  if line.isEmpty then return
  if let some out ← rep env line then
    stdout.putStrLn out
  loop env stdin stdout

def main (args : List String) : IO Unit := do
  let env ← Core.initialEnv
  let _ ← rep env "(def! not (fn* (a) (if a false true)))"
  match args with
  | [] =>
    env.set "*ARGV*" (.list [])
    let stdin  ← IO.getStdin
    let stdout ← IO.getStdout
    loop env stdin stdout
  | file :: rest =>
    let argv : List MalVal := rest.map MalVal.str
    env.set "*ARGV*" (.list argv)
    let _ ← rep env s!"(load-file \"{file}\")"
    return
