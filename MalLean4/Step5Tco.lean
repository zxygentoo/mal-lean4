import MalLean4.Core
import MalLean4.FreeVars
import MalLean4.Reader
import MalLean4.Printer

open Types

/-- Mal's truthiness: only `nil` and `false` are falsy. -/
def isTruthy : MalVal → Bool
  | .nil        => false
  | .bool false => false
  | _           => true

mutual
  partial def eval (env : Env) : MalVal → MalIO (MalVal × Env)
    | .list []                    => return (.list [], env)
    | .list (.sym "def!" :: rest) => evalDef env rest
    | .list (.sym "let*" :: rest) => evalLet env rest
    | .list (.sym "do"   :: rest) => evalDo  env rest
    | .list (.sym "if"   :: rest) => evalIf  env rest
    | .list (.sym "fn*"  :: rest) => evalFn  env rest
    | .list (head :: args)        => do
      let (head', env1) ← eval env head
      let (args', env2) ← evalArgs env1 args
      let v ← apply env2 head' args'
      return (v, env2)
    | .sym s => do
      match env.find? s with
      | some v => return (v, env)
      | none   => throw s!"'{s}' not found"
    | other  => return (other, env)

  partial def evalArgs (env : Env) :
      List MalVal → MalIO (List MalVal × Env)
    | []      => return ([], env)
    | x :: xs => do
      let (v, env1)  ← eval env x
      let (vs, env2) ← evalArgs env1 xs
      return (v :: vs, env2)

  partial def apply (callerEnv : Env) (head : MalVal)
      (args : List MalVal) : MalIO MalVal := do
    match head with
    | .fn (.builtin name) =>
      match Core.builtin? name with
      | some impl => impl args
      | none      => throw s!"unknown builtin '{name}'"
    | .fn (.lambda params body captures) =>
      if params.length ≠ args.length then
        throw s!"arity mismatch: expected {params.length}, got {args.length}"
      let paramBinds := params.zip args
      let closureEnv : Env :=
        { current := captures ++ paramBinds, outer := some callerEnv }
      let (v, _) ← eval closureEnv body
      return v
    | _ => throw "first item in list is not callable"

  partial def evalDef (env : Env) :
      List MalVal → MalIO (MalVal × Env)
    | [.sym name, expr] => do
      let (v, env') ← eval env expr
      return (v, env'.set name v)
    | _ => throw "def!: expected (def! name expr)"

  partial def evalLet (env : Env) :
      List MalVal → MalIO (MalVal × Env)
    | [.list bindings, body] => do
      let letEnv ← bindLet env.child bindings
      let (v, _) ← eval letEnv body
      return (v, env)
    | _ => throw "let*: expected (let* (bindings) body)"

  partial def bindLet (env : Env) : List MalVal → MalIO Env
    | []                      => return env
    | .sym k :: rhs :: rest   => do
      let (v, env') ← eval env rhs
      bindLet (env'.set k v) rest
    | _ => throw "let*: bindings must be symbol/expr pairs"

  partial def evalDo (env : Env) :
      List MalVal → MalIO (MalVal × Env)
    | []      => return (.nil, env)
    | [last]  => eval env last
    | x :: xs => do
      let (_, env') ← eval env x
      evalDo env' xs

  partial def evalIf (env : Env) :
      List MalVal → MalIO (MalVal × Env)
    | [pred, thn] => do
      let (p, env') ← eval env pred
      if isTruthy p then eval env' thn else return (.nil, env')
    | [pred, thn, els] => do
      let (p, env') ← eval env pred
      if isTruthy p then eval env' thn else eval env' els
    | _ => throw "if: expected (if pred then) or (if pred then else)"

  partial def evalFn (env : Env) :
      List MalVal → MalIO (MalVal × Env)
    | [.list params, body] => do
      let paramNames ← params.mapM fun
        | .sym s => return s
        | _      => throw "fn*: parameter is not a symbol"
      let frees := FreeVars.unique paramNames body
      let captures : List (String × MalVal) := frees.filterMap fun name =>
        env.findLocal? name |>.map ((name, ·))
      return (.fn (.lambda paramNames body captures), env)
    | _ => throw "fn*: expected (fn* (params) body)"
end

def READ  (s : String)   : Except String (Option MalVal) := Reader.readStr s
def PRINT (ast : MalVal) : IO String                     := Printer.prStr ast

def rep (env : Env) (s : String) : IO (Option String × Env) := do
  match READ s with
  | .ok none       => return (none, env)
  | .ok (some ast) =>
    match ← (eval env ast).run with
    | .ok (v, env') => return (some (← PRINT v), env')
    | .error e      => return (some s!"Error: {e}", env)
  | .error e       => return (some s!"Error: {e}", env)

partial def loop (env : Env) (stdin stdout : IO.FS.Stream) : IO Unit := do
  stdout.putStr "user> "
  stdout.flush
  let line ← stdin.getLine
  if line.isEmpty then return
  let (out?, env') ← rep env line
  if let some out := out? then
    stdout.putStrLn out
  loop env' stdin stdout

def main : IO Unit := do
  let env := Core.initialEnv
  let (_, env')  ← rep env "(def! not (fn* (a) (if a false true)))"
  let stdin  ← IO.getStdin
  let stdout ← IO.getStdout
  loop env' stdin stdout
