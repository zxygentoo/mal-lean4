import MalLean4.Core
import MalLean4.Reader
import MalLean4.Printer

open Types

mutual
  partial def eval (env : Env) : MalVal → Except String (MalVal × Env)
    | .list []                    => .ok (.list [], env)
    | .list (.sym "def!" :: rest) => evalDef env rest
    | .list (.sym "let*" :: rest) => evalLet env rest
    | .list (head :: args)        => do
      let (head', env1) ← eval env head
      let (args', env2) ← evalSeq env1 args
      let v ← Core.apply head' args'
      .ok (v, env2)
    | .sym s                      =>
      match env.find? s with
      | some v => .ok (v, env)
      | none   => .error s!"'{s}' not found"
    | other                       => .ok (other, env)

  partial def evalSeq (env : Env) :
      List MalVal → Except String (List MalVal × Env)
    | []      => .ok ([], env)
    | x :: xs => do
      let (x',  env1) ← eval env x
      let (xs', env2) ← evalSeq env1 xs
      .ok (x' :: xs', env2)

  partial def evalDef (env : Env) :
      List MalVal → Except String (MalVal × Env)
    | [.sym name, expr] => do
      let (v, env') ← eval env expr
      .ok (v, env'.set name v)
    | _ => .error "def!: expected (def! name expr)"

  partial def evalLet (env : Env) :
      List MalVal → Except String (MalVal × Env)
    | [.list bindings, body] => do
      let letEnv ← evalLetBindings env.child bindings
      let (v, _) ← eval letEnv body
      .ok (v, env)
    | _ => .error "let*: expected (let* (bindings) body)"

  partial def evalLetBindings (env : Env) :
      List MalVal → Except String Env
    | []                      => .ok env
    | .sym k :: vExpr :: rest => do
      let (v, env') ← eval env vExpr
      evalLetBindings (env'.set k v) rest
    | _ => .error "let*: bindings must be symbol/expr pairs"
end

def READ  (s : String)   : Except String (Option MalVal) := Reader.readStr s
def PRINT (ast : MalVal) : String                        := Printer.prStr ast

def rep (env : Env) (s : String) : Option String × Env :=
  match READ s with
  | .ok none       => (none, env)
  | .ok (some ast) =>
    match eval env ast with
    | .ok (v, env') => (some (PRINT v), env')
    | .error e      => (some s!"Error: {e}", env)
  | .error e       => (some s!"Error: {e}", env)

partial def loop (env : Env) (stdin stdout : IO.FS.Stream) : IO Unit := do
  stdout.putStr "user> "
  stdout.flush
  let line ← stdin.getLine
  if line.isEmpty then return
  let (out?, env') := rep env line
  if let some out := out? then
    stdout.putStrLn out
  loop env' stdin stdout

def main : IO Unit := do
  let stdin  ← IO.getStdin
  let stdout ← IO.getStdout
  loop Core.initialEnv stdin stdout
