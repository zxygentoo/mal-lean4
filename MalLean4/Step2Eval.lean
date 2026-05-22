import MalLean4.Core
import MalLean4.Reader
import MalLean4.Printer

open Types

mutual
  partial def EVAL (env : Env) : MalVal → MalIO (MalVal × Env)
    | .list []             => return (.list [], env)
    | .list (head :: args) => do
      let (head', env1) ← EVAL env head
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
      let (v, env1)  ← EVAL env x
      let (vs, env2) ← evalArgs env1 xs
      return (v :: vs, env2)

  partial def apply (_callerEnv : Env) (head : MalVal)
      (args : List MalVal) : MalIO MalVal := do
    match head with
    | .fn (.builtin name) =>
      match Core.builtin? name with
      | some impl => impl args
      | none      => throw s!"unknown builtin '{name}'"
    | _ => throw "first item in list is not callable"
end

def READ  (s : String)   : Except String (Option MalVal) := Reader.readStr s
def PRINT (ast : MalVal) : String                        := Printer.prStr ast

def rep (env : Env) (s : String) : IO (Option String × Env) := do
  match READ s with
  | .ok none       => return (none, env)
  | .ok (some ast) =>
    match ← (EVAL env ast).run with
    | .ok (v, env') => return (some (PRINT v), env')
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
  let stdin  ← IO.getStdin
  let stdout ← IO.getStdout
  loop Core.initialEnv stdin stdout
