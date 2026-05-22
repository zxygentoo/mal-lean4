import MalLean4.Core
import MalLean4.Reader
import MalLean4.Printer

open Types

mutual
  partial def eval (env : Env) : MalVal → MalIO MalVal
    | .list []                    => return .list []
    | .list (.sym "def!" :: rest) => evalDef env rest
    | .list (.sym "let*" :: rest) => evalLet env rest
    | .list (head :: args)        => do
      let head' ← eval env head
      let args' ← args.mapM (eval env)
      apply env head' args'
    | .sym s => do
      match ← env.find? s with
      | some v => return v
      | none   => throw s!"'{s}' not found"
    | other => return other

  partial def apply (callerEnv : Env) (head : MalVal)
      (args : List MalVal) : MalIO MalVal := do
    match head with
    | .fn (.builtin name) =>
      match Core.builtin? name with
      | some impl =>
        impl { env := callerEnv, eval := eval, apply := apply callerEnv } args
      | none      => throw s!"unknown builtin '{name}'"
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

def main : IO Unit := do
  let stdin  ← IO.getStdin
  let stdout ← IO.getStdout
  let env    ← Core.initialEnv
  loop env stdin stdout
