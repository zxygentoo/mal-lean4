import MalLean4.Core
import MalLean4.Fn
import MalLean4.Reader
import MalLean4.Printer

open Types

partial def EVAL (env : Env) : MalVal → MalIO MalVal
  | .list []             => return .list []
  | .list (head :: args) => do
    let head' ← EVAL env head
    let args' ← args.mapM (EVAL env)
    match head' with
    | .fn f => f.apply args'
    | _     => throw "first item in list is not callable"
  | .sym s => do
    match ← env.find? s with
    | some v => return v
    | none   => throw s!"'{s}' not found"
  | other  => return other

def READ  (s : String)   : Except String (Option MalVal) := Reader.readStr s
def PRINT (ast : MalVal) : String                        := Printer.prStr ast

def rep (env : Env) (s : String) : IO (Option String) := do
  match READ s with
  | .ok none       => return none
  | .ok (some ast) =>
    match ← (EVAL env ast).run with
    | .ok v    => return some (PRINT v)
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
