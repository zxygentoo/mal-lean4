import MalLean4.Core
import MalLean4.Reader
import MalLean4.Printer

open Types

def EVAL (env : Env) : MalVal → Except String MalVal
  | .list []              => .ok (.list [])
  | .list (head :: args)  => do
    match head with
    | .sym name =>
      match env.get? name with
      | some f =>
        let argsV ← args.mapM (EVAL env)
        f argsV
      | none   => .error s!"'{name}' not found"
    | _ => .error "first item in list is not callable"
  | .sym s                => .error s!"'{s}' not found"
  | other                 => .ok other

def READ  (s : String)   : Except String (Option MalVal) := Reader.readStr s
def PRINT (ast : MalVal) : String := Printer.prStr ast

def rep (env : Env) (s : String) : Option String :=
  let result : Except String (Option MalVal) := do
    let astOpt ← READ s
    match astOpt with
    | none      => .ok none
    | some ast  => .ok (some (← EVAL env ast))
  match result with
  | .ok none       => none
  | .ok (some v)   => some (PRINT v)
  | .error e       => some s!"Error: {e}"

partial def loop (env : Env) (stdin stdout : IO.FS.Stream) : IO Unit := do
  stdout.putStr "user> "
  stdout.flush
  let line ← stdin.getLine
  if line.isEmpty then return
  if let some out := rep env line then
    stdout.putStrLn out
  loop env stdin stdout

def main : IO Unit := do
  let stdin  ← IO.getStdin
  let stdout ← IO.getStdout
  loop Core.initialEnv stdin stdout
