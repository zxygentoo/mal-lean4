import MalLean4.Core
import MalLean4.Reader
import MalLean4.Printer

open Types

mutual
  partial def EVAL (env : Env) : MalVal → MalIO MalVal
    | .list []             => return .list []
    | .list (head :: args) => evalCall head args
    | .sym s               => lookupSym s
    | other                => return other
  where
    evalCall (head : MalVal) (args : List MalVal) : MalIO MalVal := do
      let head' ← EVAL env head
      let args' ← args.mapM (EVAL env)
      apply env head' args'
    lookupSym (s : String) : MalIO MalVal := do
      match ← env.find? s with
      | some v => return v
      | none   => throw (.str s!"'{s}' not found")

  partial def apply (callerEnv : Env) (head : MalVal)
      (args : List MalVal) : MalIO MalVal := do
    match head with
    | .fn (.builtin name) =>
      Core.callBuiltin name callerEnv EVAL (apply callerEnv) args
    | _ => throw (.str "first item in list is not callable")
end

def READ  (s : String)   : Except String (Option MalVal) := Reader.readStr s
def PRINT (ast : MalVal) : IO String                     := Printer.prStr ast

def rep (env : Env) (s : String) : IO (Option String) := do
  match READ s with
  | .ok none       => return none
  | .ok (some ast) =>
    match ← (EVAL env ast).run with
    | .ok v    => return some (← PRINT v)
    | .error e => return some s!"Error: {← Printer.prStr e}"
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
