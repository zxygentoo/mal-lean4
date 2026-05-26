import MalLean4.Reader
import MalLean4.Printer

open Types

def READ  (s : String)   : Except String (Option MalVal) := Reader.readStr s
def PRINT (ast : MalVal) : IO String                     := Printer.prStr ast

def EVAL (ast : MalVal) : MalVal := ast

def rep (s : String) : IO (Option String) := do
  match READ s with
  | .ok none       => return none
  | .ok (some ast) => return some (← PRINT (EVAL ast))
  | .error e       => return some s!"Error: {e}"

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  stdout.putStr "user> "
  stdout.flush
  let line ← stdin.getLine
  if line.isEmpty then return
  if let some out ← rep line then
    stdout.putStrLn out
  loop stdin stdout

def main : IO Unit := do
  let stdin  ← IO.getStdin
  let stdout ← IO.getStdout
  loop stdin stdout
