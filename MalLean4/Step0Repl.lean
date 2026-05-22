def READ (s : String) : String := s

def EVAL (s : String) : String := s

def PRINT (s : String) : String := s

def rep (s : String) : String := PRINT (EVAL (READ s))

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  stdout.putStr "user> "
  stdout.flush
  let line ← stdin.getLine
  if line.isEmpty then return
  stdout.putStrLn (rep line)
  loop stdin stdout

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  loop stdin stdout
