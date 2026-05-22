module

public import MalLean4.Types
open Types

namespace Reader

def isSeparator (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == ','

def isSpecial (c : Char) : Bool :=
  c == '(' || c == ')' || c == ';'

def isTokenChar (c : Char) : Bool :=
  !isSeparator c && !isSpecial c

def readAtom (t : String) : MalVal :=
  match t.toInt? with
  | some n => .int n
  | none   => .sym t

mutual
  partial def readForm : List String → Except String (MalVal × List String)
    | []          => .error "unexpected EOF"
    | "(" :: rest => readList #[] rest
    | ")" :: _    => .error "unexpected ')'"
    | t :: rest   => .ok (readAtom t, rest)

  partial def readList (acc : Array MalVal) :
      List String → Except String (MalVal × List String)
    | []           => .error "unbalanced: expected ')'"
    | ")" :: rest  => .ok (.list acc.toList, rest)
    | toks => do
      let (form, rest) ← readForm toks
      readList (acc.push form) rest
end

partial def tokenize (input : String) : List String :=
  go input.toList
where
  go : List Char → List String
    | [] => []
    | ';' :: rest => go (rest.dropWhile (· != '\n'))
    | c :: rest =>
      if isSeparator c then go rest
      else if c == '(' || c == ')' then String.singleton c :: go rest
      else
        let (taken, rest') := (c :: rest).span isTokenChar
        String.ofList taken :: go rest'

/-- Parse a single mal form from `s`.

Returns `.ok none` for inputs that contain only whitespace or comments,
`.ok (some form)` for a parsed expression, or `.error msg` on a parse failure
(e.g., unbalanced parentheses).
-/
public def readStr (s : String) : Except String (Option MalVal) := do
  match tokenize s with
  | [] => .ok none
  | toks =>
    let (form, _) ← readForm toks
    .ok (some form)

end Reader
