module

public import MalLean4.Types
open Types

namespace Reader

def isSeparator (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == ','

def isSpecial (c : Char) : Bool :=
  c == '(' || c == ')' || c == '[' || c == ']' || c == ';' || c == '"'

def isTokenChar (c : Char) : Bool :=
  !isSeparator c && !isSpecial c

private partial def unescape : List Char → List Char
  | [] => []
  | '\\' :: c :: rest =>
    let r := match c with
      | 'n'  => '\n'
      | '\\' => '\\'
      | '"'  => '"'
      | other => other
    r :: unescape rest
  | c :: rest => c :: unescape rest

def readAtom (t : String) : Except String MalVal :=
  match t.toList with
  | '"' :: rest =>
    match rest.reverse with
    | '"' :: bodyRev =>
      .ok (.str (String.ofList (unescape bodyRev.reverse)))
    | _ => .error "unterminated string"
  | _ =>
    match t with
    | "nil"   => .ok .nil
    | "true"  => .ok (.bool true)
    | "false" => .ok (.bool false)
    | _       =>
      match t.toInt? with
      | some n => .ok (.int n)
      | none   => .ok (.sym t)

mutual
  partial def readForm : List String → Except String (MalVal × List String)
    | []          => .error "unexpected EOF"
    | "(" :: rest => readList #[] rest
    | ")" :: _    => .error "unexpected ')'"
    | t :: rest   => do
      let atom ← readAtom t
      .ok (atom, rest)

  partial def readList (acc : Array MalVal) :
      List String → Except String (MalVal × List String)
    | []           => .error "unbalanced: expected ')'"
    | ")" :: rest  => .ok (.list acc.toList, rest)
    | toks => do
      let (form, rest) ← readForm toks
      readList (acc.push form) rest
end

private partial def readStringToken (chars : List Char) (acc : List Char) :
    String × List Char :=
  match chars with
  | []               => (String.ofList ('"' :: acc.reverse), [])
  | '"' :: rest      => (String.ofList ('"' :: acc.reverse ++ ['"']), rest)
  | '\\' :: c :: rest => readStringToken rest (c :: '\\' :: acc)
  | c :: rest        => readStringToken rest (c :: acc)

partial def tokenize (input : String) : List String :=
  go input.toList
where
  go : List Char → List String
    | [] => []
    | ';' :: rest => go (rest.dropWhile (· != '\n'))
    | '"' :: rest =>
      let (tok, rest') := readStringToken rest []
      tok :: go rest'
    | c :: rest =>
      if isSeparator c then go rest
      else if c == '(' || c == '[' then "(" :: go rest
      else if c == ')' || c == ']' then ")" :: go rest
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
