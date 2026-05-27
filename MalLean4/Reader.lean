module

public import MalLean4.Types

open Types

namespace Reader

def isSeparator (c : Char) : Bool := " \t\n\r,".contains c

def isStandalone (c : Char) : Bool := "()[]{}'`~^@".contains c

-- `;` and `"` get their own branches in `tokenize` before the
-- standalone-char branch; they're listed here so `isTokenChar` excludes
-- them.
def isSpecial (c : Char) : Bool :=
  isStandalone c || c == ';' || c == '"'

def isTokenChar (c : Char) : Bool :=
  !isSeparator c && !isSpecial c

partial def unescape : List Char → List Char
  | []                => []
  | '\\' :: c :: rest =>
    let r := match c with
      | 'n'   => '\n'
      | '\\'  => '\\'
      | '"'   => '"'
      | other => other
    r :: unescape rest
  | c :: rest         => c :: unescape rest

def readAtom (t : String) : Except String MalVal :=
  match t.toList with
  | '"' :: rest =>
    match rest.reverse with
    | '"' :: bodyRev => .ok (.str (String.ofList (unescape bodyRev.reverse)))
    | _ => .error "unbalanced string: missing closing '\"' before end of input"
  | ':' :: rest => .ok (.kw (String.ofList rest))
  | _ =>
    match t with
    | "nil"   => .ok .nil
    | "true"  => .ok (.bool true)
    | "false" => .ok (.bool false)
    | _ =>
      match t.toInt? with
      | some n => .ok (.int n)
      | none   => .ok (.sym t)

mutual
  partial def readForm : List String → Except String (MalVal × List String)
    | []           => .error "unexpected EOF"
    | "("  :: rest => readSeq #[] ")" .list rest
    | "["  :: rest => readSeq #[] "]" .vec  rest
    | "{"  :: rest => readMap #[] rest
    | ")"  :: _    => .error "unexpected ')'"
    | "]"  :: _    => .error "unexpected ']'"
    | "}"  :: _    => .error "unexpected '}'"
    | "'"  :: rest => quoteMacro "quote"          rest
    | "`"  :: rest => quoteMacro "quasiquote"     rest
    | "~"  :: rest => quoteMacro "unquote"        rest
    | "~@" :: rest => quoteMacro "splice-unquote" rest
    | "@"  :: rest => quoteMacro "deref"          rest
    | "^"  :: rest => do
      let (metaForm, rest')  ← readForm rest
      let (valueForm, rest'') ← readForm rest'
      .ok (.list [.sym "with-meta", valueForm, metaForm], rest'')
    | t    :: rest => do
      let atom ← readAtom t
      .ok (atom, rest)

  partial def readSeq (acc : Array MalVal) (close : String)
      (wrap : List MalVal → MalVal) :
      List String → Except String (MalVal × List String)
    | []          => .error s!"unbalanced: expected '{close}'"
    | t :: rest   =>
      if t == close then .ok (wrap acc.toList, rest)
      else do
        let (form, rest') ← readForm (t :: rest)
        readSeq (acc.push form) close wrap rest'

  partial def readMap (acc : Array (MalVal × MalVal)) :
      List String → Except String (MalVal × List String)
    | []          => .error "unbalanced: expected '}'"
    | "}" :: rest => .ok (.map (MalVal.dedupMap acc.toList), rest)
    | toks        => do
      let (key, rest)  ← readForm toks
      let (val, rest') ← readForm rest
      readMap (acc.push (key, val)) rest'

  partial def quoteMacro (name : String) (toks : List String) :
      Except String (MalVal × List String) := do
    let (form, rest) ← readForm toks
    .ok (.list [.sym name, form], rest)
end

-- Returns the token (always starting with `"`) and the rest of the
-- input. An unterminated literal returns with no closing quote so the
-- parser can emit "unbalanced string" rather than silently accept it.
partial def readStringToken (chars : List Char) (acc : List Char) :
    String × List Char :=
  match chars with
  | []                => (String.ofList ('"' :: acc.reverse), [])
  | '"' :: rest       => (String.ofList ('"' :: acc.reverse ++ ['"']), rest)
  | '\\' :: c :: rest => readStringToken rest (c :: '\\' :: acc)
  | c :: rest         => readStringToken rest (c :: acc)

partial def tokenize (input : String) : List String :=
  go input.toList
where
  go : List Char → List String
    | []                 => []
    | ';' :: rest        => go (rest.dropWhile (· != '\n'))
    | '"' :: rest        =>
      let (tok, rest') := readStringToken rest []
      tok :: go rest'
    | '~' :: '@' :: rest => "~@" :: go rest
    | c :: rest          =>
      if isSeparator c then go rest
      else if isStandalone c then String.singleton c :: go rest
      else
        let (taken, rest') := (c :: rest).span isTokenChar
        String.ofList taken :: go rest'

-- `.ok none` for whitespace/comment-only input; `.ok (some form)` for a
-- parsed expression; `.error msg` for parse failures.
public def readStr (s : String) : Except String (Option MalVal) := do
  match tokenize s with
  | [] => .ok none
  | toks =>
    let (form, _) ← readForm toks
    .ok (some form)

/-! ## Proofs

`readAtom` parses each canonical token form back to the value the printer
emits for it. (`readAtom` is private, so these live here.) -/

theorem readAtom_nil   : readAtom "nil"   = .ok .nil          := rfl
theorem readAtom_true  : readAtom "true"  = .ok (.bool true)  := rfl
theorem readAtom_false : readAtom "false" = .ok (.bool false) := rfl

-- A `:kw` token round-trips to the keyword (the printer emits `":" ++ s`).
theorem readAtom_kw (s : String) : readAtom (":" ++ s) = .ok (.kw s) := by
  simp [readAtom, String.ofList_toList]

-- An integer token routes to `.int`: given that it's a numeral (so the
-- `"`/`:`/`nil`/`true`/`false` branches don't fire) and that Lean's
-- `toInt?` parses it. That second fact — `toString n` round-tripping
-- through `toInt?` — is about Lean's stdlib decimal codec (whose parse side
-- ships no lemmas), so it's taken as a hypothesis rather than reproved.
theorem readAtom_int (t : String) (n : Int) (c : Char) (cs : List Char)
    (htl : t.toList = c :: cs) (hq : c ≠ '"') (hcl : c ≠ ':')
    (hnil : t ≠ "nil") (htrue : t ≠ "true") (hfalse : t ≠ "false")
    (hi : t.toInt? = some n) : readAtom t = .ok (.int n) := by
  simp only [readAtom, htl]
  split <;> simp_all

end Reader
