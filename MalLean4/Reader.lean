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

-- Total via a `fuel` budget that drops on every call, so recursion is
-- structural rather than `partial`. Plain termination fails here: `readSeq`
-- calls `readForm` on the *same* token list and then recurses on whatever's
-- left, so termination depends on the parse consuming input — which the
-- checker can't see. `readStr` passes `2 * toks.length + 1` (see there),
-- enough that the `out of fuel` arms never fire on real input.
mutual
  def readForm : Nat → List String → Except String (MalVal × List String)
    | 0,   _            => .error "reader out of fuel"
    | _+1, []           => .error "unexpected EOF"
    | f+1, "("  :: rest => readSeq f #[] ")" .list rest
    | f+1, "["  :: rest => readSeq f #[] "]" .vec  rest
    | f+1, "{"  :: rest => readMap f #[] rest
    | _+1, ")"  :: _    => .error "unexpected ')'"
    | _+1, "]"  :: _    => .error "unexpected ']'"
    | _+1, "}"  :: _    => .error "unexpected '}'"
    | f+1, "'"  :: rest => quoteMacro f "quote"          rest
    | f+1, "`"  :: rest => quoteMacro f "quasiquote"     rest
    | f+1, "~"  :: rest => quoteMacro f "unquote"        rest
    | f+1, "~@" :: rest => quoteMacro f "splice-unquote" rest
    | f+1, "@"  :: rest => quoteMacro f "deref"          rest
    | f+1, "^"  :: rest => do
      let (metaForm, rest')   ← readForm f rest
      let (valueForm, rest'') ← readForm f rest'
      .ok (.list [.sym "with-meta", valueForm, metaForm], rest'')
    | _+1, t    :: rest => do
      let atom ← readAtom t
      .ok (atom, rest)

  def readSeq : Nat → Array MalVal → String → (List MalVal → MalVal) →
      List String → Except String (MalVal × List String)
    | 0,   _,   _,     _,    _         => .error "reader out of fuel"
    | _+1, _,   close, _,    []        => .error s!"unbalanced: expected '{close}'"
    | f+1, acc, close, wrap, t :: rest =>
      if t == close then .ok (wrap acc.toList, rest)
      else do
        let (form, rest') ← readForm f (t :: rest)
        readSeq f (acc.push form) close wrap rest'

  def readMap : Nat → Array (MalVal × MalVal) →
      List String → Except String (MalVal × List String)
    | 0,   _,   _           => .error "reader out of fuel"
    | _+1, _,   []          => .error "unbalanced: expected '}'"
    | _+1, acc, "}" :: rest => .ok (.map (MalVal.dedupMap acc.toList), rest)
    | f+1, acc, toks        => do
      let (key, rest)  ← readForm f toks
      let (val, rest') ← readForm f rest
      readMap f (acc.push (key, val)) rest'

  def quoteMacro : Nat → String → List String →
      Except String (MalVal × List String)
    | 0,   _,    _    => .error "reader out of fuel"
    | f+1, name, toks => do
      let (form, rest) ← readForm f toks
      .ok (.list [.sym name, form], rest)
end

-- Returns the token (always starting with `"`) and the rest of the
-- input. An unterminated literal returns with no closing quote so the
-- parser can emit "unbalanced string" rather than silently accept it.
def readStringToken (chars : List Char) (acc : List Char) :
    String × List Char :=
  match chars with
  | []                => (String.ofList ('"' :: acc.reverse), [])
  | '"' :: rest       => (String.ofList ('"' :: acc.reverse ++ ['"']), rest)
  | '\\' :: c :: rest => readStringToken rest (c :: '\\' :: acc)
  | c :: rest         => readStringToken rest (c :: acc)

-- Fuel like the parser; `go` consumes ≥1 char per call, so `input.length + 1`
-- always suffices and the `0` arm never fires on real input.
def tokenize (input : String) : List String :=
  go (input.length + 1) input.toList
where
  go : Nat → List Char → List String
    | 0,   _                  => []
    | _+1, []                 => []
    | f+1, ';' :: rest        => go f (rest.dropWhile (· != '\n'))
    | f+1, '"' :: rest        =>
      let (tok, rest') := readStringToken rest []
      tok :: go f rest'
    | f+1, '~' :: '@' :: rest => "~@" :: go f rest
    | f+1, c :: rest          =>
      if isSeparator c then go f rest
      else if isStandalone c then String.singleton c :: go f rest
      else
        let (taken, rest') := (c :: rest).span isTokenChar
        String.ofList taken :: go f rest'

-- `.ok none` for whitespace/comment-only input; `.ok (some form)` for a
-- parsed expression; `.error msg` for parse failures.
public def readStr (s : String) : Except String (Option MalVal) := do
  match tokenize s with
  | [] => .ok none
  | toks =>
    -- `2 * length + 1`: each token costs at most one consume step plus one
    -- wrapper level (a `(`/`{`/quote that recurses without eating a token).
    let (form, _) ← readForm (2 * toks.length + 1) toks
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
