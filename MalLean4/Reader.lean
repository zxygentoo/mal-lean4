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

/-! ### Parser round-trip

`readForm` inverts a token-level printer on the "literal" fragment —
`nil`/`bool`/`kw` and nested lists/vectors. (The remaining leaf atoms
`int`/`sym` would each need their own "token ≠ every special token" dispatch
lemma, and `int`/`str` add stdlib-codec/escaping caveats; addable later.
This is the recursive heart: the parser reconstructs nested structure from
the token stream.) -/

-- Token-level printer for the fragment (the string printer composed with a
-- correct tokenizer would produce these tokens).
mutual
private def printTokens : MalVal → List String
  | .nil        => ["nil"]
  | .bool true  => ["true"]
  | .bool false => ["false"]
  | .kw s       => [":" ++ s]
  | .list xs    => "(" :: (printTokensList xs ++ [")"])
  | .vec xs     => "[" :: (printTokensList xs ++ ["]"])
  | _           => []
private def printTokensList : List MalVal → List String
  | []      => []
  | x :: xs => printTokens x ++ printTokensList xs
end

mutual
private def isLit : MalVal → Bool
  | .nil | .bool _ | .kw _ => true
  | .list xs | .vec xs     => isLitList xs
  | _                      => false
private def isLitList : List MalVal → Bool
  | []      => true
  | x :: xs => isLit x && isLitList xs
end

-- Fuel a parse needs: a leaf takes 1; a list takes one (for the `(`) above
-- whatever its `readSeq` needs, and `readSeq` over `xs` takes one per step
-- above the max of its elements (since `readForm`/`readSeq` share fuel `f`).
mutual
private def cost : MalVal → Nat
  | .list xs | .vec xs => costList xs + 1
  | _                  => 1
private def costList : List MalVal → Nat
  | []      => 1
  | x :: xs => max (cost x) (costList xs) + 1
end

-- A literal's first token is never `)`, so `readSeq` doesn't mistake an
-- element for the closer.
private theorem printTokens_head (v : MalVal) (hl : isLit v = true) :
    ∃ t ts, printTokens v = t :: ts ∧ t ≠ ")" ∧ t ≠ "]" := by
  cases v
  case nil    => exact ⟨_, _, rfl, by decide, by decide⟩
  case bool b => cases b <;> exact ⟨_, _, rfl, by decide, by decide⟩
  case kw s   => refine ⟨_, _, rfl, ?_, ?_⟩ <;>
                   (intro h; have := congrArg String.toList h; simp at this)
  case list _ => exact ⟨_, _, rfl, by decide, by decide⟩
  case vec _  => exact ⟨_, _, rfl, by decide, by decide⟩
  all_goals simp [isLit] at hl

-- A keyword token `":" ++ s` is none of the structural/quote tokens, so
-- `readForm` falls through to `readAtom`, which yields the keyword. Each
-- non-matching arm is refuted from the token's leading `:`.
private theorem readForm_kw (f : Nat) (s : String) (rest : List String) :
    readForm (f+1) ((":" ++ s) :: rest) = .ok (.kw s, rest) := by
  unfold readForm
  split <;> rename_i heq <;>
    first
    | (injection heq with hh ht; subst hh; subst ht; rw [readAtom_kw]; rfl)
    | (injection heq with hh _; exact absurd (congrArg String.toList hh) (by simp))
    | simp at heq

mutual
-- The parser inverts the token printer (with leftover `rest` untouched),
-- given enough fuel.
private theorem readForm_round : ∀ (v : MalVal) (rest : List String) (fuel : Nat),
    isLit v = true → cost v ≤ fuel →
    readForm fuel (printTokens v ++ rest) = .ok (v, rest)
  | .nil,        rest, fuel, _, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp only [cost] at hf; omega⟩
    simp [printTokens, readForm, readAtom]; rfl
  | .bool true,  rest, fuel, _, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp only [cost] at hf; omega⟩
    simp [printTokens, readForm, readAtom]; rfl
  | .bool false, rest, fuel, _, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp only [cost] at hf; omega⟩
    simp [printTokens, readForm, readAtom]; rfl
  | .kw s,       rest, fuel, _, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp only [cost] at hf; omega⟩
    simpa [printTokens] using readForm_kw f s rest
  | .list xs,    rest, fuel, hl, hf => by
    simp only [cost] at hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hll : isLitList xs = true := by simpa [isLit] using hl
    simp only [printTokens, List.cons_append, List.append_assoc, List.nil_append, readForm]
    have h := readSeq_round xs #[] rest f ")" .list hll (by omega) (Or.inl rfl)
    simpa using h
  | .vec xs,     rest, fuel, hl, hf => by
    simp only [cost] at hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hll : isLitList xs = true := by simpa [isLit] using hl
    simp only [printTokens, List.cons_append, List.append_assoc, List.nil_append, readForm]
    have h := readSeq_round xs #[] rest f "]" .vec hll (by omega) (Or.inr rfl)
    simpa using h
  | .int _, _, _, hl, _ | .str _, _, _, hl, _ | .sym _, _, _, hl, _
  | .map _, _, _, hl, _ | .fn _, _, _, hl, _ | .atom _, _, _, hl, _
  | .withMeta _ _, _, _, hl, _ => by
    simp [isLit] at hl

private theorem readSeq_round : ∀ (xs : List MalVal) (acc : Array MalVal)
    (rest : List String) (fuel : Nat) (close : String) (wrap : List MalVal → MalVal),
    isLitList xs = true → costList xs ≤ fuel → (close = ")" ∨ close = "]") →
    readSeq fuel acc close wrap (printTokensList xs ++ close :: rest)
      = .ok (wrap (acc.toList ++ xs), rest)
  | [],      acc, rest, fuel, close, wrap, _, hf, _ => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp only [costList] at hf; omega⟩
    simp [printTokensList, readSeq]
  | x :: xs, acc, rest, fuel, close, wrap, hl, hf, hclose => by
    simp only [isLitList, Bool.and_eq_true] at hl
    obtain ⟨hlx, hlxs⟩ := hl
    simp only [costList] at hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨t, ts, hpt, hne1, hne2⟩ := printTokens_head x hlx
    have hnec : t ≠ close := by rcases hclose with rfl | rfl <;> assumption
    simp only [printTokensList, hpt, List.cons_append, readSeq]
    rw [if_neg (by simp [hnec])]
    rw [show t :: (ts ++ printTokensList xs ++ close :: rest)
          = printTokens x ++ (printTokensList xs ++ close :: rest) by
        rw [hpt]; simp [List.append_assoc]]
    rw [readForm_round x _ f hlx (by omega)]
    show readSeq f (acc.push x) close wrap (printTokensList xs ++ close :: rest)
         = Except.ok (wrap (acc.toList ++ x :: xs), rest)
    rw [readSeq_round xs (acc.push x) rest f close wrap hlxs (by omega) hclose]
    simp [Array.toList_push, List.append_assoc]
end

-- Headline: on the literal fragment, `readForm` parses the token printer's
-- output back to the original value with no tokens left over.
theorem readForm_printTokens (v : MalVal) (hl : isLit v = true) :
    readForm (cost v) (printTokens v) = .ok (v, []) := by
  have h := readForm_round v [] (cost v) hl (Nat.le_refl _)
  simpa using h

-- Keywords round-trip even nested among the other literals.
example :
    let v : MalVal := .list [.kw "a", .nil, .vec [.bool true, .kw "b"]]
    readForm (cost v) (printTokens v) = .ok (v, []) := by
  intro v; exact readForm_printTokens _ (by decide)

end Reader
