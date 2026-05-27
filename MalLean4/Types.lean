module

namespace Types

mutual

public inductive MalVal where
  | nil
  | bool : Bool → MalVal
  | int  : Int → MalVal
  | str  : String → MalVal
  | kw   : String → MalVal
  | sym  : String → MalVal
  | list : List MalVal → MalVal
  | vec  : List MalVal → MalVal
  | map  : List (MalVal × MalVal) → MalVal
  | fn   : Fn → MalVal
  | atom : Nat → MalVal
  -- The printer, equality, and type predicates strip this wrapper via
  -- `MalVal.strip`; only `meta`, `with-meta`, and `apply` see it.
  | withMeta : MalVal → MalVal → MalVal

public inductive Fn where
  | builtin : String → Fn
  | lambda  : Lambda → Fn

-- `outerEnvId` is a `Nat` id into `Env.store`, not a direct `Env`: Lean's
-- strict positivity rejects `Lambda { outerEnv : Env }` because `Env`
-- chains back through `MalVal`. The indirection also gives us lexical
-- scope and live `def!` updates that a value snapshot couldn't.
public structure Lambda where
  public mk ::
  public isMacro  : Bool := false
  public params   : List String
  public restParam : Option String := none
  public body     : MalVal
  public outerEnvId : Nat

end

-- `EIO MalVal` not `ExceptT MalVal IO`: one-layer error shape halves
-- per-bind dispatch cost. `MalVal`-typed errors let `try*` catch
-- user-thrown values structurally.
public abbrev MalIO := EIO MalVal

public instance : Coe String MalVal := ⟨MalVal.str⟩

public instance : MonadLift IO MalIO where
  monadLift m := EIO.adapt (fun e => MalVal.str s!"{e}") m

-- Only `nil` and `false` are falsy; 0, "", and `()` are truthy. Meta is
-- transparent here as in `equal`/the printer, so unwrap before deciding.
public def MalVal.isTruthy : MalVal → Bool
  | .nil          => false
  | .bool false   => false
  | .withMeta v _ => v.isTruthy
  | _ => true

-- Strips meta from both sides. Lists and vectors compare equal across
-- constructors; maps as unordered key-value sets; atoms by id. Total via
-- `termination_by sizeOf a + sizeOf b`: neither argument decreases alone
-- (the meta cases shrink different sides), but their sum always does.
mutual
public def MalVal.equal (a b : MalVal) : Bool :=
  match a, b with
  | .withMeta v _, b => MalVal.equal v b
  | a, .withMeta v _ => MalVal.equal a v
  | .nil,     .nil     => true
  | .bool a,  .bool b  => a == b
  | .int a,   .int b   => a == b
  | .sym a,   .sym b   => a == b
  | .str a,   .str b   => a == b
  | .kw a,    .kw b    => a == b
  | .atom a,  .atom b  => a == b
  | .list xs, .list ys => MalVal.listEqual xs ys
  | .vec xs,  .vec ys  => MalVal.listEqual xs ys
  | .list xs, .vec ys  => MalVal.listEqual xs ys
  | .vec xs,  .list ys => MalVal.listEqual xs ys
  | .map xs,  .map ys  => xs.length == ys.length && MalVal.mapEqual ys xs
  | _,        _        => false
  termination_by sizeOf a + sizeOf b

private def MalVal.listEqual : List MalVal → List MalVal → Bool
  | [],      []      => true
  | x :: xs, y :: ys => MalVal.equal x y && MalVal.listEqual xs ys
  | _,       _       => false
  termination_by xs ys => sizeOf xs + sizeOf ys

-- Explicit-recursion equivalent of the old `find?`-then-compare: scan for
-- the first entry whose key `equal`s `k`, compare its value to `v`. Keeping
-- the value comparison on a structural subterm is what makes it terminate.
private def MalVal.mapLookup (k v : MalVal) : List (MalVal × MalVal) → Bool
  | []               => false
  | (k', v') :: rest =>
    if MalVal.equal k k' then MalVal.equal v v' else MalVal.mapLookup k v rest
  termination_by xs => sizeOf k + sizeOf v + sizeOf xs

private def MalVal.mapEqual (ys : List (MalVal × MalVal)) :
    List (MalVal × MalVal) → Bool
  | []             => true
  | (k, v) :: rest => MalVal.mapLookup k v ys && MalVal.mapEqual ys rest
  termination_by xs => sizeOf ys + sizeOf xs
end

public def MalVal.strip : MalVal → MalVal
  | .withMeta v _ => v.strip
  | v             => v

public def MalVal.getMeta : MalVal → MalVal
  | .withMeta _ m => m
  | _             => .nil

public def MalVal.isSequential : MalVal → Bool
  | .list _ => true
  | .vec _  => true
  | .withMeta v _ => v.isSequential
  | _       => false

public def MalVal.toList? : MalVal → Option (List MalVal)
  | .list xs       => some xs
  | .vec xs        => some xs
  | .withMeta v _  => v.toList?
  | _              => none

-- The new module system keeps structure field projections private even
-- when fields are declared `public`, so cross-module callers need these
-- wrappers.
public def Lambda.isMacro? (l : Lambda) : Bool := l.isMacro
public def Lambda.outerId (l : Lambda) : Nat := l.outerEnvId

-- Needed so partial list operations (`getLast!`, `head!`) type-check;
-- value irrelevant.
public instance : Inhabited MalVal := ⟨.nil⟩

-- Last-write-wins. Keeps map literals and `hash-map`/`assoc` results
-- free of duplicate keys.
public def MalVal.dedupMap (pairs : List (MalVal × MalVal)) :
    List (MalVal × MalVal) :=
  pairs.foldl (fun acc (k, v) =>
    if acc.any (fun (k', _) => MalVal.equal k k') then
      acc.map fun (k', v') => if MalVal.equal k k' then (k', v) else (k', v')
    else
      acc ++ [(k, v)]) []

/-! ## Proofs

Properties of the pure, total core. Co-located with the definitions (rather
than in a separate module) so the helpers stay `private` and no `@[expose]`
is needed; all module-private. -/

-- `strip` is a normal form: applying it twice is the same as once...
private theorem strip_idem : ∀ v : MalVal, v.strip.strip = v.strip
  | .withMeta v _ => strip_idem v
  | .nil | .bool _ | .int _ | .str _ | .kw _ | .sym _
  | .list _ | .vec _ | .map _ | .fn _ | .atom _ => rfl

-- ...and its result is never itself a `.withMeta` wrapper.
private theorem strip_no_meta : ∀ (v a b : MalVal), v.strip ≠ .withMeta a b
  | .withMeta v _, a, b => by simp only [MalVal.strip]; exact strip_no_meta v a b
  | .nil, _, _ | .bool _, _, _ | .int _, _, _ | .str _, _, _
  | .kw _, _, _ | .sym _, _, _ | .list _, _, _ | .vec _, _, _
  | .map _, _, _ | .fn _, _, _ | .atom _, _, _ => by simp [MalVal.strip]

-- `isTruthy` unwraps meta (like `equal` and the printer), so a meta-wrapped
-- value has the same truthiness as its bare form, at any nesting depth.
-- These guard against regressing that wrap-transparency.
example : MalVal.isTruthy .nil = false := rfl
example : MalVal.isTruthy (.bool false) = false := rfl
example : MalVal.isTruthy (.withMeta .nil (.kw "x")) = false := rfl
example : MalVal.isTruthy (.withMeta (.bool false) .nil) = false := rfl
example : MalVal.isTruthy (.withMeta (.withMeta .nil .nil) .nil) = false := rfl
example : MalVal.isTruthy (.withMeta (.int 0) .nil) = true := rfl

private theorem pairwise_snoc {α} {R : α → α → Prop} {l : List α} {x : α}
    (hp : l.Pairwise R) (hx : ∀ a ∈ l, R a x) : (l ++ [x]).Pairwise R := by
  induction l with
  | nil => exact List.Pairwise.cons (by intro a ha; simp at ha) List.Pairwise.nil
  | cons a t ih =>
    cases hp with
    | cons ha ht =>
      rw [List.cons_append]
      refine List.Pairwise.cons ?_ (ih ht (fun b hb => hx b (List.mem_cons_of_mem a hb)))
      intro b hb
      rw [List.mem_append] at hb
      cases hb with
      | inl hbl => exact ha b hbl
      | inr hbr => rw [List.mem_singleton] at hbr; subst hbr; exact hx a List.mem_cons_self

private def dstep (acc : List (MalVal × MalVal)) (kv : MalVal × MalVal) :
    List (MalVal × MalVal) :=
  if acc.any (fun p => MalVal.equal kv.1 p.1)
  then acc.map (fun p => if MalVal.equal kv.1 p.1 then (p.1, kv.2) else p)
  else acc ++ [kv]

private theorem dedupMap_eq (ps : List (MalVal × MalVal)) :
    MalVal.dedupMap ps = ps.foldl dstep [] := by
  unfold MalVal.dedupMap dstep; rfl

private theorem dstep_pairwise (l acc : List (MalVal × MalVal))
    (h : (acc.map Prod.fst).Pairwise (fun a b => ¬ MalVal.equal b a)) :
    ((l.foldl dstep acc).map Prod.fst).Pairwise (fun a b => ¬ MalVal.equal b a) := by
  induction l generalizing acc with
  | nil => simpa using h
  | cons kv rest ih =>
    rw [List.foldl_cons]
    apply ih
    unfold dstep
    by_cases hany : (acc.any (fun p => MalVal.equal kv.1 p.1)) = true
    · rw [if_pos hany]
      have hkeys :
          (acc.map (fun p => if MalVal.equal kv.1 p.1 then (p.1, kv.2) else p)).map Prod.fst
            = acc.map Prod.fst := by
        rw [List.map_map]
        apply List.map_congr_left
        intro p _
        by_cases hp : MalVal.equal kv.1 p.1 = true <;> simp [Function.comp, hp]
      rw [hkeys]; exact h
    · rw [if_neg hany, List.map_append]
      simp only [List.map_cons, List.map_nil]
      have hfalse : acc.any (fun p => MalVal.equal kv.1 p.1) = false := by
        simp only [Bool.not_eq_true] at hany; exact hany
      apply pairwise_snoc h
      intro a ha
      rw [List.mem_map] at ha
      obtain ⟨p, hp, rfl⟩ := ha
      intro hcontra
      have : acc.any (fun p => MalVal.equal kv.1 p.1) = true :=
        List.any_eq_true.mpr ⟨p, hp, hcontra⟩
      rw [this] at hfalse
      exact Bool.noConfusion hfalse

-- The map representation's load-bearing invariant: `dedupMap` produces a
-- key list in which no key `equal`s an earlier one (read left-to-right,
-- the order the reader and `assoc`/`hash-map` build them).
private theorem dedupMap_keys_pairwise (ps : List (MalVal × MalVal)) :
    ((MalVal.dedupMap ps).map Prod.fst).Pairwise (fun a b => ¬ MalVal.equal b a) := by
  rw [dedupMap_eq]
  exact dstep_pairwise ps [] (by simp)

-- Folding `dstep` over a list whose keys are already pairwise-distinct just
-- appends each entry (no merge ever fires), leaving the list unchanged.
private theorem foldl_dstep_append : ∀ (acc L : List (MalVal × MalVal)),
    ((acc ++ L).map Prod.fst).Pairwise (fun a b => ¬ MalVal.equal b a) →
    L.foldl dstep acc = acc ++ L
  | acc, [],           _ => by simp
  | acc, (k, v) :: xs, h => by
    have h' : (acc.map Prod.fst ++ (k :: xs.map Prod.fst)).Pairwise
        (fun a b => ¬ MalVal.equal b a) := by simpa using h
    have hcross := (List.pairwise_append.mp h').2.2
    have hno : acc.any (fun p => MalVal.equal k p.1) = false := by
      cases hcase : acc.any (fun p => MalVal.equal k p.1) with
      | false => rfl
      | true =>
        rw [List.any_eq_true] at hcase
        obtain ⟨p, hp, hpk⟩ := hcase
        exact absurd hpk (hcross p.1 (List.mem_map_of_mem hp) k List.mem_cons_self)
    rw [List.foldl_cons, show dstep acc (k, v) = acc ++ [(k, v)] by simp [dstep, hno]]
    rw [foldl_dstep_append (acc ++ [(k, v)]) xs (by simpa [List.append_assoc] using h)]
    simp [List.append_assoc]

-- `dedupMap` is idempotent: its output already has distinct keys, so
-- re-deduping appends each entry unchanged.
private theorem dedupMap_idem (ps : List (MalVal × MalVal)) :
    MalVal.dedupMap (MalVal.dedupMap ps) = MalVal.dedupMap ps := by
  rw [dedupMap_eq (MalVal.dedupMap ps),
      foldl_dstep_append [] (MalVal.dedupMap ps) (by simpa using dedupMap_keys_pairwise ps),
      List.nil_append]

/-! Reflexivity of `equal`. Not unconditional: a function never `equal`s
anything (even itself), and a *duplicate-key* map compares its later entry
against an earlier entry's value. So `=` is reflexive exactly on the "data
fragment": no functions, and every map distinct-keyed (which `dedupMap`
guarantees for every map the interpreter builds). -/

example : MalVal.equal (.fn (.builtin "f")) (.fn (.builtin "f")) = false := by
  simp [MalVal.equal]

example :
    MalVal.equal (.map [(.int 1, .int 10), (.int 1, .int 20)])
                 (.map [(.int 1, .int 10), (.int 1, .int 20)]) = false := by
  simp [MalVal.equal, MalVal.mapEqual, MalVal.mapLookup]

-- Keys pairwise distinct: no key `equal`s an earlier one — the Bool form
-- of `dedupMap_keys_pairwise`.
private def keysDistinct : List (MalVal × MalVal) → Bool
  | []             => true
  | (k, _) :: rest => rest.all (fun p => !MalVal.equal p.1 k) && keysDistinct rest

-- The fragment on which `=` is reflexive: no functions, every map distinct-
-- keyed with reflexive children. The `…List`/`…Pairs` helpers spell out the
-- element traversals so the nested recursion is structural.
mutual
private def reflEq : MalVal → Bool
  | .fn _         => false
  | .map xs       => keysDistinct xs && reflEqPairs xs
  | .list xs      => reflEqList xs
  | .vec xs       => reflEqList xs
  | .withMeta v _ => reflEq v
  | _             => true
private def reflEqList : List MalVal → Bool
  | []      => true
  | x :: xs => reflEq x && reflEqList xs
private def reflEqPairs : List (MalVal × MalVal) → Bool
  | []             => true
  | (k, v) :: rest => reflEq k && reflEq v && reflEqPairs rest
end

private theorem reflEqList_iff {xs : List MalVal} :
    reflEqList xs = true ↔ ∀ x ∈ xs, reflEq x = true := by
  induction xs with
  | nil          => simp [reflEqList]
  | cons x t ih  => simp [reflEqList, ih]

private theorem reflEqPairs_iff {xs : List (MalVal × MalVal)} :
    reflEqPairs xs = true ↔ ∀ p ∈ xs, reflEq p.1 = true ∧ reflEq p.2 = true := by
  induction xs with
  | nil         => simp [reflEqPairs]
  | cons p t ih => obtain ⟨k, v⟩ := p; simp [reflEqPairs, ih]

-- Meta on the right is transparent: stripping it never changes `equal`.
private theorem equal_strip_right : ∀ a v m : MalVal,
    MalVal.equal a (.withMeta v m) = MalVal.equal a v
  | .withMeta a' _, v, m => by simp only [MalVal.equal]; exact equal_strip_right a' v m
  | .nil, _, _ | .bool _, _, _ | .int _, _, _ | .str _, _, _ | .kw _, _, _
  | .sym _, _, _ | .atom _, _, _ | .list _, _, _ | .vec _, _, _
  | .map _, _, _ | .fn _, _, _ => by simp only [MalVal.equal]
  termination_by a => sizeOf a

private theorem listEqual_refl {xs : List MalVal}
    (H : ∀ x ∈ xs, MalVal.equal x x = true) : MalVal.listEqual xs xs = true := by
  induction xs with
  | nil => simp [MalVal.listEqual]
  | cons x t ih =>
    have h2 := ih (fun y hy => H y (List.mem_cons_of_mem x hy))
    simp [MalVal.listEqual, H x List.mem_cons_self, h2]

-- With distinct keys, `mapLookup` finds an in-list pair: no earlier entry's
-- key `equal`s `k` (distinctness), so the scan reaches `(k, v)` itself.
private theorem mapLookup_self (k v : MalVal)
    (hk : MalVal.equal k k = true) (hv : MalVal.equal v v = true) :
    ∀ L : List (MalVal × MalVal), (k, v) ∈ L → keysDistinct L = true →
      MalVal.mapLookup k v L = true
  | [],              hmem, _  => by simp at hmem
  | (k0, _) :: rest, hmem, hd => by
    simp only [keysDistinct, Bool.and_eq_true] at hd
    simp only [MalVal.mapLookup]
    by_cases hkk0 : MalVal.equal k k0 = true
    · rw [if_pos hkk0]
      rcases List.mem_cons.mp hmem with heq | hmemrest
      · simp only [Prod.mk.injEq] at heq; obtain ⟨_, rfl⟩ := heq; exact hv
      · have hb := (List.all_eq_true.mp hd.1) (k, v) hmemrest
        simp [hkk0] at hb
    · rw [if_neg hkk0]
      rcases List.mem_cons.mp hmem with heq | hmemrest
      · simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, _⟩ := heq; exact absurd hk hkk0
      · exact mapLookup_self k v hk hv rest hmemrest hd.2
  termination_by L => sizeOf L

-- Iterate `mapLookup` over `sub`, looking each entry up in the fixed `ys`.
private theorem mapEqual_go (ys : List (MalVal × MalVal)) :
    ∀ sub : List (MalVal × MalVal),
      (∀ p ∈ sub, MalVal.mapLookup p.1 p.2 ys = true) → MalVal.mapEqual ys sub = true
  | [],             _ => by simp [MalVal.mapEqual]
  | (k, v) :: rest, H => by
    simp only [MalVal.mapEqual, Bool.and_eq_true]
    exact ⟨H (k, v) List.mem_cons_self,
           mapEqual_go ys rest (fun q hq => H q (List.mem_cons_of_mem _ hq))⟩
  termination_by sub => sizeOf sub

private theorem equal_refl : ∀ a : MalVal, reflEq a = true → MalVal.equal a a = true
  | .nil, _ | .bool _, _ | .int _, _ | .str _, _
  | .kw _, _ | .sym _, _ | .atom _, _ => by simp [MalVal.equal]
  | .fn _, h => by simp [reflEq] at h
  | .list xs, h => by
    simp only [reflEq] at h
    rw [reflEqList_iff] at h
    simp only [MalVal.equal]
    exact listEqual_refl (fun x hx => equal_refl x (h x hx))
  | .vec xs, h => by
    simp only [reflEq] at h
    rw [reflEqList_iff] at h
    simp only [MalVal.equal]
    exact listEqual_refl (fun x hx => equal_refl x (h x hx))
  | .map xs, h => by
    simp only [reflEq, Bool.and_eq_true] at h
    obtain ⟨hdist, hpairs⟩ := h
    rw [reflEqPairs_iff] at hpairs
    simp only [MalVal.equal]
    rw [Bool.and_eq_true]
    refine ⟨by simp, mapEqual_go xs xs (fun p hp => ?_)⟩
    obtain ⟨k, v⟩ := p
    exact mapLookup_self k v
      (equal_refl k (hpairs (k, v) hp).1) (equal_refl v (hpairs (k, v) hp).2)
      xs hp hdist
  | .withMeta v m, h => by
    simp only [reflEq] at h
    have step1 : MalVal.equal (.withMeta v m) (.withMeta v m)
               = MalVal.equal v (.withMeta v m) := by simp only [MalVal.equal]
    rw [step1, equal_strip_right v v m]
    exact equal_refl v h
  termination_by a => sizeOf a
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (have h := List.sizeOf_lt_of_mem (by assumption); omega)
      | (have h := List.sizeOf_lt_of_mem (by assumption)
         simp only [Prod.mk.sizeOf_spec] at h; omega)

-- A distinct-key map IS reflexive (contrast the duplicate-key counterexample).
example : MalVal.equal (.map [(.kw "a", .int 1), (.kw "b", .int 2)])
                       (.map [(.kw "a", .int 1), (.kw "b", .int 2)]) = true := by
  apply equal_refl; simp [reflEq, keysDistinct, reflEqPairs, MalVal.equal]

/-! ### Meta transparency

Meta is invisible to every observer: `equal`, `isTruthy`, `isSequential`,
and `toList?` all give the same answer on a value and its `strip`. (The
existing `equal_strip_right` strips one wrapper; these strip the whole
chain on both sides.) -/

-- Stripping the entire meta chain off the left argument never changes `equal`
-- (the `.withMeta v _, b` match arm fires unconditionally on a meta left).
private theorem equal_strip_left_full : ∀ (a b : MalVal),
    MalVal.equal a.strip b = MalVal.equal a b
  | .withMeta v _, b => by
    simp only [MalVal.strip, MalVal.equal]; exact equal_strip_left_full v b
  | .nil, _ | .bool _, _ | .int _, _ | .str _, _ | .kw _, _ | .sym _, _
  | .atom _, _ | .list _, _ | .vec _, _ | .map _, _ | .fn _, _ => by simp [MalVal.strip]
  termination_by a => sizeOf a

-- Same on the right, iterating the one-step `equal_strip_right` down the chain.
private theorem equal_strip_right_full : ∀ (a b : MalVal),
    MalVal.equal a b.strip = MalVal.equal a b
  | a, .withMeta v m => by
    simp only [MalVal.strip]
    rw [equal_strip_right_full a v]; exact (equal_strip_right a v m).symm
  | a, .nil | a, .bool _ | a, .int _ | a, .str _ | a, .kw _ | a, .sym _
  | a, .atom _ | a, .list _ | a, .vec _ | a, .map _ | a, .fn _ => by simp [MalVal.strip]
  termination_by _ b => sizeOf b

-- `equal` depends only on the stripped values: meta is fully transparent.
private theorem equal_strip (a b : MalVal) :
    MalVal.equal a b = MalVal.equal a.strip b.strip := by
  rw [equal_strip_left_full, equal_strip_right_full]

private theorem isTruthy_strip : ∀ v : MalVal, v.strip.isTruthy = v.isTruthy
  | .withMeta v _ => by
    simp only [MalVal.strip, MalVal.isTruthy]; exact isTruthy_strip v
  | .nil | .bool _ | .int _ | .str _ | .kw _ | .sym _
  | .atom _ | .list _ | .vec _ | .map _ | .fn _ => by simp [MalVal.strip]

private theorem isSequential_strip : ∀ v : MalVal, v.strip.isSequential = v.isSequential
  | .withMeta v _ => by
    simp only [MalVal.strip, MalVal.isSequential]; exact isSequential_strip v
  | .nil | .bool _ | .int _ | .str _ | .kw _ | .sym _
  | .atom _ | .list _ | .vec _ | .map _ | .fn _ => by simp [MalVal.strip]

private theorem toList?_strip : ∀ v : MalVal, v.strip.toList? = v.toList?
  | .withMeta v _ => by
    simp only [MalVal.strip, MalVal.toList?]; exact toList?_strip v
  | .nil | .bool _ | .int _ | .str _ | .kw _ | .sym _
  | .atom _ | .list _ | .vec _ | .map _ | .fn _ => by simp [MalVal.strip]

/-! ### Type-predicate consistency

`isSequential` and `toList?` decide the same thing (both unwrap meta and accept
exactly `list`/`vec`), and a sequence is always truthy. -/

private theorem isSequential_eq_isSome_toList? : ∀ v : MalVal,
    v.isSequential = v.toList?.isSome
  | .withMeta v _ => by
    simp only [MalVal.isSequential, MalVal.toList?]; exact isSequential_eq_isSome_toList? v
  | .nil | .bool _ | .int _ | .str _ | .kw _ | .sym _
  | .map _ | .fn _ | .atom _ | .list _ | .vec _ => rfl

private theorem isTruthy_of_isSequential : ∀ v : MalVal,
    v.isSequential = true → v.isTruthy = true
  | .withMeta v _, h => by
    simp only [MalVal.isSequential] at h
    simp only [MalVal.isTruthy]; exact isTruthy_of_isSequential v h
  | .list _, _ | .vec _, _ => rfl
  | .nil, h | .bool _, h | .int _, h | .str _, h | .kw _, h
  | .sym _, h | .map _, h | .fn _, h | .atom _, h => by simp [MalVal.isSequential] at h

/-! ### Symmetry of `equal`

`equal` is **not** symmetric in general: the map case folds over its second
argument (`mapEqual ys xs`), so a duplicate-key map can be `equal` to another
without the reverse holding. Compare `equal_refl`'s duplicate-key failure. -/

example :
    MalVal.equal (.map [(.int 1, .int 10), (.int 1, .int 10)])
                 (.map [(.int 1, .int 10), (.int 2, .int 10)]) = true
  ∧ MalVal.equal (.map [(.int 1, .int 10), (.int 2, .int 10)])
                 (.map [(.int 1, .int 10), (.int 1, .int 10)]) = false := by
  constructor <;> simp [MalVal.equal, MalVal.mapEqual, MalVal.mapLookup]

-- The map-free fragment, where symmetry holds unconditionally. (Maps need a
-- recursive distinct-key side condition *and* a finite-counting argument that
-- the two key sets biject — entangled with `equal` transitivity; left open.)
mutual
private def mapFree : MalVal → Bool
  | .map _             => false
  | .list xs | .vec xs => mapFreeList xs
  | .withMeta v _      => mapFree v
  | _                  => true
private def mapFreeList : List MalVal → Bool
  | []      => true
  | x :: xs => mapFree x && mapFreeList xs
end

private theorem mapFreeList_iff {xs : List MalVal} :
    mapFreeList xs = true ↔ ∀ x ∈ xs, mapFree x = true := by
  induction xs with
  | nil         => simp [mapFreeList]
  | cons x t ih => simp [mapFreeList, ih]

-- Sequence symmetry given elementwise symmetry — the real content behind the
-- `list`/`vec` cases of `equal_symm`.
private theorem listEqual_symm : ∀ (xs ys : List MalVal),
    (∀ x ∈ xs, ∀ y ∈ ys, MalVal.equal x y = MalVal.equal y x) →
    MalVal.listEqual xs ys = MalVal.listEqual ys xs
  | [],      [],     _ => rfl
  | [],      _ :: _, _ => by simp [MalVal.listEqual]
  | _ :: _,  [],     _ => by simp [MalVal.listEqual]
  | x :: xs, y :: ys, H => by
    simp only [MalVal.listEqual]
    rw [H x List.mem_cons_self y List.mem_cons_self,
        listEqual_symm xs ys (fun a ha b hb =>
          H a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem y hb))]

-- `==` is symmetric on any lawful `BEq` (core's `beq_comm` isn't in scope
-- here). Closes the matching-scalar cases of `equal_symm_step`.
private theorem beq_symm {α} [BEq α] [LawfulBEq α] (a b : α) : (a == b) = (b == a) := by
  by_cases h : a = b
  · subst h; rfl
  · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (Ne.symm h)]

-- One non-recursive symmetry step, with the recursion supplied as `hrec`
-- (carrying its own size bound). `equal`'s catch-all needs both head
-- constructors concrete, so we split on both and dispatch: matching scalars
-- (`==` is symmetric) and mismatches (`false` both ways); sequences via
-- `listEqual_symm`; meta by stripping and recursing on the payload; maps are
-- ruled out by `mapFree`.
private theorem equal_symm_step (a b : MalVal)
    (hrec : ∀ x y, sizeOf x + sizeOf y < sizeOf a + sizeOf b →
      mapFree x = true → mapFree y = true → MalVal.equal x y = MalVal.equal y x)
    (ha : mapFree a = true) (hb : mapFree b = true) :
    MalVal.equal a b = MalVal.equal b a := by
  cases a <;> cases b <;>
    first
      | (simp only [MalVal.equal] <;> first | rfl | exact beq_symm _ _)
      | (simp [mapFree] at ha; done)
      | (simp [MalVal.equal]; done)
      | (simp only [MalVal.equal]
         refine listEqual_symm _ _ (fun x hx y hy => hrec x y ?_
           (mapFreeList_iff.mp (by simpa only [mapFree] using ha) x hx)
           (mapFreeList_iff.mp (by simpa only [mapFree] using hb) y hy))
         have h₁ := List.sizeOf_lt_of_mem hx
         have h₂ := List.sizeOf_lt_of_mem hy
         simp only [MalVal.list.sizeOf_spec, MalVal.vec.sizeOf_spec]; omega)
      | (simp only [MalVal.equal, equal_strip_right]
         refine hrec _ _ ?_ (by simp_all [mapFree]) (by simp_all [mapFree])
         simp only [MalVal.withMeta.sizeOf_spec]; omega)

-- Symmetry on the map-free fragment: the recursion threads through
-- `equal_symm_step`, whose size bound discharges termination directly.
private theorem equal_symm : ∀ (a b : MalVal),
    mapFree a = true → mapFree b = true → MalVal.equal a b = MalVal.equal b a
  | a, b, ha, hb =>
    equal_symm_step a b (fun x y _hlt hx hy => equal_symm x y hx hy) ha hb
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by exact _hlt

-- Symmetry in action on a nested map-free value (list/vec compare equal in
-- both directions); contrast the duplicate-key map asymmetry above.
example :
    MalVal.equal (.list [.int 1, .vec [.kw "a"]]) (.vec [.int 1, .list [.kw "a"]])
  = MalVal.equal (.vec [.int 1, .list [.kw "a"]]) (.list [.int 1, .vec [.kw "a"]]) :=
  equal_symm _ _ (by simp [mapFree, mapFreeList]) (by simp [mapFree, mapFreeList])

/-! ### Symmetry of `equal` on distinct-key maps (scalar keys)

The map-free fragment dodges maps entirely. To bring maps back, the obstacle
is that the general distinct-key case needs `equal` to be *transitive* on keys
(to show the key-matching is injective). But the keys every interpreter map
actually carries are scalars (strings/keywords/ints), and on scalars
`equal k k'` is just `k = k'` — transitivity for free. That's exactly the
fragment handled here. -/

private def isScalarKey : MalVal → Bool
  | .nil | .bool _ | .int _ | .str _ | .kw _ | .sym _ | .atom _ => true
  | _ => false

-- On scalar keys `equal` is decidable equality: this is what dissolves the
-- transitivity entanglement (`=` is an equivalence for free).
private theorem equalScalar_iff {a b : MalVal}
    (ha : isScalarKey a = true) (hb : isScalarKey b = true) :
    MalVal.equal a b = true ↔ a = b := by
  cases a <;> cases b <;> simp_all [MalVal.equal, isScalarKey, beq_iff_eq]

-- `mapEqual A B` is exactly "every entry of `B` is found by key in `A`".
private theorem mapEqual_eq_true_iff (A B : List (MalVal × MalVal)) :
    MalVal.mapEqual A B = true ↔ ∀ p ∈ B, MalVal.mapLookup p.1 p.2 A = true := by
  induction B with
  | nil          => simp [MalVal.mapEqual]
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    simp [MalVal.mapEqual, ih]

-- With distinct scalar keys, looking up `k` lands on the unique `(k, u) ∈ ys`,
-- so the lookup reduces to comparing the query value `v` against `u`.
private theorem mapLookup_eq_of_mem : ∀ (ys : List (MalVal × MalVal)) (k v u : MalVal),
    isScalarKey k = true → keysDistinct ys = true → (k, u) ∈ ys →
    MalVal.mapLookup k v ys = MalVal.equal v u
  | [],              _, _, _, _,   _,  hmem => by simp at hmem
  | (k', u') :: rest, k, v, u, hsk, hd, hmem => by
    simp only [keysDistinct, Bool.and_eq_true] at hd
    obtain ⟨hall, hdrest⟩ := hd
    simp only [MalVal.mapLookup]
    rcases List.mem_cons.mp hmem with heq | hmemrest
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [if_pos ((equalScalar_iff hsk hsk).mpr rfl)]
    · have hk_ne : MalVal.equal k k' = false := by
        have h := (List.all_eq_true.mp hall) (k, u) hmemrest
        simpa using h
      rw [if_neg (by simp [hk_ne])]
      exact mapLookup_eq_of_mem rest k v u hsk hdrest hmemrest

-- Erasing the (unique) `k`-keyed entry leaves lookups of any other key `k'`
-- untouched: `k'` never matched it anyway. The head-erased case is exactly
-- where scalar-`=` transitivity is used (`equal j k`, `¬equal k' k ⟹ ¬equal k' j`).
private theorem mapLookup_eraseP_ne : ∀ (ys : List (MalVal × MalVal)) (k k' v : MalVal),
    isScalarKey k = true → (∀ p ∈ ys, isScalarKey p.1 = true) → MalVal.equal k' k = false →
    MalVal.mapLookup k' v (ys.eraseP (fun p => MalVal.equal p.1 k))
      = MalVal.mapLookup k' v ys
  | [],             _, _,  _, _,   _,    _   => by simp [MalVal.mapLookup]
  | (j, w) :: rest, k, k', v, hsk, hsys, hne => by
    have hsj : isScalarKey j = true := hsys (j, w) List.mem_cons_self
    have hsrest : ∀ p ∈ rest, isScalarKey p.1 = true :=
      fun p hp => hsys p (List.mem_cons_of_mem _ hp)
    have ih := mapLookup_eraseP_ne rest k k' v hsk hsrest hne
    by_cases hjk : MalVal.equal j k = true
    · have hk'j : MalVal.equal k' j = false := by
        rw [(equalScalar_iff hsj hsk).mp hjk]; exact hne
      simp [hjk, MalVal.mapLookup, hk'j]
    · have hjk' : MalVal.equal j k = false := by simpa using hjk
      simp [hjk', MalVal.mapLookup, ih]

-- A successful lookup exhibits the matching entry (forward direction; no
-- distinctness needed — just walk to the first key-match).
private theorem mapLookup_mem : ∀ (ys : List (MalVal × MalVal)) (k v : MalVal),
    MalVal.mapLookup k v ys = true →
    ∃ k' u, (k', u) ∈ ys ∧ MalVal.equal k k' = true ∧ MalVal.equal v u = true
  | [],              k, v, h => by simp [MalVal.mapLookup] at h
  | (k', u) :: rest, k, v, h => by
    simp only [MalVal.mapLookup] at h
    by_cases hkk' : MalVal.equal k k' = true
    · rw [if_pos hkk'] at h
      exact ⟨k', u, List.mem_cons_self, hkk', h⟩
    · rw [if_neg hkk'] at h
      obtain ⟨k'', u'', hmem, hkk'', hvu''⟩ := mapLookup_mem rest k v h
      exact ⟨k'', u'', List.mem_cons_of_mem _ hmem, hkk'', hvu''⟩

-- Distinct keys survive erasing any entry (it can only drop a key, never
-- introduce a clash).
private theorem keysDistinct_eraseP (p : MalVal × MalVal → Bool) :
    ∀ ys : List (MalVal × MalVal), keysDistinct ys = true → keysDistinct (ys.eraseP p) = true
  | [],             _  => by simp [keysDistinct]
  | (k, w) :: rest, hd => by
    simp only [keysDistinct, Bool.and_eq_true] at hd
    obtain ⟨hall, hdrest⟩ := hd
    rw [List.eraseP_cons]
    by_cases hp : p (k, w) = true
    · simp [hp, hdrest]
    · simp only [Bool.not_eq_true] at hp
      simp only [hp, cond_false, keysDistinct, Bool.and_eq_true]
      refine ⟨List.all_eq_true.mpr (fun x hx => ?_), keysDistinct_eraseP p rest hdrest⟩
      exact (List.all_eq_true.mp hall) x (List.mem_of_mem_eraseP hx)

-- The crux, one direction: if every `xs` entry is found in `ys`, then with
-- equal lengths and distinct scalar keys every `ys` entry is found in `xs`.
-- Induct on `xs`, erasing the matched `k`-entry from `ys` at each step; equal
-- lengths keep the two lists shrinking in lockstep down to `[]`.
private theorem mapEqual_transfer : ∀ (xs ys : List (MalVal × MalVal)),
    (∀ p ∈ xs, isScalarKey p.1 = true) → (∀ p ∈ ys, isScalarKey p.1 = true) →
    keysDistinct xs = true → keysDistinct ys = true → xs.length = ys.length →
    (∀ p ∈ xs, ∀ q ∈ ys, MalVal.equal p.2 q.2 = MalVal.equal q.2 p.2) →
    MalVal.mapEqual ys xs = true → MalVal.mapEqual xs ys = true
  | [],            ys, _, _, _, _, hlen, _, _ => by
    cases ys with
    | nil      => simp [MalVal.mapEqual]
    | cons _ _ => simp at hlen
  | (k, v) :: xs', ys, hsx, hsy, hdx, hdy, hlen, hsym, hme => by
    rw [mapEqual_eq_true_iff] at hme
    have hsk : isScalarKey k = true := hsx (k, v) List.mem_cons_self
    obtain ⟨k', u, hmem0, hkk', hvu⟩ := mapLookup_mem ys k v (hme (k, v) List.mem_cons_self)
    have hsk' : isScalarKey k' = true := hsy (k', u) hmem0
    obtain rfl : k = k' := (equalScalar_iff hsk hsk').mp hkk'
    have hPku : (fun p => MalVal.equal p.1 k) (k, u) = true := by
      simpa using (equalScalar_iff hsk hsk).mpr rfl
    -- side conditions for the recursive call on `xs'` and `ys.eraseP …`
    have hsx' : ∀ p ∈ xs', isScalarKey p.1 = true :=
      fun p hp => hsx p (List.mem_cons_of_mem _ hp)
    have hsy' : ∀ p ∈ ys.eraseP (fun p => MalVal.equal p.1 k), isScalarKey p.1 = true :=
      fun p hp => hsy p (List.eraseP_subset hp)
    simp only [keysDistinct, Bool.and_eq_true] at hdx
    have hdx' : keysDistinct xs' = true := hdx.2
    have hdy' : keysDistinct (ys.eraseP (fun p => MalVal.equal p.1 k)) = true :=
      keysDistinct_eraseP _ ys hdy
    have hlen' : xs'.length = (ys.eraseP (fun p => MalVal.equal p.1 k)).length := by
      have he := List.length_eraseP_of_mem (p := fun p => MalVal.equal p.1 k) hmem0 hPku
      simp only [List.length_cons] at hlen
      omega
    have hsym' : ∀ p ∈ xs', ∀ q ∈ ys.eraseP (fun p => MalVal.equal p.1 k),
        MalVal.equal p.2 q.2 = MalVal.equal q.2 p.2 :=
      fun p hp q hq => hsym p (List.mem_cons_of_mem _ hp) q (List.eraseP_subset hq)
    have hme' : MalVal.mapEqual (ys.eraseP (fun p => MalVal.equal p.1 k)) xs' = true := by
      rw [mapEqual_eq_true_iff]
      intro p hp
      have hpk : MalVal.equal p.1 k = false := by
        have h := (List.all_eq_true.mp hdx.1) p hp; simpa using h
      rw [mapLookup_eraseP_ne ys k p.1 p.2 hsk hsy hpk]
      exact hme p (List.mem_cons_of_mem _ hp)
    have ihres := mapEqual_transfer xs' (ys.eraseP (fun p => MalVal.equal p.1 k))
      hsx' hsy' hdx' hdy' hlen' hsym' hme'
    rw [mapEqual_eq_true_iff] at ihres ⊢
    intro q hq
    obtain ⟨j, uq⟩ := q
    simp only [MalVal.mapLookup]
    by_cases hjk : MalVal.equal j k = true
    · rw [if_pos hjk]
      obtain rfl : k = j := ((equalScalar_iff (hsy (j, uq) hq) hsk).mp hjk).symm
      have hveq : MalVal.equal v uq = true := by
        rw [← mapLookup_eq_of_mem ys k v uq hsk hdy hq,
            mapLookup_eq_of_mem ys k v u hsk hdy hmem0]; exact hvu
      rw [← hsym (k, v) List.mem_cons_self (k, uq) hq]; exact hveq
    · rw [if_neg hjk]
      have hjk' : MalVal.equal j k = false := by simpa using hjk
      exact ihres (j, uq) ((List.mem_eraseP_of_neg (by simp [hjk'])).mpr hq)

-- `mapEqual` is symmetric on distinct scalar-keyed lists of equal length:
-- apply `mapEqual_transfer` in both directions (its hypotheses are symmetric).
private theorem mapEqual_symm (xs ys : List (MalVal × MalVal))
    (hsx : ∀ p ∈ xs, isScalarKey p.1 = true) (hsy : ∀ p ∈ ys, isScalarKey p.1 = true)
    (hdx : keysDistinct xs = true) (hdy : keysDistinct ys = true)
    (hlen : xs.length = ys.length)
    (hsym : ∀ p ∈ xs, ∀ q ∈ ys, MalVal.equal p.2 q.2 = MalVal.equal q.2 p.2) :
    MalVal.mapEqual ys xs = MalVal.mapEqual xs ys := by
  have t1 := mapEqual_transfer xs ys hsx hsy hdx hdy hlen hsym
  have t2 := mapEqual_transfer ys xs hsy hsx hdy hdx hlen.symm
    (fun p hp q hq => (hsym q hq p hp).symm)
  cases h1 : MalVal.mapEqual ys xs
  · cases h2 : MalVal.mapEqual xs ys
    · rfl
    · exact absurd (t2 h2) (by simp [h1])
  · cases h2 : MalVal.mapEqual xs ys
    · exact absurd (t1 h1) (by simp [h2])
    · rfl

-- Headline: two distinct scalar-keyed maps compare `equal` in either order
-- (with values symmetric). The `equal_refl`/general-symmetry duplicate-key
-- counterexamples show both side conditions are real.
private theorem equal_map_symm (xs ys : List (MalVal × MalVal))
    (hsx : ∀ p ∈ xs, isScalarKey p.1 = true) (hsy : ∀ p ∈ ys, isScalarKey p.1 = true)
    (hdx : keysDistinct xs = true) (hdy : keysDistinct ys = true)
    (hsym : ∀ p ∈ xs, ∀ q ∈ ys, MalVal.equal p.2 q.2 = MalVal.equal q.2 p.2) :
    MalVal.equal (.map xs) (.map ys) = MalVal.equal (.map ys) (.map xs) := by
  simp only [MalVal.equal]
  by_cases hlen : xs.length = ys.length
  · rw [mapEqual_symm xs ys hsx hsy hdx hdy hlen hsym, beq_symm]
  · rw [beq_eq_false_iff_ne.mpr hlen, beq_eq_false_iff_ne.mpr (Ne.symm hlen)]
    simp

-- Symmetry holds on a *reordered* distinct-key map (the case general symmetry
-- and the duplicate-key counterexample could not reach).
example :
    MalVal.equal (.map [(.kw "a", .int 1), (.kw "b", .int 2)])
                 (.map [(.kw "b", .int 2), (.kw "a", .int 1)])
  = MalVal.equal (.map [(.kw "b", .int 2), (.kw "a", .int 1)])
                 (.map [(.kw "a", .int 1), (.kw "b", .int 2)]) := by
  refine equal_map_symm _ _ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · simp [keysDistinct, MalVal.equal]
  · simp [keysDistinct, MalVal.equal]
  · intro p hp q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp [MalVal.equal]

/-! ### Transitivity of `equal`

The capstone. Functions need no exclusion (`equal (.fn _) _ = false`, so a
transitive premise is unsatisfiable — vacuous); maps need distinct scalar
keys, as for symmetry. The map case is a direct *composition* of lookups
(chase each `xs` entry through `ys` into `zs`), no counting needed. -/

private theorem beq_trans {α} [BEq α] [LawfulBEq α] {a b c : α}
    (h1 : (a == b) = true) (h2 : (b == c) = true) : (a == c) = true := by
  rw [beq_iff_eq] at *; exact h1.trans h2

-- Stripping never grows a value, and stays within the map-free fragment.
private theorem sizeOf_strip_le : ∀ v : MalVal, sizeOf v.strip ≤ sizeOf v
  | .withMeta v _ => by
    simp only [MalVal.strip]
    have := sizeOf_strip_le v; simp only [MalVal.withMeta.sizeOf_spec]; omega
  | .nil | .bool _ | .int _ | .str _ | .kw _ | .sym _
  | .atom _ | .list _ | .vec _ | .map _ | .fn _ => by simp [MalVal.strip]

private theorem mapFree_strip : ∀ v : MalVal, mapFree v.strip = mapFree v
  | .withMeta v _ => by simp only [MalVal.strip, mapFree]; exact mapFree_strip v
  | .nil | .bool _ | .int _ | .str _ | .kw _ | .sym _
  | .atom _ | .list _ | .vec _ | .map _ | .fn _ => by simp [MalVal.strip]

-- Sequence transitivity given elementwise transitivity (length-mismatched
-- combinations are vacuous: `listEqual` is `false` there).
private theorem listEqual_trans : ∀ (xs ys zs : List MalVal),
    (∀ x ∈ xs, ∀ y ∈ ys, ∀ z ∈ zs,
      MalVal.equal x y = true → MalVal.equal y z = true → MalVal.equal x z = true) →
    MalVal.listEqual xs ys = true → MalVal.listEqual ys zs = true →
    MalVal.listEqual xs zs = true
  | [],      [],      [],      _, _,  _  => by simp [MalVal.listEqual]
  | [],      [],      _ :: _,  _, _,  h2 => by simp [MalVal.listEqual] at h2
  | [],      _ :: _,  _,       _, h1, _  => by simp [MalVal.listEqual] at h1
  | _ :: _,  [],      _,       _, h1, _  => by simp [MalVal.listEqual] at h1
  | _ :: _,  _ :: _,  [],      _, _,  h2 => by simp [MalVal.listEqual] at h2
  | x :: xs, y :: ys, z :: zs, H, h1, h2 => by
    simp only [MalVal.listEqual, Bool.and_eq_true] at h1 h2 ⊢
    exact ⟨H x List.mem_cons_self y List.mem_cons_self z List.mem_cons_self h1.1 h2.1,
           listEqual_trans xs ys zs
             (fun a ha b hb c hc => H a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
               c (List.mem_cons_of_mem _ hc)) h1.2 h2.2⟩

-- A scalar `s` compared `equal` to `v` pins `v` down: `v.strip = s`. Lets the
-- transitivity proof case only on `a` and *read off* `b`/`c` from the premises.
private theorem equal_scalar_strip (s v : MalVal) (hs : isScalarKey s = true)
    (h : MalVal.equal s v = true) : v.strip = s := by
  have h' : MalVal.equal s v.strip = true := by rw [equal_strip_right_full]; exact h
  have hnm := strip_no_meta v
  cases hsv : v.strip <;> rw [hsv] at h' <;>
    first
      | exact absurd hsv (hnm _ _)
      | (cases s <;> simp_all [MalVal.equal, isScalarKey, beq_iff_eq])

-- A `list`-headed comparison pins `v.strip` to a sequence whose elements
-- `listEqual` the head's.
private theorem equal_seq_strip (xs : List MalVal) (v : MalVal)
    (h : MalVal.equal (.list xs) v = true) :
    ∃ ys, (v.strip = .list ys ∨ v.strip = .vec ys) ∧ MalVal.listEqual xs ys = true := by
  have h' : MalVal.equal (.list xs) v.strip = true := by rw [equal_strip_right_full]; exact h
  have hnm := strip_no_meta v
  cases hsv : v.strip <;> rw [hsv] at h' <;>
    first
      | exact absurd hsv (hnm _ _)
      | exact ⟨_, Or.inl rfl, by simpa [MalVal.equal] using h'⟩
      | exact ⟨_, Or.inr rfl, by simpa [MalVal.equal] using h'⟩
      | simp [MalVal.equal] at h'

-- `vec` and `list` heads compare identically (both reduce to `listEqual`).
private theorem equal_vec_list (xs : List MalVal) (v : MalVal) :
    MalVal.equal (.vec xs) v = MalVal.equal (.list xs) v := by
  rw [← equal_strip_right_full (.vec xs) v, ← equal_strip_right_full (.list xs) v]
  cases hsv : v.strip <;>
    first
      | exact absurd hsv (strip_no_meta v _ _)
      | simp [MalVal.equal]

-- A function never compares `equal` to anything — so any `fn`-headed premise
-- is unsatisfiable.
private theorem equal_fn_false (f : Fn) (v : MalVal) : MalVal.equal (.fn f) v = false := by
  rw [← equal_strip_right_full]
  cases hsv : v.strip <;>
    first
      | exact absurd hsv (strip_no_meta v _ _)
      | simp [MalVal.equal]

-- One non-recursive transitivity step. Splitting only on `a` keeps this cheap;
-- the shape lemmas read `b`/`c` off the premises. `meta` peels and recurses;
-- `map`/`fn` are vacuous; scalars pin both sides equal to `a`; sequences chain
-- via `listEqual_trans` (with `vec` folded into `list` by `equal_vec_list`).
private theorem equal_trans_step (a b c : MalVal)
    (hrec : ∀ x y z, sizeOf x + sizeOf y + sizeOf z < sizeOf a + sizeOf b + sizeOf c →
      mapFree x = true → mapFree y = true → mapFree z = true →
      MalVal.equal x y = true → MalVal.equal y z = true → MalVal.equal x z = true)
    (ha : mapFree a = true) (hb : mapFree b = true) (hc : mapFree c = true)
    (h1 : MalVal.equal a b = true) (h2 : MalVal.equal b c = true) :
    MalVal.equal a c = true := by
  cases a <;>
    first
      | (simp only [mapFree] at ha; exact Bool.noConfusion ha)
      | (rw [equal_fn_false] at h1; exact Bool.noConfusion h1)
      | (simp only [MalVal.equal] at h1 ⊢
         exact hrec _ b c (by simp only [MalVal.withMeta.sizeOf_spec]; omega)
           (by simpa [mapFree] using ha) hb hc h1 h2)
      | (have hbs := equal_scalar_strip _ b (by rfl) h1
         rw [equal_strip b c, hbs] at h2
         have hcs := equal_scalar_strip _ c.strip (by rfl) h2
         rw [strip_idem] at hcs
         rw [equal_strip _ c, hcs]; simp only [MalVal.strip]
         exact (equalScalar_iff (by rfl) (by rfl)).mpr rfl)
      | (try rw [equal_vec_list] at h1 ⊢
         obtain ⟨ys, hys, hxy⟩ := equal_seq_strip _ b h1
         have hlc : MalVal.equal (.list ys) c.strip = true := by
           rw [equal_strip] at h2
           rcases hys with hys | hys <;> rw [hys] at h2
           · exact h2
           · rwa [← equal_vec_list]
         obtain ⟨zs, hzs, hyz⟩ := equal_seq_strip _ c.strip hlc
         simp only [strip_idem] at hzs
         have hbsz := sizeOf_strip_le b
         have hcsz := sizeOf_strip_le c
         have hys_sz : sizeOf ys < sizeOf b.strip := by
           rcases hys with h | h <;> rw [h] <;>
             simp only [MalVal.list.sizeOf_spec, MalVal.vec.sizeOf_spec] <;> omega
         have hzs_sz : sizeOf zs < sizeOf c.strip := by
           rcases hzs with h | h <;> rw [h] <;>
             simp only [MalVal.list.sizeOf_spec, MalVal.vec.sizeOf_spec] <;> omega
         have hmfy : mapFreeList ys = true := by
           have h := mapFree_strip b; rw [hb] at h
           rcases hys with hh | hh <;> rw [hh] at h <;> simpa [mapFree] using h
         have hmfz : mapFreeList zs = true := by
           have h := mapFree_strip c; rw [hc] at h
           rcases hzs with hh | hh <;> rw [hh] at h <;> simpa [mapFree] using h
         rw [← equal_strip_right_full]
         rcases hzs with hzs | hzs <;> rw [hzs] <;>
           (simp only [MalVal.equal]
            exact listEqual_trans _ ys zs
              (fun x hx y hy z hz hxy' hyz' => hrec x y z (by
                have hx' := List.sizeOf_lt_of_mem hx
                have hy' := List.sizeOf_lt_of_mem hy
                have hz' := List.sizeOf_lt_of_mem hz
                simp only [MalVal.list.sizeOf_spec, MalVal.vec.sizeOf_spec]; omega)
                (mapFreeList_iff.mp (by simpa [mapFree] using ha) x hx)
                (mapFreeList_iff.mp hmfy y hy)
                (mapFreeList_iff.mp hmfz z hz)
                hxy' hyz') hxy hyz))

private theorem equal_trans : ∀ (a b c : MalVal),
    mapFree a = true → mapFree b = true → mapFree c = true →
    MalVal.equal a b = true → MalVal.equal b c = true → MalVal.equal a c = true
  | a, b, c, ha, hb, hc, h1, h2 =>
    equal_trans_step a b c (fun x y z _hlt hx hy hz => equal_trans x y z hx hy hz)
      ha hb hc h1 h2
  termination_by a b c => sizeOf a + sizeOf b + sizeOf c
  decreasing_by exact _hlt

/-! ### Transitivity on distinct-key maps (scalar keys)

Unlike symmetry, the map case is a plain composition: chase each `xs` entry to
its match in `ys` (forward lookup), then to `zs`, and transitivity of the
values closes it. No counting — `zs` distinctness just pins the final lookup. -/

private theorem mapEqual_trans (xs ys zs : List (MalVal × MalVal))
    (hsx : ∀ p ∈ xs, isScalarKey p.1 = true) (hsy : ∀ p ∈ ys, isScalarKey p.1 = true)
    (hsz : ∀ p ∈ zs, isScalarKey p.1 = true) (hdz : keysDistinct zs = true)
    (htr : ∀ p ∈ xs, ∀ q ∈ ys, ∀ r ∈ zs,
      MalVal.equal p.2 q.2 = true → MalVal.equal q.2 r.2 = true → MalVal.equal p.2 r.2 = true)
    (h1 : MalVal.mapEqual ys xs = true) (h2 : MalVal.mapEqual zs ys = true) :
    MalVal.mapEqual zs xs = true := by
  rw [mapEqual_eq_true_iff] at h1 h2 ⊢
  intro p hp
  obtain ⟨k, v⟩ := p
  obtain ⟨k', w, hwmem, hkk', hvw⟩ := mapLookup_mem ys k v (h1 (k, v) hp)
  obtain rfl : k = k' := (equalScalar_iff (hsx (k, v) hp) (hsy (k', w) hwmem)).mp hkk'
  obtain ⟨k'', x, hxmem, hkk'', hwx⟩ := mapLookup_mem zs k w (h2 (k, w) hwmem)
  obtain rfl : k = k'' := (equalScalar_iff (hsx (k, v) hp) (hsz (k'', x) hxmem)).mp hkk''
  rw [mapLookup_eq_of_mem zs k v x (hsx (k, v) hp) hdz hxmem]
  exact htr (k, v) hp (k, w) hwmem (k, x) hxmem hvw hwx

-- Headline: `equal` is transitive across three distinct scalar-keyed maps
-- (with values transitive). Only `zs` need be distinct — the final lookup is
-- the only one pinned by it.
private theorem equal_map_trans (xs ys zs : List (MalVal × MalVal))
    (hsx : ∀ p ∈ xs, isScalarKey p.1 = true) (hsy : ∀ p ∈ ys, isScalarKey p.1 = true)
    (hsz : ∀ p ∈ zs, isScalarKey p.1 = true) (hdz : keysDistinct zs = true)
    (htr : ∀ p ∈ xs, ∀ q ∈ ys, ∀ r ∈ zs,
      MalVal.equal p.2 q.2 = true → MalVal.equal q.2 r.2 = true → MalVal.equal p.2 r.2 = true)
    (h1 : MalVal.equal (.map xs) (.map ys) = true)
    (h2 : MalVal.equal (.map ys) (.map zs) = true) :
    MalVal.equal (.map xs) (.map zs) = true := by
  simp only [MalVal.equal, Bool.and_eq_true] at h1 h2 ⊢
  obtain ⟨hlen1, hme1⟩ := h1
  obtain ⟨hlen2, hme2⟩ := h2
  refine ⟨?_, mapEqual_trans xs ys zs hsx hsy hsz hdz htr hme1 hme2⟩
  rw [beq_iff_eq] at hlen1 hlen2 ⊢; omega

-- Transitivity in action: on map-free values (list/vec cross), and chaining two
-- reorderings of a distinct-key map back to the original.
example : MalVal.equal (.list [.int 1]) (.vec [.int 1]) = true →
          MalVal.equal (.vec [.int 1]) (.list [.int 1]) = true →
          MalVal.equal (.list [.int 1]) (.list [.int 1]) = true :=
  fun h1 h2 => equal_trans _ _ _ (by simp [mapFree, mapFreeList])
    (by simp [mapFree, mapFreeList]) (by simp [mapFree, mapFreeList]) h1 h2

example
    (h1 : MalVal.equal (.map [(.kw "a", .int 1), (.kw "b", .int 2)])
                       (.map [(.kw "b", .int 2), (.kw "a", .int 1)]) = true)
    (h2 : MalVal.equal (.map [(.kw "b", .int 2), (.kw "a", .int 1)])
                       (.map [(.kw "a", .int 1), (.kw "b", .int 2)]) = true) :
    MalVal.equal (.map [(.kw "a", .int 1), (.kw "b", .int 2)])
                 (.map [(.kw "a", .int 1), (.kw "b", .int 2)]) = true := by
  refine equal_map_trans _ _ _ ?_ ?_ ?_ ?_ ?_ h1 h2
  · decide
  · decide
  · decide
  · simp [keysDistinct, MalVal.equal]
  · intro p hp q hq r hr hpq hqr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq hr
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> rcases hr with rfl | rfl <;>
      simp_all [MalVal.equal]

end Types
