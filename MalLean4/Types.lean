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

end Types
