module

public import MalLean4.Env
public import MalLean4.Atoms
public import Std.Data.HashSet.Basic

open Types

-- Mark-and-sweep over `Env.store` and `Atoms.store`. Lambdas register
-- their captured env in `Env.store`, and `MalVal.atom` references entries
-- in `Atoms.store`; both grow monotonically as the program runs, so
-- without GC they leak as fast as `fn*` and `atom` are evaluated.
--
-- `GC.run` walks live values reachable from the root env (transitively
-- through bindings, lists, vectors, maps, meta wrappers, and the
-- `outerEnvId` / atom id stored in lambdas/atoms) and `none`-s out the
-- unreached slots. The array itself still grows by one `Option` slot per
-- allocation; the heavy payload (the captured frame's `HashMap` and the
-- values it pinned) becomes collectable.

namespace GC

structure Marks where
  envs  : Std.HashSet Nat := ∅
  atoms : Std.HashSet Nat := ∅

mutual

  partial def markVal (marks : IO.Ref Marks) : MalVal → IO Unit
    | .list xs       => xs.forM (markVal marks)
    | .vec  xs       => xs.forM (markVal marks)
    | .map  ps       => ps.forM fun (k, v) => do
      markVal marks k; markVal marks v
    | .withMeta v m  => do markVal marks v; markVal marks m
    | .fn (.lambda l) => do
      let m ← marks.get
      unless m.envs.contains l.outerId do
        marks.set { m with envs := m.envs.insert l.outerId }
        let env ← Env.lookup l.outerId
        markEnv marks env
    | .atom n => do
      let m ← marks.get
      unless m.atoms.contains n do
        marks.set { m with atoms := m.atoms.insert n }
        match ← Atoms.deref n with
        | some v => markVal marks v
        | none   => pure ()
    | _ => pure ()

  partial def markEnv (marks : IO.Ref Marks) (env : Env) : IO Unit := do
    let bindings ← env.current.get
    for (_, v) in bindings.toList do
      markVal marks v
    match env.outer with
    | some o => markEnv marks o
    | none   => pure ()

end

/-- Mark every env / atom id reachable from `root`, then `none` out the
unreached slots in both stores. Safe to call only at points where the
host's eval stack isn't holding values invisible to `root` — the REPL
loop boundary and the `(gc)` builtin are both safe; calling mid-eval
would collect intermediates still in use. -/
public def run (root : Env) : IO Unit := do
  let marks ← IO.mkRef ({} : Marks)
  markEnv marks root
  let m ← marks.get
  let envArr ← Env.store.get
  Env.store.set (envArr.mapIdx fun i e =>
    if m.envs.contains i then e else none)
  let atomArr ← Atoms.store.get
  Atoms.store.set (atomArr.mapIdx fun i a =>
    if m.atoms.contains i then a else none)

/-- Number of new `Env.store` registrations between automatic sweeps. -/
def threshold : Nat := 1000

/-- Trigger `run` if at least `threshold` `Env.register` calls have landed
since the last sweep. Hot path is a `Nat` read + compare — no array
allocation, no work — so it's cheap to call from `evalDo` between every
sequenced form. Safe only at points where the host eval stack isn't
holding values invisible to `root`. -/
public def maybeRun (root : Env) : IO Unit := do
  if (← Env.sinceLastSweep.get) > threshold then
    run root
    Env.sinceLastSweep.set 0

end GC
