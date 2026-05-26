module

public import MalLean4.Env
public import MalLean4.Atoms
public import Std.Data.HashSet.Basic

open Types

-- Mark-and-sweep over `Env.store` and `Atoms.store`. Lambdas register
-- their captured env there, and `MalVal.atom` references entries in
-- `Atoms.store`; both grow monotonically, so without GC they leak as
-- fast as `fn*` and `atom` evaluate. `run` walks values reachable from
-- the root env and `none`-s out unreached slots — the array still grows
-- by one `Option` per allocation, but the heavy payload (captured
-- frame's `HashMap` and the values it pinned) becomes collectable.

namespace GC

-- Each recursive `eval` entry pushes a fresh `IO.Ref Env`, updates it
-- as its mutable `env` changes, and pops on return. `GC.run` walks
-- every env here so closures sitting in an outer frame's `letEnv` (or
-- any other non-current env) survive sweeps fired by a deeper frame's
-- `evalDo`.
public initialize roots : IO.Ref (List (IO.Ref Env)) ← IO.mkRef []

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
    -- Mark this env's slot so it survives a sweep when its only outside
    -- reference is a lambda on the host stack.
    if let some id ← env.idRef.get then
      let m ← marks.get
      if !m.envs.contains id then
        marks.set { m with envs := m.envs.insert id }
    let bindings ← env.current.get
    for (_, v) in bindings.toList do
      markVal marks v
    match env.outer with
    | some o => markEnv marks o
    | none   => pure ()

end

-- Safe only at points where the host's eval stack isn't holding values
-- invisible to `root` — the REPL loop boundary and `evalDo`'s
-- between-forms gap. Calling mid-eval would collect live intermediates.
public def run (root : Env) : IO Unit := do
  let marks ← IO.mkRef ({} : Marks)
  markEnv marks root
  for envRef in (← roots.get) do
    markEnv marks (← envRef.get)
  let m ← marks.get
  let envArr ← Env.store.get
  Env.store.set (envArr.mapIdx fun i e =>
    if m.envs.contains i then e else none)
  let atomArr ← Atoms.store.get
  Atoms.store.set (atomArr.mapIdx fun i a =>
    if m.atoms.contains i then a else none)
  Env.lastSweepSize.set (← Env.store.get).size
  Env.shouldSweep.set false

public def maybeRun (root : Env) : IO Unit := do
  if (← Env.shouldSweep.get) then run root

end GC
