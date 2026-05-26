import MalLean4.Core
import MalLean4.Debug
import MalLean4.GC
import MalLean4.Reader
import MalLean4.Printer

open Types

-- Quasiquote rewrites `(quasiquote x)` into a tree of `cons`/`concat`/`vec`/
-- `quote` calls that reconstruct `x` with `unquote`/`splice-unquote` honored.
mutual
  def quasiquote : MalVal → MalVal
    | .list [.sym "unquote", x] => x
    | .list xs                  => quasiquoteList xs
    | .vec  xs                  => .list [.sym "vec", quasiquoteList xs]
    | m@(.map _)                => .list [.sym "quote", m]
    | .sym s                    => .list [.sym "quote", .sym s]
    | other                     => other

  def quasiquoteList : List MalVal → MalVal
    | []      => .list []
    | x :: xs =>
      let rest := quasiquoteList xs
      match x with
      | .list [.sym "splice-unquote", y] => .list [.sym "concat", y, rest]
      | _ => .list [.sym "cons", quasiquote x, rest]
end

def lookupSym (env : Env) (s : String) : MalIO MalVal := do
  match ← env.find? s with
  | some v => return v
  | none   => throw (.str s!"'{s}' not found")

/-- Special-form heads handled directly by `evalLoop`'s dispatch match.
Macroexpansion is skipped for these — the env lookup inside `macroexpand`
would just return nothing, since users can't bind these as macros without
shadowing the evaluator-level dispatch (which fires first). -/
def isSpecialForm : String → Bool
  | "def!" | "defmacro!" | "fn*" | "quote" | "macroexpand"
  | "let*" | "do"        | "if"  | "try*"               => true
  | _                                                   => false

/-- Walk `params` and `args` in lockstep, threading a `HashMap`. Returns
the populated map plus any leftover args (consumed by a rest-param or
flagged as an arity error). Leftover params (when args run out first)
flow back via the returned `params` tail in the caller's error path. -/
private def bindPositional :
    (hm : Std.HashMap String MalVal) → (params : List String) →
    (args : List MalVal) →
    Std.HashMap String MalVal × List String × List MalVal
  | hm, [],      rest    => (hm, [], rest)
  | hm, ps,      []      => (hm, ps, [])
  | hm, p :: ps, a :: as => bindPositional (hm.insert p a) ps as

/-- Build a fresh child env of `parent` populated with `l`'s positional
and (optional) rest-parameter bindings. One ref allocation per call —
versus the prior `Env.new + N × current.modify` which paid N ref ops
just to seed the map. Shared by `evalLoop`'s tail-call path and
`apply`'s non-tail entry. -/
def bindLambdaArgs (parent : Env) (l : Lambda)
    (args : List MalVal) : MalIO Env := do
  let (hm, leftoverParams, leftoverArgs) :=
    bindPositional ∅ l.params args
  if !leftoverParams.isEmpty then
    let needed := l.params.length
    let got    := needed - leftoverParams.length
    let qual   := if l.restParam.isSome then " at least" else ""
    throw (.str s!"arity mismatch: expected{qual} {needed}, got {got}")
  let hm ← match l.restParam with
    | some restName => pure (hm.insert restName (.list leftoverArgs))
    | none          =>
      if leftoverArgs.isEmpty then pure hm
      else
        let needed := l.params.length
        let got    := needed + leftoverArgs.length
        throw (.str s!"arity mismatch: expected {needed}, got {got}")
  Env.newWithBindings parent hm

mutual
  /-- Leaf forms short-circuit; non-leaf forms enter `evalLoop` under a
  GC root push. The root is re-synced when a tail-position form rebinds
  `env` (`let*` body, lambda apply) so a sweep fired by a deeper frame
  sees the current env, not the call-site env. -/
  partial def eval (env₀ : Env) (ast₀ : MalVal) : MalIO MalVal := do
    match ast₀ with
    | .nil | .bool _ | .int _ | .str _ | .kw _ | .fn _ | .atom _ | .list [] =>
      return ast₀
    | .sym s => lookupSym env₀ s
    | _ =>
      let envRef ← IO.mkRef env₀
      GC.roots.modify (envRef :: ·)
      let result ← tryCatch (evalLoop envRef env₀ ast₀)
        fun e => do GC.roots.modify (·.tail!); throw e
      GC.roots.modify (·.tail!)
      return result

  partial def evalLoop (envRef : IO.Ref Env) (env₀ : Env)
      (ast₀ : MalVal) : MalIO MalVal := do
    let mut env := env₀
    let mut ast := ast₀
    while true do
      -- Quasiquote: pure AST rewrite; no macroexpand, no trace.
      if let .list [.sym "quasiquote", arg] := ast then
        ast := quasiquote arg
        continue

      -- For `.list (.sym name :: args)` that isn't a special form, look
      -- the head up once and either (a) macroexpand + continue, or (b)
      -- stash the value in `cachedHead` so the call dispatch below can
      -- skip the second `env.find?` that `eval env head` would do. Other
      -- shapes (computed heads, special forms, non-list ast) leave
      -- `cachedHead = none` and fall through unchanged.
      let mut cachedHead : Option MalVal := none
      if let .list (.sym name :: args) := ast then
        unless isSpecialForm name do
          match ← env.find? name with
          | some v =>
            if let .fn (.lambda lam) := v.strip then
              if lam.isMacro then
                ast ← macroexpand env (← apply env (.fn (.lambda lam)) args)
                continue
            cachedHead := some v
          | none => pure ()  -- second lookup in the call arm will throw
      Debug.trace env ast

      match ast with
      | .list (.sym "def!"        :: rest) => return ← evalDef         env rest
      | .list (.sym "defmacro!"   :: rest) => return ← evalDefmacro    env rest
      | .list (.sym "fn*"         :: rest) => return ← evalFn          env rest
      | .list (.sym "quote"       :: rest) => return ← evalQuote           rest
      | .list (.sym "macroexpand" :: rest) => return ← evalMacroexpand env rest
      | .list (.sym "let*" :: rest) =>
        let (letEnv, body) ← evalLet env rest
        env := letEnv
        envRef.set env
        ast := body
      | .list (.sym "do" :: forms) =>
        ast ← evalDo env forms
      | .list (.sym "try*" :: rest) =>
        match rest with
        | [tryExpr] => ast := tryExpr
        | [tryExpr, .list [.sym "catch*", .sym binding, handler]] =>
          return ← tryCatch (eval env tryExpr) fun thrown => do
            let catchEnv ← env.new
            catchEnv.set binding thrown
            eval catchEnv handler
        | _ => throw (.str "try*: expected (try* expr [(catch* sym handler)])")
      | .list (.sym "if" :: rest) =>
        match rest with
        | [pred, thn]      =>
          ast := if (← eval env pred).isTruthy then thn else .nil
        | [pred, thn, els] =>
          ast := if (← eval env pred).isTruthy then thn else els
        | _ => throw (.str "if: expected (if pred then [else])")
      | .list (head :: args) =>
        let initialHead ← if let some h := cachedHead then pure h
                          else eval env head
        let mut callHead := initialHead
        let mut callArgs ← args.mapM (eval env)
        -- `(apply f xs)` peels into `(f x1 x2 …)` so user lambdas
        -- dispatched via the `apply` builtin still hit the host-level
        -- tail-call below instead of stacking through `Context.apply`.
        while (match callHead.strip with
               | .fn (.builtin "apply") => true | _ => false) do
          match callArgs with
          | [] | [_] =>
            throw (.str "apply: expected at least a function and a list")
          | f :: rest =>
            let last :: revInit := rest.reverse
              | throw (.str "apply: expected at least a function and a list")
            let some lastArgs := last.toList?
              | throw (.str "apply: last argument must be a sequence")
            callHead := f
            callArgs := revInit.reverse ++ lastArgs
        match callHead.strip with
        | .fn (.builtin name) =>
          return ← Core.callBuiltin name env eval (apply env) callArgs
        | .fn (.lambda l) =>
          let outerEnv ← Env.lookup l.outerId
          let closureEnv ← bindLambdaArgs outerEnv l callArgs
          env := closureEnv
          envRef.set env
          ast := l.body
        | _ => throw (.str "first item in list is not callable")
      | .vec xs =>
        return .vec (← xs.mapM (eval env))
      | .map ps =>
        return .map (← ps.mapM fun (k, v) => return (k, ← eval env v))
      | .sym s => return ← lookupSym env s
      | other => return other
    return .nil  -- unreachable; the while loop only exits via `return`
  where
    evalDef (env : Env) : List MalVal → MalIO MalVal
      | [.sym name, expr] => do
        let v ← eval env expr
        env.set name v
        return v
      | _ => throw (.str "def!: expected (def! name expr)")

    evalDefmacro (env : Env) : List MalVal → MalIO MalVal
      | [.sym name, expr] => do
        let .fn (.lambda l) ← eval env expr
          | throw (.str "defmacro!: value must be a function")
        let macroFn : MalVal := .fn (.lambda { l with isMacro := true })
        env.set name macroFn
        return macroFn
      | _ => throw (.str "defmacro!: expected (defmacro! name expr)")

    evalLet (env : Env) : List MalVal → MalIO (Env × MalVal)
      | [bindingsForm, body] => do
        let some bs := bindingsForm.toList?
          | throw (.str "let*: bindings must be a list")
        let letEnv ← env.new
        bindLet letEnv bs
        return (letEnv, body)
      | _ => throw (.str "let*: expected (let* (bindings) body)")

    evalDo (env : Env) : List MalVal → MalIO MalVal
      | []    => return .nil
      | forms => do
        for x in forms.dropLast do
          let _ ← eval env x
        GC.maybeRun env
        return forms.getLast!

    evalFn (env : Env) : List MalVal → MalIO MalVal
      | [paramsForm, body] => do
        let some params := paramsForm.toList?
          | throw (.str "fn*: expected (fn* (params) body)")
        let (paramNames, restParam) ← Core.parseParams params
        let envId ← Env.register env
        return .fn (.lambda { params := paramNames, restParam, body,
                              outerEnvId := envId })
      | _ => throw (.str "fn*: expected (fn* (params) body)")

    evalQuote : List MalVal → MalIO MalVal
      | [arg] => return arg
      | _ => throw (.str "quote: expected 1 argument")

    evalMacroexpand (env : Env) : List MalVal → MalIO MalVal
      | [arg] => macroexpand env arg
      | _ => throw (.str "macroexpand: expected 1 argument")

  /-- Non-tail entry for builtin callbacks (e.g. `map`, `swap!`). Body
  evaluation goes through `eval`, which pushes its own GC root. -/
  partial def apply (callerEnv : Env) (head : MalVal)
      (args : List MalVal) : MalIO MalVal := do
    match head.strip with
    | .fn (.builtin name) =>
      Core.callBuiltin name callerEnv eval (apply callerEnv) args
    | .fn (.lambda l) =>
      let outerEnv ← Env.lookup l.outerId
      let closureEnv ← bindLambdaArgs outerEnv l args
      eval closureEnv l.body
    | _ => throw (.str "first item in list is not callable")

  partial def macroexpand (env : Env) (ast : MalVal) : MalIO MalVal := do
    let .list (.sym name :: args) := ast | return ast
    let some (.fn (.lambda lam)) := (← env.find? name).map MalVal.strip
      | return ast
    if lam.isMacro then
      macroexpand env (← apply env (.fn (.lambda lam)) args)
    else
      return ast

  partial def bindLet (env : Env) : List MalVal → MalIO Unit
    | []                    => return ()
    | .sym k :: rhs :: rest => do
      let v ← eval env rhs
      env.set k v
      bindLet env rest
    | _ => throw (.str "let*: bindings must be symbol/expr pairs")
end

def READ  (s : String)   : Except String (Option MalVal) := Reader.readStr s
def PRINT (ast : MalVal) : IO String                     := Printer.prStr ast

def rep (env : Env) (s : String) : IO (Option String) := do
  match READ s with
  | .ok none       => return none
  | .ok (some ast) =>
    match ← (eval env ast).toBaseIO with
    | .ok v    => return some (← PRINT v)
    | .error e => return some s!"Error: {← Printer.prStr e}"
  | .error e       => return some s!"Error: {e}"

partial def loop (env : Env) (stdin stdout : IO.FS.Stream) : IO Unit := do
  stdout.putStr "user> "
  stdout.flush
  let line ← stdin.getLine
  if line.isEmpty then return
  if let some out ← rep env line then
    stdout.putStrLn out
  GC.maybeRun env
  loop env stdin stdout

def main (args : List String) : IO Unit := do
  let env ← Core.initialEnv
  let _ ← rep env "(def! not (fn* (a) (if a false true)))"
  let _ ← rep env "(def! load-file (fn* (f) (eval (read-string (str \"(do \" (slurp f) \"\nnil)\")))))"
  let _ ← rep env "(defmacro! cond (fn* (& xs) (if (> (count xs) 0) (list 'if (first xs) (if (> (count xs) 1) (nth xs 1) (throw \"odd number of forms to cond\")) (cons 'cond (rest (rest xs)))))))"
  let _ ← rep env "(def! *host-language* \"lean4\")"
  match args with
  | []           =>
    env.set "*ARGV*" (.list [])
    let _ ← rep env "(println (str \"Mal [\" *host-language* \"]\"))"
    let stdin  ← IO.getStdin
    let stdout ← IO.getStdout
    loop env stdin stdout
  | file :: rest =>
    let argv : List MalVal := rest.map MalVal.str
    env.set "*ARGV*" (.list argv)
    let _ ← rep env s!"(load-file \"{file}\")"
    return
