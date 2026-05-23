import MalLean4.Core
import MalLean4.Debug
import MalLean4.Reader
import MalLean4.Printer

open Types

-- Quasiquote transformation: rewrites a `quasiquote`d form into a tree of
-- `cons`/`concat` calls that, when evaluated, reconstruct the form with
-- `unquote`/`splice-unquote` substitutions applied. Vectors are wrapped in
-- `vec` so they reconstruct as vectors; hash-maps and symbols are quoted.
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

mutual
  partial def eval (env : Env) : MalVal → MalIO MalVal := fun astIn => do
    -- Quasiquote is a pure transformation; recurse on the rewritten form
    -- without a trace so DEBUG-EVAL only shows the result.
    match astIn with
    | .list [.sym "quasiquote", arg] => eval env (quasiquote arg)
    | _ => do
    -- Macroexpansion is also a transformation: trace fires AFTER expansion
    -- so DEBUG-EVAL shows the expanded form, not the macro call.
    let ast ← macroexpand env astIn
    Debug.trace env ast
    match ast with
    | .list []                           => return .list []
    | .list (.sym "def!"        :: rest) => evalDef env rest
    | .list (.sym "defmacro!"   :: rest) => evalDefmacro env rest
    | .list (.sym "let*"        :: rest) => evalLet env rest
    | .list (.sym "do"          :: rest) => evalDo  env rest
    | .list (.sym "if"          :: rest) => evalIf  env rest
    | .list (.sym "fn*"         :: rest) => evalFn  env rest
    | .list (.sym "quote"       :: rest) => evalQuote rest
    | .list (.sym "quasiquote"  :: rest) => evalQuasiquote env rest
    | .list (.sym "macroexpand" :: rest) => evalMacroexpand env rest
    | .list (.sym "try*"        :: rest) => evalTry env rest
    | .list (head :: args)               => evalCall env head args
    | .vec  xs                           => do return .vec (← xs.mapM (eval env))
    | .map  ps                           => do
      return .map (← ps.mapM fun (k, v) => return (k, ← eval env v))
    | .sym s                             => lookupSym env s
    | other                              => return other

  partial def evalCall (env : Env) (head : MalVal) (args : List MalVal) :
      MalIO MalVal := do
    let head' ← eval env head
    let args' ← args.mapM (eval env)
    apply env head' args'

  partial def lookupSym (env : Env) (s : String) : MalIO MalVal := do
    match ← env.find? s with
    | some v => return v
    | none   => throw (.str s!"'{s}' not found")

  partial def macroexpand (env : Env) : MalVal → MalIO MalVal := fun ast => do
    match ast with
    | .list (.sym name :: args) =>
      match (← env.find? name).map MalVal.strip with
      | some (.fn (.lambda lam)) =>
        if lam.isMacro then
          macroexpand env (← apply env (.fn (.lambda lam)) args)
        else
          return ast
      | _ => return ast
    | _ => return ast

  partial def apply (callerEnv : Env) (head : MalVal)
      (args : List MalVal) : MalIO MalVal := do
    match head.strip with
    | .fn (.builtin name) =>
      Core.callBuiltin name callerEnv eval (apply callerEnv) args
    | .fn (.lambda l)     =>
      let outerEnv ← Env.lookup l.outerId
      let nParams := l.params.length
      let closureEnv ← outerEnv.new
      match l.restParam with
      | none =>
        if nParams ≠ args.length then
          throw (.str s!"arity mismatch: expected {nParams}, got {args.length}")
        for (p, a) in l.params.zip args do
          closureEnv.set p a
      | some restName =>
        if args.length < nParams then
          throw (.str s!"arity mismatch: expected at least {nParams}, got {args.length}")
        let (positional, rest) := (args.take nParams, args.drop nParams)
        for (p, a) in l.params.zip positional do
          closureEnv.set p a
        closureEnv.set restName (.list rest)
      eval closureEnv l.body
    | _ => throw (.str "first item in list is not callable")

  partial def evalDef (env : Env) : List MalVal → MalIO MalVal
    | [.sym name, expr] => do
      let v ← eval env expr
      env.set name v
      return v
    | _ => throw (.str "def!: expected (def! name expr)")

  partial def evalDefmacro (env : Env) : List MalVal → MalIO MalVal
    | [.sym name, expr] => do
      match ← eval env expr with
      | .fn (.lambda l) =>
        let macroFn : MalVal := .fn (.lambda { l with isMacro := true })
        env.set name macroFn
        return macroFn
      | _ => throw (.str "defmacro!: value must be a function")
    | _ => throw (.str "defmacro!: expected (defmacro! name expr)")

  partial def evalLet (env : Env) : List MalVal → MalIO MalVal
    | [bindings, body] => do
      match bindings.toList? with
      | some bs => do
        let letEnv ← env.new
        bindLet letEnv bs
        eval letEnv body
      | none => throw (.str "let*: expected (let* (bindings) body)")
    | _ => throw (.str "let*: expected (let* (bindings) body)")

  partial def bindLet (env : Env) : List MalVal → MalIO Unit
    | []                    => return ()
    | .sym k :: rhs :: rest => do
      let v ← eval env rhs
      env.set k v
      bindLet env rest
    | _ => throw (.str "let*: bindings must be symbol/expr pairs")

  partial def evalDo (env : Env) : List MalVal → MalIO MalVal
    | []      => return .nil
    | [last]  => eval env last
    | x :: xs => do
      let _ ← eval env x
      evalDo env xs

  partial def evalIf (env : Env) : List MalVal → MalIO MalVal
    | [pred, thn]      => do
      if (← eval env pred).isTruthy then eval env thn else return .nil
    | [pred, thn, els] => do
      if (← eval env pred).isTruthy then eval env thn else eval env els
    | _ => throw (.str "if: expected (if pred then) or (if pred then else)")

  partial def evalFn (env : Env) : List MalVal → MalIO MalVal
    | [paramsForm, body] => do
      match paramsForm.toList? with
      | some params => do
        let (paramNames, restParam) ← Core.parseParams params
        let envId ← Env.register env
        return .fn (.lambda { params := paramNames, restParam, body,
                              outerEnvId := envId })
      | none => throw (.str "fn*: expected (fn* (params) body)")
    | _ => throw (.str "fn*: expected (fn* (params) body)")

  partial def evalQuote : List MalVal → MalIO MalVal
    | [arg] => return arg
    | _ => throw (.str "quote: expected 1 argument")

  partial def evalQuasiquote (env : Env) : List MalVal → MalIO MalVal
    | [arg] => eval env (quasiquote arg)
    | _ => throw (.str "quasiquote: expected 1 argument")

  partial def evalMacroexpand (env : Env) : List MalVal → MalIO MalVal
    | [arg] => macroexpand env arg
    | _ => throw (.str "macroexpand: expected 1 argument")

  /-- `(try* expr (catch* binding handler))`: eval `expr`; if it throws, bind
  the thrown `MalVal` to `binding` in a new env frame and eval `handler`.
  The catch* clause is optional — `(try* expr)` is equivalent to `expr`. -/
  partial def evalTry (env : Env) : List MalVal → MalIO MalVal
    | [tryExpr] => eval env tryExpr
    | [tryExpr, .list [.sym "catch*", .sym binding, handler]] =>
      tryCatch (eval env tryExpr) fun thrown => do
        let catchEnv ← env.new
        catchEnv.set binding thrown
        eval catchEnv handler
    | _ => throw (.str "try*: expected (try* expr [(catch* sym handler)])")
end

def READ  (s : String)   : Except String (Option MalVal) := Reader.readStr s
def PRINT (ast : MalVal) : IO String                     := Printer.prStr ast

def rep (env : Env) (s : String) : IO (Option String) := do
  match READ s with
  | .ok none       => return none
  | .ok (some ast) =>
    match ← (eval env ast).run with
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
  loop env stdin stdout

def main (args : List String) : IO Unit := do
  let env ← Core.initialEnv
  let _ ← rep env "(def! not (fn* (a) (if a false true)))"
  let _ ← rep env "(def! load-file (fn* (f) (eval (read-string (str \"(do \" (slurp f) \"\nnil)\")))))"
  let _ ← rep env "(defmacro! cond (fn* (& xs) (if (> (count xs) 0) (list 'if (first xs) (if (> (count xs) 1) (nth xs 1) (throw \"odd number of forms to cond\")) (cons 'cond (rest (rest xs)))))))"
  match args with
  | []           =>
    env.set "*ARGV*" (.list [])
    let stdin  ← IO.getStdin
    let stdout ← IO.getStdout
    loop env stdin stdout
  | file :: rest =>
    let argv : List MalVal := rest.map MalVal.str
    env.set "*ARGV*" (.list argv)
    let _ ← rep env s!"(load-file \"{file}\")"
    return
