module

public import MalLean4.Types
open Types

-- Free-variable analysis for closure conversion. Given the names already
-- bound in the enclosing scope, returns the symbols referenced in the AST
-- that aren't bound by an enclosing binder or by any inner binding form.
-- Used at `fn*` time to decide which free variables to snapshot into the
-- closure.
--
-- Honors mal's binding forms (`let*` is sequential — each RHS sees only
-- previous binders; `fn*` adds its params; `def!` doesn't bind its name in
-- its RHS). Other special forms (`if`, `do`) are pass-through. Vectors and
-- hash-maps are scanned element-wise with no binding semantics.

namespace FreeVars

/-- Strip `&` from a param list and return the positional names plus an
optional rest-parameter name. Mirrors `fn*` arity handling. -/
def splitParams (params : List String) : List String × Option String :=
  match params with
  | []  => ([], none)
  | [p] => ([p], none)
  | p :: rest =>
    match rest with
    | "&" :: restName :: _ => ([p], some restName)
    | _ =>
      let (more, rp) := splitParams rest
      (p :: more, rp)

mutual

partial def freeVars (binders : List String) : MalVal → List String
  | .sym s    => if binders.contains s then [] else [s]
  | .list xs  => freeVarsList binders xs
  | .vec  xs  => xs.flatMap (freeVars binders)
  | .map pairs => pairs.flatMap fun (k, v) => freeVars binders k ++ freeVars binders v
  | _ => []

partial def freeVarsList (binders : List String) : List MalVal → List String
  | [.sym "let*", .list bindings, body] => letFrees binders bindings body
  | [.sym "let*", .vec  bindings, body] => letFrees binders bindings body
  | [.sym "fn*",  .list params,   body] => fnFrees binders params body
  | [.sym "fn*",  .vec  params,   body] => fnFrees binders params body
  | [.sym "def!", .sym _,         expr] => freeVars binders expr
  | [.sym "if", p, t]                   => freeVars binders p ++ freeVars binders t
  | [.sym "if", p, t, e]                =>
    freeVars binders p ++ freeVars binders t ++ freeVars binders e
  | .sym "do" :: exprs                  => exprs.flatMap (freeVars binders)
  | xs                                  => xs.flatMap (freeVars binders)

partial def fnFrees (binders : List String) (params : List MalVal)
    (body : MalVal) : List String :=
  let paramNames := params.filterMap fun | .sym s => some s | _ => none
  -- `&` becomes a binder for the rest-parameter name; remove the literal "&".
  let bound := paramNames.filter (· != "&")
  freeVars (binders ++ bound) body

partial def letFrees (binders : List String)
    (bindings : List MalVal) (body : MalVal) : List String :=
  let (finalBinders, bindingFrees) := accumulateLet binders bindings
  bindingFrees ++ freeVars finalBinders body

partial def accumulateLet (binders : List String) :
    List MalVal → List String × List String
  | []                       => (binders, [])
  | .sym k :: rhs :: rest    =>
    let rhsFrees := freeVars binders rhs
    let (finalBinders, restFrees) := accumulateLet (k :: binders) rest
    (finalBinders, rhsFrees ++ restFrees)
  | _ :: _                   => (binders, [])

end

/-- Free symbols in `ast` not bound by `binders` or any inner form. The
result is deduplicated. -/
public def unique (binders : List String) (ast : MalVal) : List String :=
  (freeVars binders ast).eraseDups

end FreeVars
