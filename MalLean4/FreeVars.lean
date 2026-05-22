module

public import MalLean4.Types
open Types

-- Free-variable analysis for closure conversion. Given the names already
-- bound in the enclosing scope, returns the symbols referenced in the AST
-- that aren't bound by an enclosing binder or by any inner binding form.
-- Used at `fn*` time to decide which free variables to snapshot into the
-- closure's captures list.
--
-- Honors mal's binding forms (`let*` is sequential — each RHS sees only
-- previous binders; `fn*` adds its params; `def!` doesn't bind its name in
-- its RHS). Other special forms (`if`, `do`) are pass-through.

namespace FreeVars

mutual

partial def freeVars (binders : List String) : MalVal → List String
  | .sym s    => if binders.contains s then [] else [s]
  | .list xs  => freeVarsList binders xs
  | _         => []

partial def freeVarsList (binders : List String) : List MalVal → List String
  | [.sym "let*", .list bindings, body] => letFrees binders bindings body
  | [.sym "fn*",  .list params,   body] =>
    let paramNames := params.filterMap fun | .sym s => some s | _ => none
    freeVars (binders ++ paramNames) body
  | [.sym "def!", .sym _,         expr] => freeVars binders expr
  | [.sym "if", p, t]                   => freeVars binders p ++ freeVars binders t
  | [.sym "if", p, t, e]                =>
    freeVars binders p ++ freeVars binders t ++ freeVars binders e
  | .sym "do" :: exprs                  => exprs.flatMap (freeVars binders)
  | xs                                  => xs.flatMap (freeVars binders)

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
