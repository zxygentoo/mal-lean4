module

mutual
  inductive Value where
    | nil
    | bool    : Bool → Value
    | int     : Int → Value
    | str     : String → Value
    | keyword : String → Value
    | symbol  : String → Value → Value
    | list    : List Value → Value → Value
    | vector  : List Value → Value → Value
    | map     : List (Value × Value) → Value → Value
    | fn      : Closure → Value → Value
    | atom    : Nat → Value

  inductive Closure where
    | builtin : Nat → Closure
    | lambda  : List String → Value → Env → Closure

  inductive Env where
    | mk (current : List (String × Value)) (outer : Option Env)
end

#check (Value.nil : Value)
#check (Closure.builtin 0 : Closure)
