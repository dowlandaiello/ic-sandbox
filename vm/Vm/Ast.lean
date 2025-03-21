import Mathlib.Control.Combinators

def CId (n : Nat) := Fin n

instance : ToString (CId (n : Nat)) where
  toString
    | id => s!"{id.val}"

structure Port (n : Nat) where
  id   : CId n
  port : Nat

instance : ToString (Port (n : Nat)) where
  toString
    | ⟨id, port⟩ => s!"({id}, {port})"

inductive Expr (n : Nat) where
  | Era    : Option (Port n) → Expr n
  | Constr : Option (Port n) → Option (Port n) → Option (Port n) → Expr n
  | Dup    : Option (Port n) → Option (Port n) → Option (Port n) → Expr n
  | Var    : String      → Option (Port n) → Expr n

def hasPort {n : Nat}  : Expr n → Nat → Prop
  | Expr.Var _ _, i
  | Expr.Era _, i => i = 0
  | Expr.Constr _ _ _, i => i < 3
  | Expr.Dup _ _ _, i => i < 3

def setPort {n : Nat} (e : Expr n) (i : Nat) (val : Option (Port n)) (h1 : hasPort e i) :=
  match e with
    | Expr.Var name _ => Expr.Var name val
    | Expr.Era _ => Expr.Era val
    | Expr.Constr primary a1 a2 => match Fin.ofNat' 3 i with
       | 0 => Expr.Constr val a1 a2
       | 1 => Expr.Constr primary val a2
       | 2 => Expr.Constr primary a1 val
    | Expr.Dup primary a1 a2 => match Fin.ofNat' 3 i with
       | 0 => Expr.Dup val a1 a2
       | 1 => Expr.Dup primary val a2
       | 2 => Expr.Dup primary a1 val

open Expr

def allPorts {n : Nat} : Expr n → List (Option (Port n))
  | Era    primary        => [primary]
  | Constr primary a b    => [primary, a, b]
  | Dup    primary a b    => [primary, a, b]
  | Var    _ primary      => [primary]

def ports {n : Nat} {_ : Option.isSome ∘ Monad.sequence ∘ allPorts $ e} (e : Expr n) : List (Port n) :=
  allPorts e
    |> List.filterMap id

instance : ToString (Expr (n : Nat)) where
  toString
    | Era    primaryPort      => s!"Era({primaryPort})"
    | Constr primaryPort a b  => s!"Constr({primaryPort}, {a}, {b})"
    | Dup    primaryPort a b  => s!"Dup({primaryPort}, {a}, {b})"
    | Var    name primaryPort => s!"{name}({primaryPort})"
