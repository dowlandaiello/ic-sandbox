import Vm.Ast
import Mathlib.Logic.Basic
import Init.Prelude

structure Agent (n : Nat) where
  id    : CId n
  inner : Expr n

structure AdjacencyMatrix (n : Nat) where
  cells    : Vector (Option (Expr n)) n
  nextFree : List (CId n)

def hasCell {n : Nat} (mat : AdjacencyMatrix n) (id : CId n) : Bool :=
  Option.isSome $ mat.cells[id.val]

def getCell {n : Nat} (mat : AdjacencyMatrix n) (id : CId n) (h1 : hasCell mat id) : Expr n :=
  Option.get (mat.cells[id.val]) h1

def cellHasPort {n : Nat} (mat : AdjacencyMatrix n) (id : CId n) (port : Nat) (h1 : hasCell mat id) : Prop :=
  hasPort (getCell mat id h1) port

def connect {n : Nat} (buff : AdjacencyMatrix n) (fromConn : CId n × Nat) (toConn : CId n × Nat) (h1 : hasCell buff $ fromConn.fst) (h2 : hasCell buff $ toConn.fst) (h3 : cellHasPort buff (fromConn.fst) (fromConn.snd) h1) (h4 : cellHasPort buff (toConn.fst) (toConn.snd) h2) : AdjacencyMatrix n :=
  match fromConn, toConn with
    | (fromId, fromPort), (toId, toPort) =>
      let oldFromCell := getCell buff fromId (by simp [h1])
      let oldToCell   := getCell buff toId (by simp [h2])

      let newFromCell := setPort oldFromCell fromPort (some { id := toId, port :=  toPort }) (by {
        unfold cellHasPort at h3
        unfold oldFromCell
        exact h3
      })
      let newToCell := setPort oldToCell toPort (some { id := fromId, port :=  fromPort }) (by {
        unfold cellHasPort at h4
        unfold oldToCell
        exact h4
      })

      let cells' := Vector.set buff.cells fromId.val newFromCell

      { buff with cells := Vector.set cells' toId.val newToCell }

def push {n : Nat} (buff : AdjacencyMatrix n) (expr : Expr n) (h1 : buff.nextFree ≠ List.nil) : CId n × AdjacencyMatrix n :=
  let x := buff.nextFree.head h1
  let xs := buff.nextFree.tail

  let cells' := Vector.set buff.cells x.val $ some expr
  (x, { buff with cells := cells', nextFree := xs })


def mkCommutationEra {n : Nat} (buff : AdjacencyMatrix n) (port : Port n) (h1 : hasCell buff $ port.id) (h2 : buff.nextFree ≠ List.nil) (h3 : buff.nextFree.head h2 ≠ port.id) (h4 : cellHasPort buff port.id port.port h1) : AdjacencyMatrix n :=
  let idBuff' := push buff (Expr.Era none) h2

  let eraId := idBuff'.fst
  let buff' := idBuff'.snd

  let hasEra : hasCell buff' $ eraId := by {
    unfold buff'
    unfold idBuff'
    unfold eraId
    unfold idBuff'
    unfold hasCell
    unfold push
    simp [Array.getElem_set]
  }
  let hasOther : hasCell buff' $ port.id := by {
    unfold buff'
    unfold idBuff'
    unfold push
    simp
    cases h5 : buff.cells with
    | mk arr => {
      unfold hasCell
      simp
      unfold hasCell at h1
      simp [Array.get_set]
      simp [Fin.val_inj]
      simp [h3]
      simp [h5] at h1
      simp [h1]
    }
  }
  let hasPort0Era : cellHasPort buff' eraId 0 hasEra := by
    unfold eraId
    unfold buff'
    unfold idBuff'
    unfold cellHasPort
    unfold getCell
    unfold push
    simp
    unfold hasPort
    simp

  connect buff' (eraId, 0) (port.id, port.port) hasEra hasOther hasPort0Era (by sorry)

def evalStep {n : Nat} (buff : AdjacencyMatrix n) (lhs : Agent n) (rhs : Agent n) (h1 : buff.nextFree ≠ List.nil) : AdjacencyMatrix n :=
  let mkCommutation := fun (topPorts, botPorts) =>
      let dup    := LazyRef.Create $ Expr.Dup    None None None
      let constr := LazyRef.Create $ Expr.Constr None None None

      -- Both left to right
      do
        let dups    := [dup,    dup]
        let constrs := [constr, constr]

  match lhs.inner, rhs.inner with
    -- Port freeing happens externally
    -- Era >< Era
    | Expr.Era _, Expr.Era _ => []
    -- Alpha >< Alpha
    | Expr.Constr _ _ _, Expr.Constr _ _ _
    | Expr.Dup    _ _ _, Expr.Dup    _ _ _ =>
      List.zip (ports lhs.inner) (ports rhs.inner).reverse
        |> List.map connectPorts
    -- Commutations
    -- Alpha >< Era
    | Expr.Constr _ _ _, Expr.Era    _ =>
      List.map mkCommutationEra $ ports lhs.inner
    | Expr.Era    _,       Expr.Constr _ _ _ =>
      List.map mkCommutationEra $ ports rhs.inner
    -- Alpha >< Beta
    | Expr.Constr _ tP1 tP2, Expr.Dup    _ bP1 bP2 =>
      mkCommutation [tP1, tP2] [bP1, bP2]
    | Expr.Dup    _ bP1 bP2, Expr.Constr _ tP1 tP2 =>
      mkCommutation [bP1, bP2] [tP1, tP2]
