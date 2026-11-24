/-! The bundle below: definitions, theorems proved by computation and by induction, an inductive type, a
structure. `lean/ReplayAll.lean` must accept it as it is, and refuse it when `lean/Tamper.lean` has changed a
proof, a statement or a body in the compiled file. -/

def RA.double (n : Nat) : Nat := n + n

def RA.triple (n : Nat) : Nat := n + n + n

theorem RA.double_two : RA.double 2 = 4 := rfl

theorem RA.triple_two : RA.triple 2 = 6 := rfl

inductive RA.Tree where
  | leaf : RA.Tree
  | node : RA.Tree → RA.Tree → RA.Tree

def RA.Tree.size : RA.Tree → Nat
  | .leaf => 1
  | .node a b => a.size + b.size

theorem RA.size_pos (t : RA.Tree) : 0 < t.size := by
  induction t with
  | leaf => exact Nat.one_pos
  | node a b iha _ => exact Nat.add_pos_left iha _

structure RA.Pt where
  x : Nat
  y : Nat

theorem RA.Pt.eta (p : RA.Pt) : RA.Pt.mk p.x p.y = p := rfl

theorem RA.common : 1 + 1 = 2 := by decide
