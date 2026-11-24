import B.RA1

/-! A bundle above `RA1`: its proofs use the statements and the bodies of the bundle below. -/

theorem RA.four : RA.double 2 + 0 = 4 := RA.double_two

theorem RA.node_pos (a b : RA.Tree) : 0 < (RA.Tree.node a b).size := RA.size_pos _

def RA.origin : RA.Pt := ⟨RA.double 0, 0⟩
