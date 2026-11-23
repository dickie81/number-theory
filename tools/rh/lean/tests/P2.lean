def P2.b : Fin 3 := ⟨1, by decide⟩
theorem P2.t : P2.b = ⟨1, P2.b._proof_1⟩ := rfl
