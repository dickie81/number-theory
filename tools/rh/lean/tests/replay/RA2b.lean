/-! A bundle of the level of `RA1` that does not import it and states one of its theorems again, with another
proof: Lean lets two modules hold such a pair, and the pass counts it as known and checks its proof. -/

theorem RA.common : 1 + 1 = 2 := rfl
