/-! A declaration whose proof is `sorry`: the kernel accepts it, and the pass reports the axiom it names. -/

theorem RA.gap : (1 : Nat) = 1 := sorry
