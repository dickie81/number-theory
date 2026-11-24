structure Arc where
  n : Nat
theorem Arc.dup (a : Arc) : a.n = a.n := rfl
theorem Arc.uses (a : Arc) : a.n = a.n := a.dup
theorem viaOther : 2 = 2 := _root_.Other.dup
theorem viaNS : 1 = 1 := NS.dup
