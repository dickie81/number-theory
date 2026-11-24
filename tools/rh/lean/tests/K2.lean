open A2
def StatX : Prop :=
  ∀ (p : Nat) (K : Fin (p + (1 + 1)))
    (A G : Type) [Inhabited G] (x : G), x = x
theorem usesG : G = 3 := rfl
theorem bound2 : ∀ n : Nat, (fun G => G + 0) n = n := fun _ => rfl
