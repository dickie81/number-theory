open NS
structure Laws (f : Nat → Nat) : Prop where
  dim : ∀ n, f n = n
  twist : ∀ n, f (twist n) = twist n
  later : twist = twist
  (other more : dim = dim)
theorem uses (f : Nat → Nat) (h : Laws f) : ∀ n, f (NS.twist n) = NS.twist n := h.twist
