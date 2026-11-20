import AxiomTools

/-!
# Which tactics bring axioms into a proof

Each theorem below proves a small statement with one tactic, and uses no lemma of core that depends on an axiom
(many do: `Nat.one_ne_zero` and `Nat.succ_ne_zero` depend on `propext`). `#axioms_table` at the end prints, for
each, the axioms its proof depends on; LOG.md, entry 3, has the table.
-/


namespace Spec

theorem t_rfl : 2 + 2 = 4 := rfl
theorem t_decide : ∀ d : Fin 10, 2 ≤ d.val → d.val < 97 → 97 % d.val ≠ 0 := by decide
theorem t_exact (a b : Nat) : a + b = b + a := Nat.add_comm a b
theorem t_induction (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih
theorem t_cases (n : Nat) : n = 0 ∨ ∃ m, n = m + 1 := by
  cases n with
  | zero => exact Or.inl rfl
  | succ m => exact Or.inr ⟨m, rfl⟩
theorem t_rw_eq (a b c : Nat) : a + b + c = c + (b + a) := by
  rw [Nat.add_comm a b, Nat.add_comm]
theorem t_rw_iff (a b : Nat) (h : a < b) : a + 1 ≤ b := by
  rw [← Nat.lt_iff_add_one_le]; exact h
theorem t_simp_only (a : Nat) : a + 0 = a := by simp only [Nat.add_zero]
theorem t_simp_arith (a b : Nat) : a + 0 + b = b + a := by simp [Nat.add_comm]
theorem t_simp_prop (p q : Prop) (hp : p) (hq : q) : p ∧ q := by simp [hp, hq]
theorem t_simp_iff (p : Prop) : p ∧ True ↔ p := by simp
theorem t_omega_lin (x y : Nat) (h : x < y) : x + 1 ≤ y := by omega
theorem t_omega_eq (x y : Nat) : x + y = y + x := by omega
theorem t_omega_neg (x y : Nat) (h : ¬ x ≤ y) : y < x := by omega
theorem t_omega_div (x : Nat) : x / 2 * 2 ≤ x := by omega
theorem t_omega_int (x y : Int) (h : 2 * x = 2 * y + 1) : False := by omega
theorem t_grind_lin (x y : Nat) (h : x < y) : x + 1 ≤ y := by grind
theorem t_grind_ring (x y : Int) : (x + y) * (x + y) = x * x + 2 * x * y + y * y := by grind
theorem t_by_cases_dec (n : Nat) : n = 0 ∨ n ≠ 0 := by
  by_cases h : n = 0
  · exact Or.inl h
  · exact Or.inr h
theorem t_by_cases_prop (p : Prop) : p ∨ ¬ p := by
  by_cases h : p
  · exact Or.inl h
  · exact Or.inr h
theorem t_split (n : Nat) : (if n = 0 then 1 else n) ≠ 0 := by
  split
  · exact Nat.add_one_ne_zero 0
  · assumption
theorem t_simp_only_open (a b : Nat) (h : a = b) : a + 0 = b := by
  simp only [Nat.add_zero]
  exact h
theorem t_decide_dvd : 3 ∣ 12 := by decide
theorem t_decide_exists : ∃ n, n < 10 ∧ n * n = 49 := by decide
theorem t_match : ∀ a b : Nat, a = 0 ∨ b = 0 ∨ ∃ c d, a = c + 1 ∧ b = d + 1
  | 0, _ => Or.inl rfl
  | _, 0 => Or.inr (Or.inl rfl)
  | c + 1, d + 1 => Or.inr (Or.inr ⟨c, d, rfl, rfl⟩)
theorem t_funext : (fun n : Nat => n + 0) = (fun n => n) := by funext n; rfl
theorem t_funext_rfl : (fun n : Nat => n + 0) = (fun n => n) := rfl
theorem t_contradiction (n : Nat) (h : n + 1 = 0) : False := by contradiction
theorem t_injection (a b : Nat) (h : a + 1 = b + 1) : a = b := by injection h
theorem t_subst (a b : Nat) (h : a = b) (h' : 0 < a) : 0 < b := by subst h; exact h'
theorem t_obtain (p : Nat → Prop) (h : ∃ n, p n ∧ 0 < n) : ∃ n, p n := by
  obtain ⟨n, hn, _⟩ := h; exact ⟨n, hn⟩
theorem t_rcases_or (p q : Prop) (h : p ∨ q) : q ∨ p := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h
theorem t_calc (a b c : Nat) (h₁ : a ≤ b) (h₂ : b < c) : a < c :=
  calc a ≤ b := h₁
    _ < c := h₂
theorem t_congr (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by congr
theorem t_ac_rfl (a b c : Nat) : a + b + c = c + (a + b) := by ac_rfl
theorem t_nomatch (h : (0 : Nat) = 1) : False := nomatch h
theorem t_exists : ∃ n : Nat, n * n = 49 := by exists 7
theorem t_conv (a b : Nat) : a + b = b + a := by
  conv => lhs; rw [Nat.add_comm]
theorem t_native_decide : 2 ^ 61 % 1000 = 952 := by native_decide
theorem t_decide_kernel : 2 ^ 61 % 1000 = 952 := by decide +kernel
theorem t_bv_decide (x y : BitVec 8) : x &&& y = y &&& x := by bv_decide
theorem t_norm_cast (a b : Nat) (h : (a : Int) = b) : a = b := by exact_mod_cast h
theorem t_push_cast (a b : Nat) : ((a + b : Nat) : Int) = a + b := by push_cast; rfl
theorem t_exact_decide (n : Nat) (h : n < 3) : n * n < 9 := by
  have : ∀ m : Fin 3, m.val * m.val < 9 := by decide
  exact this ⟨n, h⟩

/-- structural recursion -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
theorem t_structural : fib 10 = 55 := rfl

/-- well-founded recursion, the decrease proved by `omega` -/
def log2' (n : Nat) : Nat := if h : n < 2 then 0 else log2' (n / 2) + 1
decreasing_by omega
theorem t_wf_unfold : log2' 1 = 0 := by rw [log2']; rfl
theorem t_wf_decide : log2' 1024 = 10 := by decide +kernel

/-- well-founded recursion, the decrease proved by a term without axioms -/
def log2'' (n : Nat) : Nat := if h : n < 2 then 0 else log2'' (n / 2) + 1
decreasing_by exact Nat.div_lt_self (Nat.lt_of_lt_of_le (by decide : 0 < 2) (Nat.le_of_not_lt h)) (by decide)
/-- the same by structural recursion on a bound -/
def log2f : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if n < 2 then 0 else log2f f (n / 2) + 1
theorem t_fuel_decide : log2f 1024 1024 = 10 := by decide +kernel
theorem t_wf2_decide : log2'' 1024 = 10 := by decide +kernel

end Spec

#axioms_table Spec

#why Spec.t_split
#why Spec.t_simp_only_open
#why Spec.t_decide_dvd
#why Spec.t_decide_exists
#why Spec.log2''
#why Spec.t_norm_cast
#why Spec.t_ac_rfl
