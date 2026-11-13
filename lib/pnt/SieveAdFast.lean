/-
# The tests in one pass are the tests

Plain statements. `SieveAdFastDefs.lean` computes the tests of the trees in one pass over the box by the recursor
of lists. Here they are compared with the tests that the estimates are proved for:

* `bpass_eq`: what a pass gives its continuation: the sums of `mSum`, `loSum`, `hiSum` over the first cells, the
  sum `devSum` of the cells' deviations and the length.
* `cellsP_eq`: the cells' check from the deviations is `cellsFrom`.
* `uOfP_eq`, `vOfP_eq`, `coreI2P_eq`, `coreJ2_eq`, `coreJ3_eq`: the checks on numbers.
* `fillTestsF_eq`: **the tests with no window in one pass are `fillTests`**, as functions.
* `frozTestsC_okI`, `frozTestsC_okJ`: **the tests of the tree over a frozen part that read the frozen primes once
  for the tree imply `frozTests`**, on a box that is a chain followed by the frozen primes, when the frozen
  primes' cells pass the check `cellsFrom 1`. Those are the boxes that a statement of the tree concerns. The tests
  are not equal as functions: `frozTestsC` checks the cells of the chain only, and not the cells that follow them
  in the box.

The file imports `SieveAdFastDefs.lean` only.
-/
import SieveAdFastDefs

namespace SieveAd

open SieveCert (DEN cdiv)

/-! ### The pass -/

/-- The sum over the cells of `(lo − f) + (hi − lo) + (DEN − hi)`. -/
def devSum (f : ℕ) : List Cell → ℕ
  | [] => 0
  | c :: b => (c.1 - f) + (c.2 - c.1) + (DEN - c.2) + devSum f b

theorem land_one_mul (m y : ℕ) : (m &&& 1) * y = cond (Nat.testBit m 0) y 0 := by
  rw [Nat.and_one_is_mod, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h]

/-- **What a pass gives its continuation.** -/
theorem bpass_eq (f : ℕ) : ∀ (l : List Cell) (j m0 mr m1 a0 b0 ar br a1 b1 aT bT e n : ℕ)
    (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool),
    bpass f l j m0 mr m1 a0 b0 ar br a1 b1 aT bT e n k =
      k (a0 + mSum (fun c => c.1) (l.take j) m0) (b0 + mSum (fun c => c.2) (l.take j) m0)
        (ar + mSum (fun c => c.1) (l.take j) mr) (br + mSum (fun c => c.2) (l.take j) mr)
        (a1 + mSum (fun c => c.1) (l.take j) m1) (b1 + mSum (fun c => c.2) (l.take j) m1)
        (aT + loSum (l.take j)) (bT + hiSum (l.take j)) (e + devSum f l) (n + l.length) := by
  intro l
  induction l with
  | nil =>
    intro j m0 mr m1 a0 b0 ar br a1 b1 aT bT e n k
    show k a0 b0 ar br a1 b1 aT bT e n = _
    simp [mSum, loSum, hiSum, devSum]
  | cons x l ih =>
    intro j m0 mr m1 a0 b0 ar br a1 b1 aT bT e n k
    show bpass f l (j - 1) (m0 / 2) (mr / 2) (m1 / 2) (a0 + (1 - (1 - j)) * (m0 &&& 1) * x.1)
      (b0 + (1 - (1 - j)) * (m0 &&& 1) * x.2) (ar + (1 - (1 - j)) * (mr &&& 1) * x.1)
      (br + (1 - (1 - j)) * (mr &&& 1) * x.2) (a1 + (1 - (1 - j)) * (m1 &&& 1) * x.1)
      (b1 + (1 - (1 - j)) * (m1 &&& 1) * x.2) (aT + (1 - (1 - j)) * x.1) (bT + (1 - (1 - j)) * x.2)
      (e + ((x.1 - f) + (x.2 - x.1) + (DEN - x.2))) (n + 1) k = _
    rw [ih]
    cases j with
    | zero =>
      simp only [Nat.zero_sub, List.take_zero, mSum, loSum, hiSum, devSum, List.length_cons, Nat.sub_self,
        Nat.zero_mul, Nat.add_zero]
      congr 1 <;> omega
    | succ j =>
      have h1 : 1 - (1 - (j + 1)) = 1 := by omega
      simp only [h1, Nat.add_sub_cancel, List.take_succ_cons, mSum, loSum, hiSum, devSum, List.length_cons,
        Nat.one_mul, land_one_mul]
      congr 1 <;> omega

/-! ### The cells' check -/

theorem devSum_ge {f : ℕ} (hf : f ≤ DEN) : ∀ l : List Cell, l.length * (DEN - f) ≤ devSum f l
  | [] => by simp [devSum]
  | c :: b => by
    have ih := devSum_ge hf b
    simp only [devSum, List.length_cons, Nat.succ_mul]
    omega

theorem cellsFrom_iff_dev {f : ℕ} (hf : f ≤ DEN) :
    ∀ l : List Cell, cellsFrom f l = true ↔ devSum f l = l.length * (DEN - f)
  | [] => by simp [cellsFrom, devSum]
  | c :: b => by
    have ih := cellsFrom_iff_dev hf b
    have hge := devSum_ge hf b
    simp only [cellsFrom, Bool.and_eq_true, Nat.ble_eq, ih, devSum, List.length_cons, Nat.succ_mul]
    omega

theorem cellsFrom_cons_false {f : ℕ} (hf : DEN < f) (c : Cell) (b : List Cell) : cellsFrom f (c :: b) = false := by
  cases h : cellsFrom f (c :: b) with
  | false => rfl
  | true =>
    simp only [cellsFrom, Bool.and_eq_true, Nat.ble_eq] at h
    omega

/-- **The cells' check from the deviations is `cellsFrom`.** -/
theorem cellsP_eq (f : ℕ) (l : List Cell) : cellsP f (devSum f l) l.length = cellsFrom f l := by
  unfold cellsP
  by_cases hf : f ≤ DEN
  · have h := cellsFrom_iff_dev hf l
    have e1 : Nat.ble f DEN = true := Nat.ble_eq_true_of_le hf
    cases hc : cellsFrom f l with
    | true =>
      have := h.1 hc
      simp [e1, this]
    | false =>
      have e2 : Nat.beq (devSum f l) (Nat.mul l.length (Nat.sub DEN f)) = false := by
        cases hb : Nat.beq (devSum f l) (Nat.mul l.length (Nat.sub DEN f)) with
        | false => rfl
        | true =>
          rw [h.2 (Nat.eq_of_beq_eq_true hb)] at hc
          cases hc
      rw [e2, Bool.and_false]
  · have e1 : Nat.ble f DEN = false := by
      cases h : Nat.ble f DEN with
      | false => rfl
      | true => exact absurd (Nat.le_of_ble_eq_true h) hf
    cases l with
    | nil => simp [cellsFrom, devSum]
    | cons c b =>
      rw [cellsFrom_cons_false (by omega) c b]
      simp [e1]

theorem lenR_eq : ∀ l : List Cell, lenR l = l.length
  | [] => rfl
  | _ :: b => by
    show Nat.succ (lenR b) = _
    rw [lenR_eq b]
    rfl

/-! ### The checks on numbers -/

theorem ble_false_of_not_le {a b : ℕ} (h : ¬ a ≤ b) : Nat.ble a b = false := by
  cases h' : Nat.ble a b with
  | false => rfl
  | true => exact absurd (Nat.le_of_ble_eq_true h') h

theorem cond_ble (a b : ℕ) {α : Type} (x y : α) : cond (Nat.ble a b) x y = if a ≤ b then x else y := by
  cases h : Nat.ble a b with
  | true =>
    have hle : a ≤ b := Nat.le_of_ble_eq_true h
    simp [hle]
  | false =>
    have hnle : ¬ a ≤ b := fun hle => by
      rw [Nat.ble_eq_true_of_le hle] at h
      cases h
    simp [hnle]

theorem cofP_eq (m nch nb : ℕ) : cofP m nch nb = Nat.testBit (m / 2 ^ nch) nb := by
  show Nat.beq ((m / 2 ^ nch / 2 ^ nb) &&& 1) 1 = _
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ nch / 2 ^ nb) with h | h <;> rw [h] <;> rfl

variable [SieveCert.IBPar]

open SieveCert.IBPar (Lnum Lden)

theorem uOfP_eq (ρ₁ : ℕ) : uOfP ρ₁ = uOf ρ₁ := by
  show cond (Nat.ble (cdiv (2 * Lden * DEN) (3 * Lnum))
      (cdiv (62505 * Lden * DEN + 27637 * Lnum - 27637 * Lnum * ρ₁) (62500 * Lnum)))
    (cdiv (62505 * Lden * DEN + 27637 * Lnum - 27637 * Lnum * ρ₁) (62500 * Lnum)) (cdiv (2 * Lden * DEN) (3 * Lnum)) =
      max (cdiv (2 * Lden * DEN) (3 * Lnum))
        (cdiv (62505 * Lden * DEN + 27637 * Lnum - 27637 * Lnum * ρ₁) (62500 * Lnum))
  rw [cond_ble, Nat.max_def]

theorem vOfP_eq (ρ₂ : ℕ) : vOfP ρ₂ = vOf ρ₂ := by
  show cond (Nat.ble ((3 * Lnum * DEN - 2 * Lden * DEN) / (3 * Lnum) - (ρ₂ + 1))
      ((62500 * Lnum * DEN - 62505 * Lden * DEN - 34863 * Lnum * (ρ₂ + 1)) / (62500 * Lnum)))
    ((3 * Lnum * DEN - 2 * Lden * DEN) / (3 * Lnum) - (ρ₂ + 1))
    ((62500 * Lnum * DEN - 62505 * Lden * DEN - 34863 * Lnum * (ρ₂ + 1)) / (62500 * Lnum)) =
      min ((3 * Lnum * DEN - 2 * Lden * DEN) / (3 * Lnum) - (ρ₂ + 1))
        ((62500 * Lnum * DEN - 62505 * Lden * DEN - 34863 * Lnum * (ρ₂ + 1)) / (62500 * Lnum))
  rw [cond_ble, Nat.min_def]

theorem coreI2P_eq (u v ρ₁ ρ₂ : ℕ) : coreI2P u v ρ₁ ρ₂ = coreI2 u v ρ₁ ρ₂ := rfl

theorem coreJ3_eq (f : ℕ) (e : Bool) (u v t r1 r2 c0lo c0hi h1s h2s : ℕ) :
    coreJ3 f e u v t r1 r2 c0lo c0hi h1s h2s = (Nat.blt 0 f && coreJ3P f e u v t r1 r2 c0lo c0hi h1s h2s) := by
  simp only [coreJ3, coreJ3P, zoneJP, leavesP, leavesL, Bool.and_assoc]
  rfl

theorem coreJ2_eq (f : ℕ) (e : Bool) (u v t ρ₁ ρ₂ c0lo c0hi h1s h2s : ℕ) :
    coreJ2 f e u v t ρ₁ ρ₂ c0lo c0hi h1s h2s = (Nat.blt 0 f && coreJ2P f e u v t ρ₁ ρ₂ c0lo c0hi h1s h2s) := by
  simp only [coreJ2, coreJ2P, zoneJP, leavesP, leavesL, Bool.and_assoc]
  rfl

/-! ### The tests with no window -/

theorem okI2F_eq (bl : List Cell) (cfg : Cfg) : okI2F bl cfg = okI2 bl cfg := by
  unfold okI2F
  rw [bpass_eq]
  simp only [Nat.zero_add]
  by_cases h : bl.length ≤ 13
  · rw [List.take_of_length_le h, cellsP_eq, coreI2P_eq]
    simp only [okI2, chkI2, coreI2, Bool.and_assoc]
  · simp only [okI2, chkI2, ble_false_of_not_le h, Bool.false_and]

theorem okJ2F_eq (bl : List Cell) (f : ℕ) (cfg : Cfg) : okJ2F bl f cfg = okJ2 bl f cfg := by
  unfold okJ2F
  rw [bpass_eq]
  simp only [Nat.zero_add]
  by_cases h : bl.length ≤ 13
  · rw [List.take_of_length_le h, cellsP_eq, uOfP_eq, vOfP_eq]
    simp only [okJ2, chkJ2, coreJ2P, zoneJP, leavesP, leavesL, Bool.and_assoc]
    rfl
  · simp only [okJ2, chkJ2, ble_false_of_not_le h, Bool.false_and, Bool.and_false]

theorem okJ3F_eq (bl : List Cell) (f : ℕ) (cfg : Cfg) : okJ3F bl f cfg = okJ3 bl f cfg := by
  unfold okJ3F
  rw [bpass_eq]
  simp only [Nat.zero_add]
  by_cases h : bl.length ≤ 13
  · rw [List.take_of_length_le h, cellsP_eq, uOfP_eq, vOfP_eq]
    simp only [okJ3, chkJ3, coreJ3P, zoneJP, leavesP, leavesL, Bool.and_assoc]
    rfl
  · simp only [okJ3, chkJ3, ble_false_of_not_le h, Bool.false_and, Bool.and_false]

/-- **The tests with no window in one pass are `fillTests`.** -/
theorem fillTestsF_eq : (fillTestsF : Tests) = fillTests := by
  unfold fillTestsF fillTests
  congr 1
  · funext bl cfg
    exact okI2F_eq bl cfg
  · funext bl f cfg
    rw [okJ3F_eq, okJ2F_eq]

/-! ### The tests of the tree over a frozen part, the frozen primes read once for each tree -/

omit [SieveCert.IBPar] in
theorem canonN_eq {α : Type} (m : ℕ) (k : ℕ → α) : canonN m k = k m := by
  cases m <;> rfl

omit [SieveCert.IBPar] in
theorem msumP_eq : ∀ (l : List Cell) (m a b : ℕ),
    msumP l m a b = (a + mSum (fun c => c.1) l m, b + mSum (fun c => c.2) l m)
  | [], _, _, _ => rfl
  | x :: l, m, a, b => by
    show msumP l (m / 2) (a + (m &&& 1) * x.1) (b + (m &&& 1) * x.2) = _
    rw [msumP_eq l]
    simp only [mSum, land_one_mul, Nat.add_assoc]

omit [SieveCert.IBPar] in
/-- **What the pass over the chain gives its continuation**: the sums over the first `j` cells. -/
theorem cpass_eq (f : ℕ) : ∀ (l : List Cell) (j m0 mr m1 a0 b0 ar br a1 b1 bT e n : ℕ)
    (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool),
    cpass f l j m0 mr m1 a0 b0 ar br a1 b1 bT e n k =
      k (a0 + mSum (fun c => c.1) (l.take j) m0) (b0 + mSum (fun c => c.2) (l.take j) m0)
        (ar + mSum (fun c => c.1) (l.take j) mr) (br + mSum (fun c => c.2) (l.take j) mr)
        (a1 + mSum (fun c => c.1) (l.take j) m1) (b1 + mSum (fun c => c.2) (l.take j) m1)
        (bT + hiSum (l.take j)) (e + devSum f (l.take j)) (n + (l.take j).length) := by
  intro l
  induction l with
  | nil =>
    intro j m0 mr m1 a0 b0 ar br a1 b1 bT e n k
    show k a0 b0 ar br a1 b1 bT e n = _
    simp [mSum, hiSum, devSum]
  | cons x l ih =>
    intro j m0 mr m1 a0 b0 ar br a1 b1 bT e n k
    cases j with
    | zero =>
      show k a0 b0 ar br a1 b1 bT e n = _
      simp [mSum, hiSum, devSum]
    | succ j =>
      show cpass f l (j + 1 - 1) (m0 / 2) (mr / 2) (m1 / 2) (a0 + (m0 &&& 1) * x.1) (b0 + (m0 &&& 1) * x.2)
        (ar + (mr &&& 1) * x.1) (br + (mr &&& 1) * x.2) (a1 + (m1 &&& 1) * x.1) (b1 + (m1 &&& 1) * x.2) (bT + x.2)
        (e + ((x.1 - f) + (x.2 - x.1) + (DEN - x.2))) (n + 1) k = _
      rw [ih]
      simp only [Nat.add_sub_cancel, List.take_succ_cons, mSum, hiSum, devSum, List.length_cons, land_one_mul]
      congr 1 <;> omega

omit [SieveCert.IBPar] in
theorem cellsFrom_append (f : ℕ) : ∀ l₁ l₂ : List Cell, cellsFrom f (l₁ ++ l₂) = (cellsFrom f l₁ && cellsFrom f l₂)
  | [], l₂ => by simp [cellsFrom]
  | c :: b, l₂ => by
    show (Nat.ble f c.1 && Nat.ble c.1 c.2 && Nat.ble c.2 DEN && cellsFrom f (b ++ l₂)) =
      (Nat.ble f c.1 && Nat.ble c.1 c.2 && Nat.ble c.2 DEN && cellsFrom f b && cellsFrom f l₂)
    rw [cellsFrom_append f b l₂]
    simp only [Bool.and_assoc]

omit [SieveCert.IBPar] in
/-- A floor at most `lomP` of the cells is at most their lower ends: the cells' check at one floor gives it at
that one. -/
theorem cellsFrom_of_lomP {f g : ℕ} : ∀ (l : List Cell) (a : ℕ), cellsFrom g l = true → f ≤ lomP l a →
    cellsFrom f l = true ∧ lomP l a ≤ a
  | [], a, _, _ => ⟨rfl, Nat.le_refl a⟩
  | x :: l, a, h, hf => by
    have hf' : f ≤ lomP l (a - (a - x.1)) := hf
    simp only [cellsFrom, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨hc, hle⟩ := cellsFrom_of_lomP l (a - (a - x.1)) h.2 hf'
    refine ⟨?_, ?_⟩
    · simp only [cellsFrom, Bool.and_eq_true, Nat.ble_eq]
      refine ⟨⟨⟨?_, h.1.1.2⟩, h.1.2⟩, hc⟩
      omega
    · show lomP l (a - (a - x.1)) ≤ a
      omega

omit [SieveCert.IBPar] in
theorem chainOf_app (ch β : List Cell) : chainOf β.length (ch ++ β) = ch := by
  unfold chainOf
  rw [List.length_append, Nat.add_sub_cancel]
  exact List.take_left' rfl

omit [SieveCert.IBPar] in
theorem lenR_app_sub (ch β : List Cell) : Nat.sub (lenR (ch ++ β)) β.length = ch.length := by
  rw [lenR_eq, List.length_append]
  show ch.length + β.length - β.length = ch.length
  omega

/-- **`okIFC` implies `okIF`** on a box that is a chain followed by the frozen primes, whose cells pass the
check. -/
theorem okIFC_imp (e₁ e₂ : ℕ) (β ch : List Cell) (cfg : Cfg) (hβ : cellsFrom 1 β = true)
    (h : okIFC e₁ e₂ β (loSum β) (hiSum β) β.length (ch ++ β) cfg = true) : okIF e₁ e₂ β (ch ++ β) cfg = true := by
  unfold okIFC at h
  simp only [lenR_app_sub] at h
  rw [cpass_eq] at h
  simp only [canonN_eq, roleB, msumP_eq, cofP_eq, Nat.zero_add, List.take_left' rfl, cellsP_eq, coreI2P_eq,
    Nat.pow_zero, Nat.div_one] at h
  simp only [okIF, loR, hiR, chainOf_app, cellsFrom_append, hβ, Bool.and_true]
  exact h

/-- **`okJF3C` implies `okJF3`** on a box that is a chain followed by the frozen primes, whose cells pass the
check, for `lomβ` their least lower end. -/
theorem okJF3C_imp (e₁ e₂ Kb : ℕ) (β ch : List Cell) (f : ℕ) (cfg : Cfg) (hβ : cellsFrom 1 β = true)
    (h : okJF3C e₁ e₂ Kb β (loSum β) (hiSum β) β.length (lomP β DEN) (ch ++ β) f cfg = true) :
    okJF3 e₁ e₂ Kb β (ch ++ β) f cfg = true := by
  unfold okJF3C at h
  simp only [lenR_app_sub] at h
  rw [cpass_eq] at h
  simp only [canonN_eq, roleB, msumP_eq, cofP_eq, Nat.zero_add, List.take_left' rfl, cellsP_eq, uOfP_eq, vOfP_eq,
    Nat.pow_zero, Nat.div_one] at h
  simp only [okJF3, coreJ3_eq, loR, hiR, hiRc, chainOf_app, cellsFrom_append]
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨hA, hC⟩, hL⟩, hcore⟩ := h
  rw [Nat.ble_eq] at hL
  exact ⟨⟨hA, hC, (cellsFrom_of_lomP β DEN hβ hL).1⟩, hA, hcore⟩

/-- **`okJF2C` implies `okJF2`** on a box that is a chain followed by the frozen primes, whose cells pass the
check, for `lomβ` their least lower end. -/
theorem okJF2C_imp (e₁ e₂ Kb : ℕ) (β ch : List Cell) (f : ℕ) (cfg : Cfg) (hβ : cellsFrom 1 β = true)
    (h : okJF2C e₁ e₂ Kb β (loSum β) (hiSum β) β.length (lomP β DEN) (ch ++ β) f cfg = true) :
    okJF2 e₁ e₂ Kb β (ch ++ β) f cfg = true := by
  unfold okJF2C at h
  simp only [lenR_app_sub] at h
  rw [cpass_eq] at h
  simp only [canonN_eq, roleB, msumP_eq, cofP_eq, Nat.zero_add, List.take_left' rfl, cellsP_eq, uOfP_eq, vOfP_eq,
    Nat.pow_zero, Nat.div_one] at h
  simp only [okJF2, coreJ2_eq, loR, hiR, hiRc, chainOf_app, cellsFrom_append]
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨hA, hC⟩, hL⟩, hS⟩, hR⟩, hcore⟩ := h
  rw [Nat.ble_eq] at hL
  exact ⟨⟨⟨⟨hA, hC, (cellsFrom_of_lomP β DEN hβ hL).1⟩, hS⟩, hR⟩, hA, hcore⟩

/-- **The tests that read the frozen primes once for each tree imply `frozTests`**, on a box that is a chain
followed by the frozen primes, whose cells pass the check: for the term of the box. -/
theorem frozTestsC_okI (e₁ e₂ Kb : ℕ) (β ch : List Cell) (cfg : Cfg) (hβ : cellsFrom 1 β = true)
    (h : (frozTestsC e₁ e₂ Kb β (loSum β) (hiSum β) β.length (lomP β DEN)).okI (ch ++ β) cfg = true) :
    (frozTests e₁ e₂ Kb β).okI (ch ++ β) cfg = true :=
  okIFC_imp e₁ e₂ β ch cfg hβ h

/-- The same for the terms at a floor. -/
theorem frozTestsC_okJ (e₁ e₂ Kb : ℕ) (β ch : List Cell) (f : ℕ) (cfg : Cfg) (hβ : cellsFrom 1 β = true)
    (h : (frozTestsC e₁ e₂ Kb β (loSum β) (hiSum β) β.length (lomP β DEN)).okJ (ch ++ β) f cfg = true) :
    (frozTests e₁ e₂ Kb β).okJ (ch ++ β) f cfg = true := by
  have h' : cond (Nat.beq cfg.kind 2) (okJF3C e₁ e₂ Kb β (loSum β) (hiSum β) β.length (lomP β DEN) (ch ++ β) f cfg)
      (okJF2C e₁ e₂ Kb β (loSum β) (hiSum β) β.length (lomP β DEN) (ch ++ β) f cfg) = true := h
  show cond (Nat.beq cfg.kind 2) (okJF3 e₁ e₂ Kb β (ch ++ β) f cfg) (okJF2 e₁ e₂ Kb β (ch ++ β) f cfg) = true
  cases hk : Nat.beq cfg.kind 2 with
  | true =>
    rw [hk] at h'
    exact okJF3C_imp e₁ e₂ Kb β ch f cfg hβ h'
  | false =>
    rw [hk] at h'
    exact okJF2C_imp e₁ e₂ Kb β ch f cfg hβ h'

end SieveAd
