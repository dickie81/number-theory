/-
# The tests in one pass are the tests

Plain statements. `SieveAdFastDefs.lean` computes the tests of the trees in one pass over the box by the recursor
of lists. Here they are proved equal to the tests that the estimates are proved for, as functions:

* `bpass_eq`: what a pass gives its continuation: the sums of `mSum`, `loSum`, `hiSum` over the first cells, the
  sum `devSum` of the cells' deviations and the length.
* `cellsP_eq`: the cells' check from the deviations is `cellsFrom`.
* `uOfP_eq`, `vOfP_eq`, `coreI2P_eq`, `coreJ2_eq`, `coreJ3_eq`: the checks on numbers.
* `fillTestsF_eq`: **the tests with no window in one pass are `fillTests`.**
* `frozTestsF_eq`: **the tests of the tree over a frozen part in two passes are `frozTests`.**

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

theorem and_and_left (a b c : Bool) : (a && b && (a && c)) = (a && b && c) := by
  cases a <;> cases b <;> rfl

theorem and_and_left4 (a b c d x : Bool) : (a && b && c && d && (a && x)) = (a && b && c && d && x) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem chainOf_length (β bl : List Cell) : (chainOf β.length bl).length = bl.length - β.length := by
  unfold chainOf
  rw [List.length_take]
  omega

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
  simp only [coreJ3, coreJ3P, zoneJP, leavesP, Bool.and_assoc]
  rfl

theorem coreJ2_eq (f : ℕ) (e : Bool) (u v t ρ₁ ρ₂ c0lo c0hi h1s h2s : ℕ) :
    coreJ2 f e u v t ρ₁ ρ₂ c0lo c0hi h1s h2s = (Nat.blt 0 f && coreJ2P f e u v t ρ₁ ρ₂ c0lo c0hi h1s h2s) := by
  simp only [coreJ2, coreJ2P, zoneJP, leavesP, Bool.and_assoc]
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
    simp only [okJ2, chkJ2, coreJ2P, zoneJP, leavesP, Bool.and_assoc]
    rfl
  · simp only [okJ2, chkJ2, ble_false_of_not_le h, Bool.false_and, Bool.and_false]

theorem okJ3F_eq (bl : List Cell) (f : ℕ) (cfg : Cfg) : okJ3F bl f cfg = okJ3 bl f cfg := by
  unfold okJ3F
  rw [bpass_eq]
  simp only [Nat.zero_add]
  by_cases h : bl.length ≤ 13
  · rw [List.take_of_length_le h, cellsP_eq, uOfP_eq, vOfP_eq]
    simp only [okJ3, chkJ3, coreJ3P, zoneJP, leavesP, Bool.and_assoc]
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

/-! ### The tests of the tree over a frozen part -/

theorem okIFF_eq (e₁ e₂ : ℕ) (β bl : List Cell) (cfg : Cfg) : okIFF e₁ e₂ β bl cfg = okIF e₁ e₂ β bl cfg := by
  unfold okIFF
  simp only [lenR_eq]
  rw [bpass_eq]
  simp only [Nat.zero_add]
  rw [bpass_eq]
  simp only [Nat.zero_add, List.take_length, roleP, cofP_eq, cellsP_eq, coreI2P_eq]
  simp only [okIF, loR, hiR, chainOf_length]
  rfl

theorem okJF3F_eq (e₁ e₂ Kb : ℕ) (β bl : List Cell) (f : ℕ) (cfg : Cfg) :
    okJF3F e₁ e₂ Kb β bl f cfg = okJF3 e₁ e₂ Kb β bl f cfg := by
  unfold okJF3F
  simp only [lenR_eq]
  rw [bpass_eq]
  simp only [Nat.zero_add]
  rw [bpass_eq]
  simp only [Nat.zero_add, List.take_length, roleP, cofP_eq, cellsP_eq, uOfP_eq, vOfP_eq]
  simp only [okJF3, coreJ3_eq, loR, hiR, hiRc, chainOf_length]
  rw [and_and_left]
  rfl

theorem okJF2F_eq (e₁ e₂ Kb : ℕ) (β bl : List Cell) (f : ℕ) (cfg : Cfg) :
    okJF2F e₁ e₂ Kb β bl f cfg = okJF2 e₁ e₂ Kb β bl f cfg := by
  unfold okJF2F
  simp only [lenR_eq]
  rw [bpass_eq]
  simp only [Nat.zero_add]
  rw [bpass_eq]
  simp only [Nat.zero_add, List.take_length, roleP, cofP_eq, cellsP_eq, uOfP_eq, vOfP_eq]
  simp only [okJF2, coreJ2_eq, loR, hiR, hiRc, chainOf_length]
  rw [and_and_left4]
  rfl

/-- **The tests of the tree over a frozen part in two passes are `frozTests`.** -/
theorem frozTestsF_eq (e₁ e₂ Kb : ℕ) (β : List Cell) : frozTestsF e₁ e₂ Kb β = frozTests e₁ e₂ Kb β := by
  unfold frozTestsF frozTests
  congr 1
  · funext bl cfg
    exact okIFF_eq e₁ e₂ β bl cfg
  · funext bl f cfg
    rw [okJF3F_eq, okJF2F_eq]

/-- `flipTreeHT` with the tests `frozTests` is `flipTreeH`. -/
theorem flipTreeHT_froz (SK : Cell → List Cell → Strat) (GK : Cell → List Cell → List Cell → ℕ → Option (ℕ × Cfg))
    (fuel : ℕ) : flipTreeHT frozTests SK GK fuel = flipTreeH SK GK fuel := by
  funext ctx β lim h
  cases β <;> rfl

/-- **The hinted bound with the fast tests over the frozen part is `altFH`.** -/
theorem altFHT_fast (SK : Cell → List Cell → Strat) (GK : Cell → List Cell → List Cell → ℕ → Option (ℕ × Cfg))
    (fuel maxlen : ℕ) : altFHT frozTestsF SK GK fuel maxlen = altFH SK GK fuel maxlen := by
  have hT : (frozTestsF : ℕ → ℕ → ℕ → List Cell → Tests) = frozTests := by
    funext e₁ e₂ Kb β
    exact frozTestsF_eq e₁ e₂ Kb β
  funext bl par l h
  rw [hT]
  unfold altFHT altFH flipCostHT flipCostH
  rw [flipTreeHT_froz]

end SieveAd
