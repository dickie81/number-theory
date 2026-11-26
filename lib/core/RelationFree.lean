import Mathlib

/-!
# Relation-free sets of Behrend type

`RelFree T L` says that no three distinct `s₁, s₂, s₃ ∈ T` satisfy `j(s₂ − s₁) = i(s₃ − s₁)` with integers `i ≠ j`,
`0 < |i|, |j| ≤ L`. At level `L = 1` the only pairs are `(i, j) = (±1, ∓1)` and the relation is `s₂ + s₃ = 2s₁`, so
relation-free means free of three-term progressions. For `L ≥ 2` and `N ≥ 1` there is a relation-free
`T ⊆ [0, N)` with `|T| ≥ N·exp(−6√(log N · log(2L + 1)))` (`RelFree.exists_six`).

The set is Behrend's sphere in a box, written in a base large enough for the relation to carry no digits.

* **Digits.** With `K = 2L + 1` and base `B = K·d`, a vector `v ∈ [0, d)^D` is read as `Σ v_ℓ B^ℓ`
  (`Behrend.map`). This is injective on the box (`Behrend.map_injOn`) and lands below `B^D` (`RelFree.map_lt_pow`).
* **No carries.** A relation among three images is `Σ c_ℓ B^ℓ = 0` with `c_ℓ = j(v₂ − v₁)_ℓ − i(v₃ − v₁)_ℓ`, and
  `|c_ℓ| ≤ 2L(d − 1) < B`. Then every `c_ℓ = 0`, since the lowest nonzero digit would be a multiple of `B`
  (`RelFree.digits_eq_zero`). So the digit vectors satisfy the same relation.
* **No line on a sphere.** The vectors of `Behrend.sphere D d k` lie on one Euclidean sphere
  (`Behrend.norm_of_mem_sphere`). The relation reads `(i − j)v₁ + j v₂ − i v₃ = 0`: three nonzero coefficients with
  sum `0`. Two of them share a sign, which makes one vector a strict convex combination of the other two, against
  strict convexity (`RelFree.sphere_relation`, from `norm_combo_lt_of_ne`).
* **Density.** Some sphere holds at least `d^D/(D d²)` points of the box (`Behrend.exists_large_sphere`). Let
  `r = √(log N · log K)`, `D = ⌈r / log K⌉` and `d = ⌊N^{1/D}/K⌋`, so that `B^D ≤ N`. If `r ≥ 4 log K` then
  `N^{1/D} ≥ K²`, so `d ≥ N^{1/D}/(2K)`, and with `D ≤ 2^D` this gives
  `d^D/(D d²) ≥ N/((4K)^D N^{2/D}) ≥ N e^{−6r}`, using `4K ≤ K²`, `D ≤ 2r/log K` and `log N ≤ rD`. If
  `r < 4 log K` then `log N ≤ 4r`, so `N e^{−6r} ≤ 1` and one point is enough.
-/

open Finset Real WithLp

/-- `T` is relation-free at level `L`: no three distinct `s₁, s₂, s₃ ∈ T` satisfy `j(s₂ − s₁) = i(s₃ − s₁)` with
integers `i ≠ j` and `0 < |i|, |j| ≤ L`. -/
def RelFree (T : Finset ℕ) (L : ℕ) : Prop :=
  ∀ s₁ ∈ T, ∀ s₂ ∈ T, ∀ s₃ ∈ T, s₁ ≠ s₂ → s₁ ≠ s₃ → s₂ ≠ s₃ →
    ∀ i j : ℤ, 0 < |i| → |i| ≤ L → 0 < |j| → |j| ≤ L → i ≠ j → j * ((s₂ : ℤ) - s₁) ≠ i * ((s₃ : ℤ) - s₁)

namespace RelFree

/-- A one-point set is relation-free: it has no three distinct elements. -/
theorem singleton (s L : ℕ) : RelFree {s} L := by
  intro s₁ h₁ s₂ h₂ _ _ h₁₂
  rw [Finset.mem_singleton] at h₁ h₂
  exact absurd (h₁.trans h₂.symm) h₁₂

/-- No carries: integer digits with `|c ℓ| < B` and `Σ c ℓ B^ℓ = 0` all vanish, since the lowest nonzero digit would
be a multiple of `B`. -/
theorem digits_eq_zero {B : ℤ} : ∀ {D : ℕ} (c : Fin D → ℤ), (∀ ℓ, |c ℓ| < B) →
    ∑ ℓ, c ℓ * B ^ (ℓ : ℕ) = 0 → c = 0
  | 0, _, _, _ => Subsingleton.elim _ _
  | D + 1, c, hc, h => by
    have hB : 0 < B := (abs_nonneg _).trans_lt (hc 0)
    rw [Fin.sum_univ_succ] at h
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, ← mul_assoc, ← Finset.sum_mul] at h
    have hX : ∑ ℓ : Fin D, c ℓ.succ * B ^ (ℓ : ℕ) = 0 := by
      by_contra hne
      refine (hc 0).not_ge ?_
      rw [eq_neg_of_add_eq_zero_left h, abs_neg, abs_mul, abs_of_pos hB]
      exact le_mul_of_one_le_left hB.le (Int.one_le_abs hne)
    have h0 : c 0 = 0 := by rw [hX, zero_mul, add_zero] at h; exact h
    have hrest := digits_eq_zero (fun ℓ => c ℓ.succ) (fun ℓ => hc _) hX
    funext ℓ
    exact Fin.cases h0 (fun m => congrFun hrest m) ℓ

/-- A vector with entries `< B` is read in base `B` as a number `< B^D`. -/
theorem map_lt_pow {B : ℕ} : ∀ {D : ℕ} (v : Fin D → ℕ), (∀ ℓ, v ℓ < B) → Behrend.map B v < B ^ D
  | 0, v, _ => by simp
  | D + 1, v, hv => by
    rw [Behrend.map_succ', pow_succ]
    have h := map_lt_pow (v ∘ Fin.succ) fun ℓ => hv _
    have h0 := hv 0
    calc v 0 + Behrend.map B (v ∘ Fin.succ) * B < (Behrend.map B (v ∘ Fin.succ) + 1) * B := by
          rw [add_one_mul]; omega
      _ ≤ B ^ D * B := Nat.mul_le_mul_right _ h

section Convex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E] {a b c : E} {r : ℝ}

/-- In a strictly convex space, a point `c` of a sphere is not a strict convex combination
`α a + β b = (α + β) c` (`α, β > 0`) of two distinct points `a, b` of the same sphere. -/
theorem sphere_combo {α β : ℝ} (hab : a ≠ b) (ha : ‖a‖ = r) (hb : ‖b‖ = r) (hc : ‖c‖ = r)
    (hα : 0 < α) (hβ : 0 < β) (h : α • a + β • b = (α + β) • c) : False := by
  have hs : 0 < α + β := add_pos hα hβ
  have hcomb : (α / (α + β)) • a + (β / (α + β)) • b = c := by
    rw [div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, ← smul_add, h, smul_smul, inv_mul_cancel₀ hs.ne',
      one_smul]
  have := norm_combo_lt_of_ne ha.le hb.le hab (div_pos hα hs) (div_pos hβ hs) (by field_simp)
  rw [hcomb, hc] at this
  exact lt_irrefl _ this

/-- No three distinct points of a sphere in a strictly convex space satisfy `α a + β b + γ c = 0` with nonzero
coefficients of sum `0`: two coefficients share a sign, and that makes the third point a strict convex combination of
the other two (`sphere_combo`). -/
theorem sphere_relation {α β γ : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ha : ‖a‖ = r) (hb : ‖b‖ = r)
    (hc : ‖c‖ = r) (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0) (hsum : α + β + γ = 0)
    (h : α • a + β • b + γ • c = 0) : False := by
  rcases hα.lt_or_gt with hα | hα <;> rcases hβ.lt_or_gt with hβ | hβ <;> rcases hγ.lt_or_gt with hγ | hγ
  · linarith
  · exact sphere_combo hab ha hb hc (neg_pos.2 hα) (neg_pos.2 hβ)
      (by linear_combination (norm := module) -h + hsum • c)
  · exact sphere_combo hac ha hc hb (neg_pos.2 hα) (neg_pos.2 hγ)
      (by linear_combination (norm := module) -h + hsum • b)
  · exact sphere_combo hbc.symm hc hb ha hγ hβ
      (by linear_combination (norm := module) h - hsum • a)
  · exact sphere_combo hbc.symm hc hb ha (neg_pos.2 hγ) (neg_pos.2 hβ)
      (by linear_combination (norm := module) -h + hsum • a)
  · exact sphere_combo hac ha hc hb hα hγ
      (by linear_combination (norm := module) h - hsum • b)
  · exact sphere_combo hab ha hb hc hα hβ
      (by linear_combination (norm := module) h - hsum • c)
  · linarith

end Convex

/-- Three distinct points of `Behrend.sphere` satisfy no relation `j(v₂ − v₁) = i(v₃ − v₁)` with nonzero `i ≠ j`:
as points of Euclidean space they lie on one sphere, and `(i − j)v₁ + j v₂ − i v₃ = 0` (`sphere_relation`). -/
theorem sphere_no_relation {D d k : ℕ} {v₁ v₂ v₃ : Fin D → ℕ} (h₁ : v₁ ∈ Behrend.sphere D d k)
    (h₂ : v₂ ∈ Behrend.sphere D d k) (h₃ : v₃ ∈ Behrend.sphere D d k) (h₁₂ : v₁ ≠ v₂) (h₁₃ : v₁ ≠ v₃)
    (h₂₃ : v₂ ≠ v₃) {i j : ℤ} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j)
    (h : ∀ ℓ, j * ((v₂ ℓ : ℤ) - v₁ ℓ) = i * ((v₃ ℓ : ℤ) - v₁ ℓ)) : False := by
  have inj : Function.Injective fun v : Fin D → ℕ => toLp 2 ((↑) ∘ v : Fin D → ℝ) :=
    (toLp_injective 2).comp Nat.cast_injective.comp_left
  refine sphere_relation (inj.ne h₁₂) (inj.ne h₁₃) (inj.ne h₂₃) (Behrend.norm_of_mem_sphere h₁)
    (Behrend.norm_of_mem_sphere h₂) (Behrend.norm_of_mem_sphere h₃) (α := (i : ℝ) - j) (β := j) (γ := -i)
    (sub_ne_zero.2 (Int.cast_injective.ne hij)) (Int.cast_ne_zero.2 hj) (neg_ne_zero.2 (Int.cast_ne_zero.2 hi))
    (by ring) ?_
  ext ℓ
  have := congrArg (Int.cast : ℤ → ℝ) (h ℓ)
  push_cast at this
  simp
  linarith

/-- Behrend's set: a sphere of the box `[0, d)^D`, read in base `(2L + 1)d`, is relation-free at level `L`. The
relation has no carries (`digits_eq_zero`), so it holds for the digit vectors (`sphere_no_relation`). -/
theorem image_sphere (L D d k : ℕ) :
    RelFree ((Behrend.sphere D d k).image (Behrend.map ((2 * L + 1) * d))) L := by
  intro s₁ hs₁ s₂ hs₂ s₃ hs₃ h₁₂ h₁₃ h₂₃ i j hi hiL hj hjL hij heq
  obtain ⟨v₁, hv₁, rfl⟩ := mem_image.1 hs₁
  obtain ⟨v₂, hv₂, rfl⟩ := mem_image.1 hs₂
  obtain ⟨v₃, hv₃, rfl⟩ := mem_image.1 hs₃
  have hlt : ∀ v ∈ Behrend.sphere D d k, ∀ ℓ, v ℓ < d := fun v hv =>
    Behrend.mem_box.1 (Behrend.sphere_subset_box hv)
  have hc := digits_eq_zero (B := ((2 * L + 1) * d : ℕ))
    (fun ℓ => j * ((v₂ ℓ : ℤ) - v₁ ℓ) - i * ((v₃ ℓ : ℤ) - v₁ ℓ)) (fun m => ?_) ?_
  · exact sphere_no_relation hv₁ hv₂ hv₃ (fun h => h₁₂ (congrArg _ h)) (fun h => h₁₃ (congrArg _ h))
      (fun h => h₂₃ (congrArg _ h)) (abs_pos.1 hi) (abs_pos.1 hj) hij fun ℓ => sub_eq_zero.1 (congrFun hc ℓ)
  · have h₁ := hlt v₁ hv₁ m
    have h₂ := hlt v₂ hv₂ m
    have h₃ := hlt v₃ hv₃ m
    have e₂ : |(v₂ m : ℤ) - v₁ m| ≤ d - 1 := abs_sub_le_iff.2 ⟨by omega, by omega⟩
    have e₃ : |(v₃ m : ℤ) - v₁ m| ≤ d - 1 := abs_sub_le_iff.2 ⟨by omega, by omega⟩
    calc |j * ((v₂ m : ℤ) - v₁ m) - i * ((v₃ m : ℤ) - v₁ m)|
        ≤ |j| * |(v₂ m : ℤ) - v₁ m| + |i| * |(v₃ m : ℤ) - v₁ m| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ L * (d - 1) + L * (d - 1) := by gcongr
      _ < ((2 * L + 1) * d : ℕ) := by push_cast; nlinarith
  · simp only [Behrend.map_apply] at heq
    push_cast at heq ⊢
    rw [← sub_eq_zero] at heq
    rw [← heq]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ℓ _ => by ring

/-- The density bound with the constant `6`, for every `N ≥ 1`: Behrend's set with `D = ⌈r / log(2L + 1)⌉` and
`d = ⌊N^{1/D}/(2L + 1)⌋`, `r = √(log N · log(2L + 1))`, or a single point when `r < 4 log(2L + 1)`. -/
theorem exists_six (L N : ℕ) (hL : 2 ≤ L) (hN : 0 < N) : ∃ T : Finset ℕ, (∀ s ∈ T, s < N) ∧ RelFree T L ∧
    (N : ℝ) * exp (-6 * √(log N * log (2 * L + 1))) ≤ T.card := by
  set K : ℝ := 2 * L + 1 with hKdef
  set lam := log N
  set κ := log K
  set r := √(lam * κ)
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hK : 5 ≤ K := by rw [hKdef]; linarith
  have hκ : 0 < κ := log_pos (by linarith)
  have hlam : 0 ≤ lam := log_nonneg (by exact_mod_cast hN)
  have hr : 0 ≤ r := sqrt_nonneg _
  have hr2 : r * r = lam * κ := mul_self_sqrt (mul_nonneg hlam hκ.le)
  have hNexp : exp lam = N := exp_log (by exact_mod_cast hN)
  by_cases hbig : 4 * κ ≤ r
  swap
  · refine ⟨{0}, by simpa using hN, singleton 0 L, ?_⟩
    have : lam ≤ 6 * r := by nlinarith
    rw [card_singleton, Nat.cast_one, ← hNexp, ← exp_add]
    exact exp_le_one_iff.2 (by linarith)
  have hrκ : 4 ≤ r / κ := (le_div_iff₀ hκ).2 (by linarith)
  set D := ⌈r / κ⌉₊
  have hD1 : r / κ ≤ D := Nat.le_ceil _
  have hD2 : (D : ℝ) ≤ 2 * (r / κ) := by
    have := Nat.ceil_lt_add_one (div_nonneg hr hκ.le); linarith
  have hD : (0 : ℝ) < D := by linarith
  have hlamD : lam ≤ r * D := by
    calc lam = r * (r / κ) := by rw [← mul_div_assoc, hr2, mul_div_cancel_right₀ _ hκ.ne']
      _ ≤ r * D := mul_le_mul_of_nonneg_left hD1 hr
  have hlam4 : 4 * r ≤ lam := le_of_mul_le_mul_right (by nlinarith) hκ
  have hDκ : D * (2 * κ) ≤ 4 * r := by
    calc D * (2 * κ) ≤ 2 * (r / κ) * (2 * κ) := by gcongr
      _ = 4 * r := by field_simp; ring
  set x := exp (lam / D)
  have hKK : K * K = exp (2 * κ) := by rw [two_mul, exp_add, exp_log (by linarith)]
  have hxK : K * K ≤ x := by
    rw [hKK]; exact exp_le_exp.2 ((le_div_iff₀ hD).2 (by linarith))
  set d := ⌊x / K⌋₊
  have hdx : (d : ℝ) ≤ x / K := Nat.floor_le (by positivity)
  have hd : x / (2 * K) ≤ d := by
    have := Nat.sub_one_lt_floor (x / K)
    have : K ≤ x / K := (le_div_iff₀ (by linarith)).2 hxK
    rw [mul_comm, ← div_div]; linarith
  have hdx' : (d : ℝ) ≤ x := hdx.trans (div_le_self (exp_pos _).le (by linarith))
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by positivity) hd
  have hxD : x ^ D = N := by rw [← exp_nat_mul, mul_div_cancel₀ _ hD.ne', hNexp]
  have hBN : ((2 * L + 1) * d) ^ D ≤ N := by
    have : (((2 * L + 1) * d : ℕ) : ℝ) ^ D ≤ N := by
      rw [← hxD]; push_cast
      exact pow_le_pow_left₀ (by positivity) ((le_div_iff₀' (by linarith)).1 hdx) D
    exact_mod_cast this
  obtain ⟨k, hk⟩ := Behrend.exists_large_sphere D d
  have hlt : ∀ v ∈ Behrend.sphere D d k, ∀ ℓ, v ℓ < (2 * L + 1) * d := fun v hv ℓ =>
    (Behrend.mem_box.1 (Behrend.sphere_subset_box hv) ℓ).trans_le (Nat.le_mul_of_pos_left d (by omega))
  have hinj : Set.InjOn (Behrend.map ((2 * L + 1) * d)) (Behrend.sphere D d k) :=
    Behrend.map_injOn.mono fun v hv => hlt v hv
  refine ⟨(Behrend.sphere D d k).image (Behrend.map ((2 * L + 1) * d)), ?_, image_sphere L D d k, ?_⟩
  · intro s hs
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hs
    exact (map_lt_pow v (hlt v hv)).trans_le hBN
  rw [card_image_of_injOn hinj]
  refine le_trans ?_ hk
  have h4K : (4 * K) ^ D ≤ exp (4 * r) := by
    calc (4 * K) ^ D ≤ (K * K) ^ D := pow_le_pow_left₀ (by positivity) (by nlinarith) D
      _ = exp (D * (2 * κ)) := by rw [hKK, exp_nat_mul]
      _ ≤ exp (4 * r) := exp_le_exp.2 hDκ
  have h2 : exp (2 * (lam / D)) ≤ exp (2 * r) := by
    gcongr; exact (div_le_iff₀ hD).2 hlamD
  have hD2D : (D : ℝ) ≤ 2 ^ D := by exact_mod_cast Nat.lt_two_pow_self.le
  calc (N : ℝ) * exp (-6 * r) = exp lam / (exp (4 * r) * exp (2 * r)) := by
        rw [← hNexp, ← exp_add, ← exp_add, ← exp_sub]; ring_nf
    _ ≤ exp lam / ((4 * K) ^ D * exp (2 * (lam / D))) := by gcongr
    _ = (x / (2 * K)) ^ D / (2 ^ D * x ^ 2) := by
        have hx2 : x ^ 2 = exp (2 * (lam / D)) := by
          show exp (lam / D) ^ 2 = _
          rw [← exp_nat_mul]; norm_num
        rw [div_pow, hxD, ← hNexp, hx2, show (4 : ℝ) * K = 2 * (2 * K) by ring, mul_pow, div_div]; ring
    _ ≤ d ^ D / (D * d ^ 2) :=
        div_le_div₀ (by positivity) (pow_le_pow_left₀ (by positivity) hd D) (by positivity)
          (mul_le_mul hD2D (pow_le_pow_left₀ hd0.le hdx' 2) (by positivity) (by positivity))
    _ = ((d ^ D : ℕ) : ℝ) / ((D * d ^ 2 : ℕ) : ℝ) := by push_cast; ring

end RelFree
