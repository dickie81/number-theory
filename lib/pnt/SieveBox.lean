/-
# The share of a box of prime intervals

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. A box is `m + 1` intervals of exponents `[a_t, a_t + w_t)`, in units of `1/DEN`; `boxP x a w` is the
set of primes `p` with `x^{a/DEN} ≤ p < x^{(a + w)/DEN}`, and `SB x a w` the sum `Σ Ψ(x/∏rt, rt_last)` over the tuples
`rt` of primes in the box's intervals.

* `mem_boxP`, `evLe_box_tr`, `evLe_box_ex`: the box's primes by their exponents, and as `SieveRough.evLe_cell_tr` and
  `evLe_cell_ex` for an interval: `Σ 1/p ≤ trB(a, w) + o(1)` and `log x · Σ 1/(p log p) ≤ exB(a, w) + o(1)`.
* `EvLe.prod`: `SieveRough.EvLe` holds for finite products of nonnegative functions.
* `shareBox`: **the share of a box.** If the intervals' lower ends are positive, the box fits
  (`s + t + W ≤ DEN`, with `s` the sum of the lower ends but the last, `t` the last, `W` the widths' sum), and
  `B ≥ (omKw s t W w_last/K)·∏_{t < m} trB(a_t, w_t)·exB(a_last, w_last)`, then for every `δ > 0`, eventually
  `SB x a w ≤ (B + δ)·x/log x`. The proof is that of `SieveRough.share6`, for any number of intervals.

The file imports `SieveRough.lean`.
-/
import SieveRough

open Real Filter Finset SieveCert

namespace SieveRough

/-! ### The primes of an interval -/

/-- The primes `p` with `x^{a/DEN} ≤ p < x^{(a + w)/DEN}`. -/
noncomputable def boxP (x : ℝ) (a w : ℕ) : Finset ℕ := primesIn (x ^ ((a : ℝ) / DEN)) (x ^ (((a : ℝ) + w) / DEN))

/-- A prime lies in `boxP x a w` exactly when its exponent `log p/log x` lies in `[a, a + w)/DEN`. -/
theorem mem_boxP {x : ℝ} (hx : 1 < x) {a w p : ℕ} :
    p ∈ boxP x a w ↔ p.Prime ∧ (a : ℝ) ≤ Real.log p / Real.log x * DEN ∧
      Real.log p / Real.log x * DEN < (a : ℝ) + w := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hD := DEN_pos'
  rw [boxP, mem_primesIn]
  refine and_congr_right fun hp => ?_
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have key : ∀ r : ℝ, x ^ r ≤ p ↔ r * DEN ≤ Real.log p / Real.log x * DEN := by
    intro r
    rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hx0 r) hp0, Real.log_rpow hx0,
      mul_le_mul_iff_of_pos_right hD, le_div_iff₀ hlx]
  have key' : ∀ r : ℝ, (p : ℝ) < x ^ r ↔ Real.log p / Real.log x * DEN < r * DEN := by
    intro r
    rw [← not_le, key, not_le]
  rw [key, key', div_mul_cancel₀ _ hD.ne', div_mul_cancel₀ _ hD.ne']

/-- An interval's `Σ 1/p` is at most the trapezoid bound `trB(a, w)` of `log(1 + w/a)`, up to `o(1)`. -/
theorem evLe_box_tr {a w : ℕ} (ha : 0 < a) : EvLe (fun x => ∑ p ∈ boxP x a w, 1 / (p : ℝ)) (trB a w) := by
  have hek : (0 : ℝ) < a := by exact_mod_cast ha
  have hH : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  have hD := DEN_pos'
  have ha' : (0 : ℝ) < (a : ℝ) / DEN := div_pos hek hD
  have hac : (a : ℝ) / DEN ≤ ((a : ℝ) + w) / DEN := div_le_div_of_nonneg_right (by linarith) hD.le
  have hlog : Real.log (((a : ℝ) + w) / DEN) - Real.log ((a : ℝ) / DEN) ≤ trB a w := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have heq : ((a : ℝ) + w) / DEN / ((a : ℝ) / DEN) = ((a : ℝ) + w) / a := by field_simp
    rw [heq]
    have h1 : (1 : ℝ) ≤ ((a : ℝ) + w) / a := by rw [le_div_iff₀ hek]; linarith
    have h := SieveOmegaB.log_le_half_sub_inv h1
    have h2 : (((a : ℝ) + w) / a - (((a : ℝ) + w) / a)⁻¹) / 2 = trB a w := by
      unfold trB; field_simp; ring
    linarith
  intro δ hδ
  filter_upwards [evLe_sum_inv ha' hac δ hδ] with x hx
  exact le_trans hx (by linarith)

/-- An interval's `log x · Σ 1/(p log p)` is at most `exB(a, w) = w·DEN/(a(a + w))`, up to `o(1)`. -/
theorem evLe_box_ex {a w : ℕ} (ha : 0 < a) :
    EvLe (fun x => Real.log x * ∑ p ∈ boxP x a w, 1 / ((p : ℝ) * Real.log p)) (exB a w) := by
  have hek : (0 : ℝ) < a := by exact_mod_cast ha
  have hH : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  have hD := DEN_pos'
  have ha' : (0 : ℝ) < (a : ℝ) / DEN := div_pos hek hD
  have hac : (a : ℝ) / DEN ≤ ((a : ℝ) + w) / DEN := div_le_div_of_nonneg_right (by linarith) hD.le
  have hle : 1 / ((a : ℝ) / DEN) - 1 / (((a : ℝ) + w) / DEN) = exB a w := by
    unfold exB; field_simp; ring
  intro δ hδ
  filter_upwards [evLe_sum_inv_log ha' hac δ hδ] with x hx
  exact le_trans hx (by linarith)

/-- `EvLe` holds for finite products of eventually nonnegative functions. -/
theorem EvLe.prod {m : ℕ} (S : Fin m → ℝ → ℝ) (P : Fin m → ℝ) (hP : ∀ t, 0 ≤ P t)
    (hS0 : ∀ t, ∀ᶠ x : ℝ in atTop, 0 ≤ S t x) (hS : ∀ t, EvLe (S t) (P t)) :
    EvLe (fun x => ∏ t, S t x) (∏ t, P t) := by
  induction m with
  | zero =>
    intro δ hδ
    exact Filter.Eventually.of_forall fun x => by simp; linarith
  | succ m ih =>
    have h := ih (fun t => S t.succ) (fun t => P t.succ) (fun t => hP t.succ) (fun t => hS0 t.succ)
      (fun t => hS t.succ)
    have h0 : ∀ᶠ x : ℝ in atTop, 0 ≤ ∏ t : Fin m, S t.succ x := by
      filter_upwards [Filter.eventually_all.2 fun t : Fin m => hS0 t.succ] with x hx
      exact Finset.prod_nonneg fun t _ => hx t
    have hm := EvLe.mul (hP 0) (Finset.prod_nonneg fun t _ => hP t.succ) (hS0 0) h0 (hS 0) h
    simp only [Fin.prod_univ_succ]
    exact hm

/-! ### The share of a box -/

/-- The sum `Σ Ψ(x/∏rt, rt_last)` over the tuples `rt` of primes in the box's intervals. -/
noncomputable def SB (x : ℝ) {m : ℕ} (a w : Fin (m + 1) → ℕ) : ℝ :=
  ∑ rt ∈ Fintype.piFinset (fun t => boxP x (a t) (w t)), (Psi (x / (∏ t, rt t : ℕ)) (rt (Fin.last m)) : ℝ)

theorem SB_nonneg (x : ℝ) {m : ℕ} (a w : Fin (m + 1) → ℕ) : 0 ≤ SB x a w :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- **The share of a box.** For `m + 1` intervals with positive lower ends that fit (`s + t + W ≤ DEN`) and
`B ≥ (omKw s t W w_last/K)·∏_{t<m} trB(a_t, w_t)·exB(a_last, w_last)`: for every `δ > 0`, eventually
`SB x a w ≤ (B + δ)·x/log x`. -/
theorem shareBox {m : ℕ} (a w : Fin (m + 1) → ℕ) (ha : ∀ t, 0 < a t)
    (hfit : (∑ t : Fin m, a t.castSucc) + a (Fin.last m) + ∑ t, w t ≤ DEN) {B : ℝ}
    (hB : (omKw (∑ t : Fin m, a t.castSucc) (a (Fin.last m)) (∑ t, w t) (w (Fin.last m)) : ℝ) / K *
      ((∏ t : Fin m, trB (a t.castSucc) (w t.castSucc)) * exB (a (Fin.last m)) (w (Fin.last m))) ≤ B)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, SB x a w ≤ (B + δ) * (x / Real.log x) := by
  have hD := DEN_pos'
  have hK := K_pos'
  set s : ℕ := ∑ t : Fin m, a t.castSucc with hs
  set tl : ℕ := a (Fin.last m) with htl
  set wl : ℕ := w (Fin.last m) with hwl
  set W : ℕ := ∑ t, w t with hW
  have htl0 : 0 < tl := ha _
  have htl' : (0 : ℝ) < tl := by exact_mod_cast htl0
  obtain ⟨Wc, hWc⟩ : ∃ Wc, Wc = (omKw s tl W wl : ℝ) / K := ⟨_, rfl⟩
  have hWc0 : 0 ≤ Wc := by rw [hWc]; positivity
  have hPt : ∀ t : Fin m, (0 : ℝ) ≤ trB (a t.castSucc) (w t.castSucc) := fun t => trB_nonneg _ _
  have hPl : (0 : ℝ) ≤ exB tl wl := exB_nonneg _ _
  have hP0 : (0 : ℝ) ≤ (∏ t : Fin m, trB (a t.castSucc) (w t.castSucc)) * exB tl wl :=
    mul_nonneg (Finset.prod_nonneg fun t _ => hPt t) hPl
  have hprod := EvLe.prod (fun t x => ∑ p ∈ boxP x (a t.castSucc) (w t.castSucc), 1 / (p : ℝ))
    (fun t => trB (a t.castSucc) (w t.castSucc)) hPt
    (fun t => Filter.Eventually.of_forall fun x => sum_inv_nonneg _) (fun t => evLe_box_tr (ha _))
  have hR := EvLe.mul (Finset.prod_nonneg fun t _ => hPt t) hPl
    (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun t _ => sum_inv_nonneg _)
    (ev_log_mul_nonneg fun x => boxP x tl wl) hprod (evLe_box_ex (w := wl) htl0)
  refine evLe_finish hWc0 hP0 (by rw [hWc]; exact hB) hR (fun ε hε => ?_) hδ
  obtain ⟨z₀, hz₀⟩ := psi_le (2 * DEN / tl) hε
  have hb : (0 : ℝ) < (tl : ℝ) / DEN := div_pos htl' hD
  filter_upwards [eventually_gt_atTop 1, Real.tendsto_log_atTop.eventually_gt_atTop (DEN * Real.log 2),
    (tendsto_rpow_atTop hb).eventually_ge_atTop (z₀ : ℝ)] with x hx1 hlx2 hxz
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hτ : Real.log 2 / Real.log x * DEN < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one hlx]; linarith
  -- each tuple
  have hterm : ∀ rt ∈ Fintype.piFinset (fun t => boxP x (a t) (w t)),
      (Psi (x / (∏ t, rt t : ℕ)) (rt (Fin.last m)) : ℝ) ≤
        (Wc + ε) * (x / ((∏ t : Fin m, (rt t.castSucc : ℝ)) * rt (Fin.last m) * Real.log (rt (Fin.last m)))) := by
    intro rt hrt
    rw [Fintype.mem_piFinset] at hrt
    have hmem := fun t => (mem_boxP hx1).1 (hrt t)
    have hp := (hmem (Fin.last m)).1
    have hz : z₀ ≤ rt (Fin.last m) := by
      have h1 : (z₀ : ℝ) ≤ rt (Fin.last m) := le_trans hxz (mem_primesIn.1 (hrt (Fin.last m))).2.1
      exact_mod_cast h1
    have hpos : ∀ t, (0 : ℝ) < rt t := fun t => by exact_mod_cast (hmem t).1.pos
    have hd1 : (1 : ℝ) ≤ ∏ t : Fin m, (rt t.castSucc : ℝ) :=
      Finset.one_le_prod₀ fun t _ => by exact_mod_cast (hmem t.castSucc).1.one_lt.le
    have hlogd : Real.log (∏ t : Fin m, (rt t.castSucc : ℝ)) / Real.log x * DEN =
        ∑ t : Fin m, Real.log (rt t.castSucc) / Real.log x * DEN := by
      rw [Real.log_prod (fun t _ => (hpos t.castSucc).ne'), Finset.sum_div, Finset.sum_mul]
    have hcast : ((∏ t, rt t : ℕ) : ℝ) = (∏ t : Fin m, (rt t.castSucc : ℝ)) * rt (Fin.last m) := by
      push_cast
      rw [Fin.prod_univ_castSucc]
    rw [hcast, hWc]
    refine psi_point_w (s := s) (t := tl) (W := W) (w := wl) htl0 hz₀ hx1 hτ hd1 hp.two_le hz ?_
      (hmem (Fin.last m)).2.1 (hmem (Fin.last m)).2.2.le ?_ ?_
    · rw [hlogd, hs]
      push_cast
      exact Finset.sum_le_sum fun t _ => (hmem t.castSucc).2.1
    · rw [add_mul, hlogd, hs, hW, Fin.sum_univ_castSucc (f := fun t => w t)]
      push_cast
      have h1 : ∑ t : Fin m, Real.log (rt t.castSucc) / Real.log x * DEN ≤
          ∑ t : Fin m, ((a t.castSucc : ℝ) + w t.castSucc) :=
        Finset.sum_le_sum fun t _ => (hmem t.castSucc).2.2.le
      have h2 := (hmem (Fin.last m)).2.2
      rw [Finset.sum_add_distrib] at h1
      linarith
    · exact_mod_cast hfit
  -- the sum
  set φ : Fin (m + 1) → ℕ → ℝ := fun t p => if t = Fin.last m then Real.log x / ((p : ℝ) * Real.log p) else 1 / (p : ℝ)
    with hφ
  have hterm_eq : ∀ rt ∈ Fintype.piFinset (fun t => boxP x (a t) (w t)),
      (Wc + ε) * (x / ((∏ t : Fin m, (rt t.castSucc : ℝ)) * rt (Fin.last m) * Real.log (rt (Fin.last m)))) =
        (Wc + ε) * (x / Real.log x) * ∏ t, φ t (rt t) := by
    intro rt hrt
    rw [Fintype.mem_piFinset] at hrt
    have hmem := fun t => (mem_boxP hx1).1 (hrt t)
    have hpos : ∀ t, (0 : ℝ) < rt t := fun t => by exact_mod_cast (hmem t).1.pos
    have hD0 : (∏ t : Fin m, (rt t.castSucc : ℝ)) ≠ 0 := (Finset.prod_pos fun t _ => hpos t.castSucc).ne'
    have hL0 : Real.log (rt (Fin.last m)) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (hmem (Fin.last m)).1.one_lt)).ne'
    have hp0 : (rt (Fin.last m) : ℝ) ≠ 0 := (hpos _).ne'
    rw [Fin.prod_univ_castSucc]
    simp only [hφ, Fin.castSucc_ne_last, ite_false, ite_true]
    rw [Finset.prod_div_distrib, Finset.prod_const_one]
    have := hlx.ne'
    field_simp
  have hsum_eq : ∑ rt ∈ Fintype.piFinset (fun t => boxP x (a t) (w t)),
      (Wc + ε) * (x / ((∏ t : Fin m, (rt t.castSucc : ℝ)) * rt (Fin.last m) * Real.log (rt (Fin.last m)))) =
      (Wc + ε) * (x / Real.log x) * ((∏ t : Fin m, ∑ p ∈ boxP x (a t.castSucc) (w t.castSucc), 1 / (p : ℝ)) *
        (Real.log x * ∑ p ∈ boxP x tl wl, 1 / ((p : ℝ) * Real.log p))) := by
    rw [Finset.sum_congr rfl hterm_eq, ← Finset.mul_sum, ← Finset.prod_univ_sum, Fin.prod_univ_castSucc]
    simp only [hφ, Fin.castSucc_ne_last, ite_false, ite_true]
    congr 2
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  calc SB x a w ≤ ∑ rt ∈ Fintype.piFinset (fun t => boxP x (a t) (w t)),
        (Wc + ε) * (x / ((∏ t : Fin m, (rt t.castSucc : ℝ)) * rt (Fin.last m) * Real.log (rt (Fin.last m)))) :=
        Finset.sum_le_sum hterm
    _ = _ := hsum_eq

end SieveRough
