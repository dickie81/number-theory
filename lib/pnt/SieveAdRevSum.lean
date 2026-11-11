/-
# Role reversal: the cost of a reversal bounds the term

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. For a box `[c3, c2, c1]` of three primes that passes `SieveAd.revOK` (`SieveAdRevDefs.lean`):

* `Q_in_iq2`: in an atoms' box with a cofactor of two primes, the larger lies in its cell `iq2` whenever the others
  lie in theirs and the product is in the range of the condition. `famK_cutQ`: so a sum over the tuples of such a
  box with the smaller prime in `[a, t)` is the sum over `[a, m)` plus the sum over `[m, t)`.
* `QBd`: the three atoms' boxes with a cofactor of two primes, the smaller in a cell `d`, are bounded at a cost.
  `qbd_split`: the costs of two adjacent cells add. `cellQ_sound`: a cost that `cellQ` returns below its limit
  bounds the cell.
* `sq_small`: the `n ≡ a` of `(N₁, N₂]` that the square of a prime at least `⌈x^{y/DEN}⌉` divides weigh
  `o(x/(φ(q) log x))`.
* `bd_rev`: **the cost of a reversal bounds the term.** For tests that are sound under two more atoms: a cost `C`
  that `revCost` returns below its limit on a box that passes `revOK` gives `SieveAd.Bd false (C/K)` for the box:
  its term in `𝒜` minus the comparison set is at most `(C/K + o(1))x/(φ(q) log x)`.

The file imports `SieveAdRevInj.lean`.
-/
import SieveAdRevInj

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K DEN_pos' K_pos')

variable [Route]

/-! ### The cells of the smaller prime of a cofactor of two primes -/

omit [Route] in
theorem le_maxN_right (a b : ℕ) : b ≤ maxN a b := by
  unfold maxN
  cases h : Nat.ble a b
  · simp only [Bool.cond_false]
    have : ¬ a ≤ b := by rw [← Nat.ble_eq, h]; simp
    omega
  · simp

/-- **The larger prime of a cofactor of two primes lies in its cell.** For primes `p₂`, `p₃` in the cells `c2`,
`c3`, `q₂` in a cell `d`, `Q > q₂`, and the product `p₂·Q·q₂·p₃` in `(x^{ea/DEN}, x^{eb/DEN}]` inside the range of
the condition: `Q` lies in the cell `iq2 d`. -/
theorem Q_in_iq2 [RouteOK] {q : ℕ} (hq : Big q) {c1 c2 c3 : Cell} (hsumh : c1.2 + c2.2 + c3.2 ≤ DEN)
    (hsuml : c1.1 + c2.1 + c3.1 ≤ DEN + 1) (hc1 : c1.1 ≤ DEN) {ea eb : ℕ} (hea : e1 c1 ≤ ea) (heb : eb ≤ e2 c1)
    (d : Cell) {p₂ Q q₂ p₃ : ℕ} (hQ1 : 1 ≤ Q) (hp2 : Xe q c2.1 ≤ p₂ ∧ (p₂ : ℝ) < Xe q c2.2)
    (hp3 : Xe q c3.1 ≤ p₃ ∧ (p₃ : ℝ) < Xe q c3.2) (hq2 : Xe q d.1 ≤ q₂ ∧ (q₂ : ℝ) < Xe q d.2) (hqQ : q₂ < Q)
    (hs : Xe q ea < (p₂ : ℝ) * Q * q₂ * p₃ ∧ (p₂ : ℝ) * Q * q₂ * p₃ ≤ Xe q eb) :
    Xe q (iq2 c1 c2 c3 d).1 ≤ Q ∧ (Q : ℝ) < Xe q (iq2 c1 c2 c3 d).2 := by
  obtain ⟨hx3, hX1, -⟩ := big_n hq
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 ≤ xq q := by linarith
  have hp2pos : (0 : ℝ) < p₂ := lt_of_lt_of_le (Xe_pos hx0 _) hp2.1
  have hp3pos : (0 : ℝ) < p₃ := lt_of_lt_of_le (Xe_pos hx0 _) hp3.1
  have hq2pos : (0 : ℝ) < q₂ := lt_of_lt_of_le (Xe_pos hx0 _) hq2.1
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ1
  have hpos : ∀ a b c : ℕ, 0 < Xe q a * Xe q b * Xe q c := fun a b c =>
    mul_pos (mul_pos (Xe_pos hx0 _) (Xe_pos hx0 _)) (Xe_pos hx0 _)
  constructor
  · refine Xe_maxN_le ?_ (hq2.1.trans (by exact_mod_cast hqQ.le))
    by_cases ht : d.2 ≤ mlo c1 c2 c3
    · have e : Xe q (mlo c1 c2 c3 - d.2) * (Xe q c2.2 * Xe q d.2 * Xe q c3.2) = Xe q (e1 c1) := by
        rw [← Xe_add hx0, ← Xe_add hx0, ← Xe_add hx0]
        congr 1
        unfold mlo e1 at *
        omega
      have h0 : (p₂ : ℝ) * q₂ * p₃ ≤ Xe q c2.2 * Xe q d.2 * Xe q c3.2 :=
        mul_le_mul (mul_le_mul hp2.2.le hq2.2.le hq2pos.le (Xe_pos hx0 _).le) hp3.2.le hp3pos.le
          (mul_nonneg (Xe_pos hx0 _).le (Xe_pos hx0 _).le)
      have h1 : (p₂ : ℝ) * Q * q₂ * p₃ ≤ Q * (Xe q c2.2 * Xe q d.2 * Xe q c3.2) := by
        calc (p₂ : ℝ) * Q * q₂ * p₃ = Q * (p₂ * q₂ * p₃) := by ring
          _ ≤ Q * (Xe q c2.2 * Xe q d.2 * Xe q c3.2) := mul_le_mul_of_nonneg_left h0 hQpos.le
      have h2 : Xe q (mlo c1 c2 c3 - d.2) * (Xe q c2.2 * Xe q d.2 * Xe q c3.2) <
          Q * (Xe q c2.2 * Xe q d.2 * Xe q c3.2) := by
        rw [e]
        have := Xe_mono hx1 hea
        linarith [hs.1]
      exact (lt_of_mul_lt_mul_right h2 (hpos _ _ _).le).le
    · rw [show mlo c1 c2 c3 - d.2 = 0 by omega, Xe_zero]
      exact_mod_cast hQ1
  · have h0 : Xe q c2.1 * Xe q d.1 * Xe q c3.1 ≤ (p₂ : ℝ) * q₂ * p₃ :=
      mul_le_mul (mul_le_mul hp2.1 hq2.1 (Xe_pos hx0 _).le hp2pos.le) hp3.1 (Xe_pos hx0 _).le
        (mul_nonneg hp2pos.le hq2pos.le)
    have h1 : (Q : ℝ) * (Xe q c2.1 * Xe q d.1 * Xe q c3.1) ≤ (p₂ : ℝ) * Q * q₂ * p₃ := by
      calc (Q : ℝ) * (Xe q c2.1 * Xe q d.1 * Xe q c3.1) ≤ Q * (p₂ * q₂ * p₃) :=
            mul_le_mul_of_nonneg_left h0 hQpos.le
        _ = (p₂ : ℝ) * Q * q₂ * p₃ := by ring
    have h2 : (Q : ℝ) * (Xe q c2.1 * Xe q d.1 * Xe q c3.1) ≤ Xe q (e2 c1) :=
      h1.trans (hs.2.trans (Xe_mono hx1 heb))
    by_cases ht : d.1 ≤ mhi c1 c2 c3
    · have e : Xe q (mhi c1 c2 c3 - d.1) * (Xe q c2.1 * Xe q d.1 * Xe q c3.1) = Xe q (e2 c1) := by
        rw [← Xe_add hx0, ← Xe_add hx0, ← Xe_add hx0]
        congr 1
        unfold mhi e2 at *
        omega
      have h3 : (Q : ℝ) ≤ Xe q (mhi c1 c2 c3 - d.1) :=
        le_of_mul_le_mul_right (by rw [e]; exact h2) (hpos _ _ _)
      have h4 : Xe q (mhi c1 c2 c3 - d.1) < Xe q (mhi c1 c2 c3 - d.1 + 1) := by
        rw [Xe_add hx0]
        have := Xe_pos hx0 (mhi c1 c2 c3 - d.1)
        nlinarith
      exact lt_of_le_of_lt h3 h4
    · exfalso
      have e : Xe q (e2 c1) ≤ 1 * (Xe q c2.1 * Xe q d.1 * Xe q c3.1) := by
        rw [one_mul, ← Xe_add hx0, ← Xe_add hx0]
        exact Xe_mono hx1 (by unfold mhi e2 at *; omega)
      have h3 : (Q : ℝ) ≤ 1 := le_of_mul_le_mul_right (h2.trans e) (hpos _ _ _)
      have h4 : (1 : ℝ) < Q := lt_of_le_of_lt ((one_le_Xe hx1 _).trans hq2.1) (by exact_mod_cast hqQ)
      linarith

/-- **The cells of the smaller prime add up.** For atoms' boxes `bx d` of four primes with the cell `c2` at `jp`,
`c3` at the last index, the cell `d` of the smaller prime of the cofactor at `jq` and `iq2 d` for the larger at
`jQ < jq`: a sum over the tuples of `bx (a, t)` under a condition inside the range is the sum over those of
`bx (a, m)` plus the sum over those of `bx (m, t)`, for `a ≤ m ≤ t`. -/
theorem famK_cutQ [RouteOK] {q : ℕ} (hq : Big q) {c1 c2 c3 : Cell} (hsumh : c1.2 + c2.2 + c3.2 ≤ DEN)
    (hsuml : c1.1 + c2.1 + c3.1 ≤ DEN + 1) (hc1 : c1.1 ≤ DEN) (bx : Cell → Fin 4 → Cell) (jp jQ jq : Fin 4)
    (hcov : ∀ i : Fin 4, i = jp ∨ i = jQ ∨ i = jq ∨ i = 3) (hQq : jQ < jq)
    (hprod : ∀ f : Fin 4 → ℝ, ∏ i, f i = f jp * f jQ * f jq * f 3) (hbp : ∀ d, bx d jp = c2)
    (hb3 : ∀ d, bx d 3 = c3) (hbq : ∀ d, bx d jq = d) (hbQ : ∀ d, bx d jQ = iq2 c1 c2 c3 d) {ea eb : ℕ}
    (hea : e1 c1 ≤ ea) (heb : eb ≤ e2 c1) {a m t : ℕ} (ham : a ≤ m) (hmt : m ≤ t) (G : (Fin 4 → ℕ) → ℝ) :
    ∑ u ∈ famK q ea eb 4 (bx (a, t)), G u =
      ∑ u ∈ famK q ea eb 4 (bx (a, m)), G u + ∑ u ∈ famK q ea eb 4 (bx (m, t)), G u := by
  obtain ⟨hx3, hX1, -⟩ := big_n hq
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 ≤ xq q := by linarith
  have hmem : ∀ (d : Cell) (u : Fin 4 → ℕ), u ∈ famK q ea eb 4 (bx d) ↔
      ((∀ i, u i ≤ N2 q ∧ (u i).Prime) ∧ StrictAnti u ∧ (Xe q c2.1 ≤ u jp ∧ (u jp : ℝ) < Xe q c2.2) ∧
        (Xe q c3.1 ≤ u 3 ∧ (u 3 : ℝ) < Xe q c3.2) ∧ slabP q ea eb 4 u) ∧
          (Xe q d.1 ≤ u jq ∧ (u jq : ℝ) < Xe q d.2) := by
    intro d u
    rw [famK, Finset.mem_filter, mem_famB]
    constructor
    · rintro ⟨⟨hp, hsa, hc⟩, hsl⟩
      have h1 := hc jp
      rw [hbp] at h1
      have h2 := hc 3
      rw [hb3] at h2
      have h3 := hc jq
      rw [hbq] at h3
      exact ⟨⟨hp, hsa, h1, h2, hsl⟩, h3⟩
    · rintro ⟨⟨hp, hsa, h1, h2, hsl⟩, h3⟩
      refine ⟨⟨hp, hsa, fun i => ?_⟩, hsl⟩
      rcases hcov i with rfl | rfl | rfl | rfl
      · rw [hbp]; exact h1
      · rw [hbQ]
        have hs := hsl
        unfold slabP at hs
        rw [aprodR_full (le_refl _), hprod] at hs
        exact Q_in_iq2 hq hsumh hsuml hc1 hea heb d (hp _).2.one_lt.le h1 h2 h3 (hsa hQq) hs
      · rw [hbq]; exact h3
      · rw [hb3]; exact h2
  have hA : famK q ea eb 4 (bx (a, m)) =
      (famK q ea eb 4 (bx (a, t))).filter fun u => (u jq : ℝ) < Xe q m := by
    ext u
    rw [Finset.mem_filter, hmem, hmem]
    constructor
    · rintro ⟨h, hlo, hhi⟩
      exact ⟨⟨h, hlo, hhi.trans_le (Xe_mono hx1 hmt)⟩, hhi⟩
    · rintro ⟨⟨h, hlo, -⟩, hhi⟩
      exact ⟨h, hlo, hhi⟩
  have hB : famK q ea eb 4 (bx (m, t)) =
      (famK q ea eb 4 (bx (a, t))).filter fun u => ¬ (u jq : ℝ) < Xe q m := by
    ext u
    rw [Finset.mem_filter, hmem, hmem, not_lt]
    constructor
    · rintro ⟨h, hlo, hhi⟩
      exact ⟨⟨h, (Xe_mono hx1 ham).trans hlo, hhi⟩, hlo⟩
    · rintro ⟨⟨h, -, hhi⟩, hlo⟩
      exact ⟨h, hlo, hhi⟩
  rw [hA, hB, Finset.sum_filter_add_sum_filter_not]

/-- **The three atoms' boxes with a cofactor of two primes, the smaller in the cell `d`, are bounded at the cost
`C`**: their terms under the condition, at the level `⌈x^{l₃/DEN}⌉`, in `𝒜`, minus the numbers `K·r'` of the
comparison set with `K` prime, sum to at most `(C/K + o(1))x/(φ(q) log x)`. -/
def QBd (c1 c2 c3 d : Cell) (C : ℕ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
    (famJ (gA q a) (N1 q) (N2 q) ⌈Xe q c3.1⌉₊
        (famK q (e1 c1) (e2 c1) 4 (boxFn [c3, d, iq2 c1 c2 c3 d, c2] 4 rfl)) -
      famPr (gB q) (N1 q) (N2 q) (famK q (e1 c1 + 1) (e2 c1 - 1) 4 (boxFn [c3, d, iq2 c1 c2 c3 d, c2] 4 rfl))) +
    (famJ (gA q a) (N1 q) (N2 q) ⌈Xe q c3.1⌉₊
        (famK q (e1 c1) (e2 c1) 4 (boxFn [c3, d, c2, iq2 c1 c2 c3 d] 4 rfl)) -
      famPr (gB q) (N1 q) (N2 q) (famK q (e1 c1 + 1) (e2 c1 - 1) 4 (boxFn [c3, d, c2, iq2 c1 c2 c3 d] 4 rfl))) +
    (famJ (gA q a) (N1 q) (N2 q) ⌈Xe q c3.1⌉₊
        (famK q (e1 c1) (e2 c1) 4 (boxFn [c3, c2, d, iq2 c1 c2 c3 d] 4 rfl)) -
      famPr (gB q) (N1 q) (N2 q) (famK q (e1 c1 + 1) (e2 c1 - 1) 4 (boxFn [c3, c2, d, iq2 c1 c2 c3 d] 4 rfl))) ≤
      (q.totient : ℝ)⁻¹ * (((C : ℝ) / K + η) * Xq q)

/-- The costs of two adjacent cells of the smaller prime add. -/
theorem qbd_split [RouteOK] {c1 c2 c3 : Cell} (hsumh : c1.2 + c2.2 + c3.2 ≤ DEN)
    (hsuml : c1.1 + c2.1 + c3.1 ≤ DEN + 1) (hc1 : c1.1 ≤ DEN) {a m t : ℕ} (ham : a ≤ m) (hmt : m ≤ t) {C1 C2 : ℕ}
    (h1 : QBd c1 c2 c3 (a, m) C1) (h2 : QBd c1 c2 c3 (m, t) C2) : QBd c1 c2 c3 (a, t) (C1 + C2) := by
  intro η hη
  filter_upwards [h1 (η / 2) (by positivity), h2 (η / 2) (by positivity), big_ev] with q hq1 hq2 hbig r hr
  have cut : ∀ (bx : Cell → Fin 4 → Cell) (jp jQ jq : Fin 4), (∀ i : Fin 4, i = jp ∨ i = jQ ∨ i = jq ∨ i = 3) →
      jQ < jq → (∀ f : Fin 4 → ℝ, ∏ i, f i = f jp * f jQ * f jq * f 3) → (∀ d, bx d jp = c2) →
      (∀ d, bx d 3 = c3) → (∀ d, bx d jq = d) → (∀ d, bx d jQ = iq2 c1 c2 c3 d) →
      (famJ (gA q r) (N1 q) (N2 q) ⌈Xe q c3.1⌉₊ (famK q (e1 c1) (e2 c1) 4 (bx (a, t))) =
        famJ (gA q r) (N1 q) (N2 q) ⌈Xe q c3.1⌉₊ (famK q (e1 c1) (e2 c1) 4 (bx (a, m))) +
          famJ (gA q r) (N1 q) (N2 q) ⌈Xe q c3.1⌉₊ (famK q (e1 c1) (e2 c1) 4 (bx (m, t)))) ∧
      (famPr (gB q) (N1 q) (N2 q) (famK q (e1 c1 + 1) (e2 c1 - 1) 4 (bx (a, t))) =
        famPr (gB q) (N1 q) (N2 q) (famK q (e1 c1 + 1) (e2 c1 - 1) 4 (bx (a, m))) +
          famPr (gB q) (N1 q) (N2 q) (famK q (e1 c1 + 1) (e2 c1 - 1) 4 (bx (m, t)))) := by
    intro bx jp jQ jq hcov hQq hprod hbp hb3 hbq hbQ
    constructor
    · unfold famJ
      exact famK_cutQ hbig hsumh hsuml hc1 bx jp jQ jq hcov hQq hprod hbp hb3 hbq hbQ le_rfl le_rfl ham hmt _
    · unfold famPr
      exact famK_cutQ hbig hsumh hsuml hc1 bx jp jQ jq hcov hQq hprod hbp hb3 hbq hbQ (Nat.le_succ _)
        (Nat.sub_le _ _) ham hmt _
  obtain ⟨j1, p1⟩ := cut (fun d => boxFn [c3, d, iq2 c1 c2 c3 d, c2] 4 rfl) 0 1 2 (by decide) (by decide)
    (fun f => by rw [Fin.prod_univ_four]) (fun d => rfl) (fun d => rfl) (fun d => rfl) (fun d => rfl)
  obtain ⟨j2, p2⟩ := cut (fun d => boxFn [c3, d, c2, iq2 c1 c2 c3 d] 4 rfl) 1 0 2 (by decide) (by decide)
    (fun f => by rw [Fin.prod_univ_four]; ring) (fun d => rfl) (fun d => rfl) (fun d => rfl) (fun d => rfl)
  obtain ⟨j3, p3⟩ := cut (fun d => boxFn [c3, c2, d, iq2 c1 c2 c3 d] 4 rfl) 2 0 1 (by decide) (by decide)
    (fun f => by rw [Fin.prod_univ_four]; ring) (fun d => rfl) (fun d => rfl) (fun d => rfl) (fun d => rfl)
  have hA := hq1 r hr
  have hB := hq2 r hr
  rw [j1, p1, j2, p2, j3, p3]
  have e : (q.totient : ℝ)⁻¹ * ((((C1 + C2 : ℕ) : ℝ) / K + η) * Xq q) =
      (q.totient : ℝ)⁻¹ * (((C1 : ℝ) / K + η / 2) * Xq q) + (q.totient : ℝ)⁻¹ * (((C2 : ℝ) / K + η / 2) * Xq q) := by
    push_cast
    ring
  rw [e]
  refine le_trans (le_of_eq ?_) (add_le_add hA hB)
  ring

/-- **A cost that `cellQ` returns below its limit bounds the cell**, for tests that are sound under two more
atoms, a box that passes `revOK` and a cell `d` of the smaller prime that starts at `l₃` or above. -/
theorem cellQ_sound [RouteOK] {τ : Tests} (hτ : τ.SoundX) (SK : Cell → ℕ → Strat) (fuel : ℕ) {c1 c2 c3 : Cell}
    (hrev : revOK [c3, c2, c1] = true) {d : Cell} (hd : c3.1 ≤ d.1) {par : Bool} {lim : ℕ}
    (h : cellQ τ SK fuel c1 c2 c3 (mlo c1 c2 c3) (mhi c1 c2 c3) [d] par lim < lim) :
    QBd c1 c2 c3 d (cellQ τ SK fuel c1 c2 c3 (mlo c1 c2 c3) (mhi c1 c2 c3) [d] par lim) := by
  simp only [revOK, Bool.and_eq_true, Nat.ble_eq] at hrev
  obtain ⟨⟨⟨⟨hcells, hb⟩, hsum⟩, hcube⟩, h31⟩ := hrev
  have hcl := (cellsOK_iff _).1 hcells
  have hk3 := hcl c3 (by simp)
  have hk2 := hcl c2 (by simp)
  have hk1 := hcl c1 (by simp)
  have hctx : 0 < c1.1 ∧ c1.1 < c1.2 ∧ c1.2 ≤ DEN := ⟨hk1.1, hk1.2, by omega⟩
  have hd0 : 0 < d.1 := lt_of_lt_of_le hk3.1 hd
  have hiq0 : 0 < (iq2 c1 c2 c3 d).1 := lt_of_lt_of_le hd0 (le_maxN_right _ _)
  have hyh : c1.2 + c3.1 + 1 ≤ DEN := by omega
  have hunf : cellQ τ SK fuel c1 c2 c3 (mlo c1 c2 c3) (mhi c1 c2 c3) [d] par lim =
      addL (famCost τ SK fuel c1 [c3, d, iq2 c1 c2 c3 d, c2] 2 lim)
        (fun l1 => addL (famCost τ SK fuel c1 [c3, d, c2, iq2 c1 c2 c3 d] 3 l1)
          (fun l2 => famCost τ SK fuel c1 [c3, c2, d, iq2 c1 c2 c3 d] 3 l2) l1) lim := rfl
  rw [hunf] at h ⊢
  obtain ⟨hA, hrest, heq⟩ := addL_lt h
  obtain ⟨hB, hC, heq2⟩ := addL_lt hrest
  rw [heq, heq2]
  have F1 := famCost_sound hτ SK fuel hctx [c3, d, iq2 c1 c2 c3 d, c2] (by
    intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact hk3.1
    · exact hd0
    · exact hiq0
    · exact hk2.1) (by simp) 2 (by simp) h31 hyh hA
  have F2 := famCost_sound hτ SK fuel hctx [c3, d, c2, iq2 c1 c2 c3 d] (by
    intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact hk3.1
    · exact hd0
    · exact hk2.1
    · exact hiq0) (by simp) 3 (by simp) h31 hyh hB
  have F3 := famCost_sound hτ SK fuel hctx [c3, c2, d, iq2 c1 c2 c3 d] (by
    intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact hk3.1
    · exact hk2.1
    · exact hd0
    · exact hiq0) (by simp) 3 (by simp) h31 hyh hC
  intro η hη
  filter_upwards [F1 (η / 3) (by positivity), F2 (η / 3) (by positivity), F3 (η / 3) (by positivity)]
    with q h1 h2 h3 a ha
  have h1' : famJ (gA q a) (N1 q) (N2 q) ⌈Xe q c3.1⌉₊
        (famK q (e1 c1) (e2 c1) 4 (boxFn [c3, d, iq2 c1 c2 c3 d, c2] 4 rfl)) -
      famPr (gB q) (N1 q) (N2 q) (famK q (e1 c1 + 1) (e2 c1 - 1) 4 (boxFn [c3, d, iq2 c1 c2 c3 d, c2] 4 rfl)) ≤
      (q.totient : ℝ)⁻¹ * (((famCost τ SK fuel c1 [c3, d, iq2 c1 c2 c3 d, c2] 2 lim : ℝ) / K + η / 3) * Xq q) :=
    h1 a ha
  have h2' : famJ (gA q a) (N1 q) (N2 q) ⌈Xe q c3.1⌉₊
        (famK q (e1 c1) (e2 c1) 4 (boxFn [c3, d, c2, iq2 c1 c2 c3 d] 4 rfl)) -
      famPr (gB q) (N1 q) (N2 q) (famK q (e1 c1 + 1) (e2 c1 - 1) 4 (boxFn [c3, d, c2, iq2 c1 c2 c3 d] 4 rfl)) ≤
      (q.totient : ℝ)⁻¹ * (((famCost τ SK fuel c1 [c3, d, c2, iq2 c1 c2 c3 d] 3
        (lim - famCost τ SK fuel c1 [c3, d, iq2 c1 c2 c3 d, c2] 2 lim) : ℝ) / K + η / 3) * Xq q) := h2 a ha
  have h3' : famJ (gA q a) (N1 q) (N2 q) ⌈Xe q c3.1⌉₊
        (famK q (e1 c1) (e2 c1) 4 (boxFn [c3, c2, d, iq2 c1 c2 c3 d] 4 rfl)) -
      famPr (gB q) (N1 q) (N2 q) (famK q (e1 c1 + 1) (e2 c1 - 1) 4 (boxFn [c3, c2, d, iq2 c1 c2 c3 d] 4 rfl)) ≤
      (q.totient : ℝ)⁻¹ * (((famCost τ SK fuel c1 [c3, c2, d, iq2 c1 c2 c3 d] 3
        (lim - famCost τ SK fuel c1 [c3, d, iq2 c1 c2 c3 d, c2] 2 lim -
          famCost τ SK fuel c1 [c3, d, c2, iq2 c1 c2 c3 d] 3
            (lim - famCost τ SK fuel c1 [c3, d, iq2 c1 c2 c3 d, c2] 2 lim)) : ℝ) / K + η / 3) * Xq q) := h3 a ha
  refine le_trans (add_le_add (add_le_add h1' h2') h3') (le_of_eq ?_)
  push_cast
  ring

/-! ### The numbers with a square factor -/

/-- **The numbers with a square factor weigh little.** For `y > 0` and `η > 0`, at a large modulus and for a unit
`a`: `(DEN + 1)³` times the number of the `n ≡ a` of `(N₁, N₂]` that the square of a prime at least `⌈x^{y/DEN}⌉`
divides is at most `η·x/(φ(q) log x)`. -/
theorem sq_small [RouteOK] {y : ℕ} (hy : 0 < y) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
      ((DEN + 1 : ℕ) : ℝ) ^ 3 * ∑ n ∈ (Ioc (N1 q) (N2 q)).filter
          (fun n => ∃ s : ℕ, s.Prime ∧ ⌈Xe q y⌉₊ ≤ s ∧ s ^ 2 ∣ n), gA q a n ≤
        (q.totient : ℝ)⁻¹ * (η * Xq q) := by
  have hL0 : 0 < L := L_pos
  have hL2 : 2 < L := two_lt_L
  have hD := DEN_pos'
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ((DEN + 1 : ℕ) : ℝ) ^ 3 := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM]; positivity
  filter_upwards [big_ev, le_Xq (δ := L / DEN) (by positivity) (show 0 < η / (6 * M) by positivity),
    le_Xq (δ := L / 2 - 1) (by linarith) (show 0 < η / (4 * M) by positivity)] with q hbig hX1 hX2 a ha
  obtain ⟨hq2, hx3, -, -, -⟩ := big_facts hbig
  obtain ⟨-, hXe1, -⟩ := big_n hbig
  have hq0 : 0 < q := by omega
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq0
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 ≤ xq q := by linarith
  have hX := Xq_pos hbig
  obtain ⟨z, hz⟩ : ∃ z, z = ⌈Xe q y⌉₊ := ⟨_, rfl⟩
  rw [← hz, ← hM]
  have hzge : Xe q 1 ≤ z := by rw [hz]; exact (Xe_mono hx1 hy).trans (Nat.le_ceil _)
  have hz3 : (3 : ℝ) ≤ z := hXe1.trans hzge
  have hz2 : 2 ≤ z := by
    have : (2 : ℝ) ≤ z := by linarith
    exact_mod_cast this
  have hsum : ∑ n ∈ (Ioc (N1 q) (N2 q)).filter (fun n => ∃ s : ℕ, s.Prime ∧ z ≤ s ∧ s ^ 2 ∣ n), gA q a n =
      (((Ioc (N1 q) (N2 q)).filter
        fun n : ℕ => (n : ZMod q) = a ∧ ∃ s : ℕ, s.Prime ∧ z ≤ s ∧ s ^ 2 ∣ n).card : ℝ) := by
    rw [Finset.card_filter, Finset.sum_filter]
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold gA
    by_cases h1 : (n : ZMod q) = a <;> by_cases h2 : ∃ s : ℕ, s.Prime ∧ z ≤ s ∧ s ^ 2 ∣ n <;> simp [h1, h2]
  rw [hsum]
  have hN12 : N1 q ≤ N2 q := Nat.floor_le_floor (by linarith)
  have hcard := card_sq_le hq0 ha hN12 hz2
  refine (mul_le_mul_of_nonneg_left hcard hM0.le).trans ?_
  have hφ : (q : ℝ)⁻¹ ≤ (q.totient : ℝ)⁻¹ := by
    have h1 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq0
    have h2 : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
    exact inv_anti₀ h1 h2
  have hηX : 0 ≤ η * Xq q := by positivity
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hφ hηX)
  rw [inv_mul_eq_div, le_div_iff₀ hq']
  have hNN : (N2 q : ℝ) - N1 q ≤ 2 * xq q := by
    have h1 : (N2 q : ℝ) ≤ 2 * xq q := Nat.floor_le (by positivity)
    have h2 : xq q - 1 < (N1 q : ℝ) := Nat.sub_one_lt_floor _
    linarith
  have hzm : (2 / 3 : ℝ) * Xe q 1 ≤ (z : ℝ) - 1 := by linarith
  have hzm0 : (0 : ℝ) < (z : ℝ) - 1 := by linarith
  have ht1 : ((N2 q : ℝ) - N1 q) / (q * ((z : ℝ) - 1)) * q ≤ 3 * (q : ℝ) ^ (L - L / DEN) := by
    have e : ((N2 q : ℝ) - N1 q) / (q * ((z : ℝ) - 1)) * q = ((N2 q : ℝ) - N1 q) / ((z : ℝ) - 1) := by
      field_simp
    rw [e, div_le_iff₀ hzm0]
    have hpow : (q : ℝ) ^ (L - L / DEN) * Xe q 1 = xq q := by
      unfold Xe
      rw [Nat.cast_one, xpow, ← Real.rpow_add hq']
      congr 1
      ring
    have hp0 : 0 ≤ (q : ℝ) ^ (L - L / DEN) := by positivity
    have h3 := mul_le_mul_of_nonneg_left hzm hp0
    nlinarith
  have ht2 : (Nat.sqrt (N2 q) : ℝ) * q ≤ 2 * (q : ℝ) ^ (L - (L / 2 - 1)) := by
    have hs : (Nat.sqrt (N2 q) : ℝ) ≤ 2 * (q : ℝ) ^ (L / 2) := by
      have h1 : ((Nat.sqrt (N2 q) : ℕ) : ℝ) ^ 2 ≤ (N2 q : ℝ) := by exact_mod_cast Nat.sqrt_le' (N2 q)
      have h2 : (N2 q : ℝ) ≤ 2 * xq q := Nat.floor_le (by positivity)
      have h3 : ((q : ℝ) ^ (L / 2)) ^ 2 = xq q := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hq'.le]
        congr 1
        push_cast
        ring
      have h4 : ((Nat.sqrt (N2 q) : ℕ) : ℝ) ^ 2 ≤ (2 * (q : ℝ) ^ (L / 2)) ^ 2 := by
        rw [mul_pow, h3]
        linarith
      exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) two_ne_zero).1 h4
    have e : (q : ℝ) ^ (L / 2) * q = (q : ℝ) ^ (L - (L / 2 - 1)) := by
      rw [← Real.rpow_add_one hq'.ne']
      congr 1
      ring
    calc (Nat.sqrt (N2 q) : ℝ) * q ≤ 2 * (q : ℝ) ^ (L / 2) * q := mul_le_mul_of_nonneg_right hs hq'.le
      _ = 2 * (q : ℝ) ^ (L - (L / 2 - 1)) := by rw [mul_assoc, e]
  calc M * (((N2 q : ℝ) - N1 q) / (q * ((z : ℝ) - 1)) + Nat.sqrt (N2 q)) * q
      = M * (((N2 q : ℝ) - N1 q) / (q * ((z : ℝ) - 1)) * q + Nat.sqrt (N2 q) * q) := by ring
    _ ≤ M * (3 * (q : ℝ) ^ (L - L / DEN) + 2 * (q : ℝ) ^ (L - (L / 2 - 1))) :=
        mul_le_mul_of_nonneg_left (add_le_add ht1 ht2) hM0.le
    _ ≤ M * (3 * (η / (6 * M) * Xq q) + 2 * (η / (4 * M) * Xq q)) :=
        mul_le_mul_of_nonneg_left (by linarith) hM0.le
    _ = η * Xq q := by
        field_simp
        ring

/-! ### The cost of a reversal bounds the term -/

/-- What the costs of the cells of the smaller prime prove: a list of one cell that starts at `l₃` or above is
bounded at the cost. -/
def PQ (c1 c2 c3 : Cell) (bl : List Cell) (_ : Bool) (c : ℕ) : Prop :=
  ∀ d : Cell, bl = [d] → c3.1 ≤ d.1 → QBd c1 c2 c3 d c

/-- **The cost of a reversal bounds the term.** For tests that are sound under two more atoms, and a box of three
primes that passes `revOK`: a cost `C` that `revCost` returns below its limit gives `Bd false (C/K)` for the box,
that is, its term in `𝒜` minus the comparison set is at most `(C/K + o(1))x/(φ(q) log x)`. -/
theorem bd_rev [RouteOK] {τ : Tests} (hτ : τ.SoundX) (SK : Cell → ℕ → Strat) (fuel : ℕ) (cq : ℕ → ℕ → List ℕ)
    {bl : List Cell} (hrev : revOK bl = true) {lim : ℕ} (h : revCost τ SK fuel cq bl lim < lim)
    (h3 : bl.length = 3) : Bd false ((revCost τ SK fuel cq bl lim : ℝ) / K) (boxFn bl 3 h3) := by
  obtain ⟨c3, c2, c1, rfl⟩ : ∃ c3 c2 c1, bl = [c3, c2, c1] := by
    cases bl with
    | nil => simp at h3
    | cons a t =>
      cases t with
      | nil => simp at h3
      | cons b t =>
        cases t with
        | nil => simp at h3
        | cons c t =>
          cases t with
          | nil => exact ⟨a, b, c, rfl⟩
          | cons d t => simp at h3
  have hrev' := hrev
  simp only [revOK, Bool.and_eq_true, Nat.ble_eq] at hrev'
  obtain ⟨⟨⟨⟨hcells, hb⟩, hsum⟩, hcube⟩, h31⟩ := hrev'
  have hcl := (cellsOK_iff _).1 hcells
  have hk3 := hcl c3 (by simp)
  have hk2 := hcl c2 (by simp)
  have hk1 := hcl c1 (by simp)
  have hctx : 0 < c1.1 ∧ c1.1 < c1.2 ∧ c1.2 ≤ DEN := ⟨hk1.1, hk1.2, by omega⟩
  have hyh : c1.2 + c3.1 + 1 ≤ DEN := by omega
  have hiq0 : 0 < (iq1 c1 c2 c3).1 := lt_of_lt_of_le hk3.1 (le_maxN_right _ _)
  have hunf : revCost τ SK fuel cq [c3, c2, c1] lim =
      addL (famCost τ SK fuel c1 [c3, c2, iq1 c1 c2 c3] 2 lim)
        (fun l1 => addL (famCost τ SK fuel c1 [c3, iq1 c1 c2 c3, c2] 1 l1)
          (fun l2 => kids (cellQ τ SK fuel c1 c2 c3 (mlo c1 c2 c3) (mhi c1 c2 c3)) (topQ c1 c2 c3) [] false
            (cq c3.1 (topQ c1 c2 c3)) c3.1 l2) l1) lim := rfl
  rw [hunf] at h ⊢
  obtain ⟨hA, hrest, heq⟩ := addL_lt h
  obtain ⟨hB, hC, heq2⟩ := addL_lt hrest
  rw [heq, heq2]
  obtain ⟨C1, hC1⟩ : ∃ C1 : ℕ, C1 = famCost τ SK fuel c1 [c3, c2, iq1 c1 c2 c3] 2 lim := ⟨_, rfl⟩
  rw [← hC1] at hA hB hC ⊢
  obtain ⟨C2, hC2⟩ : ∃ C2 : ℕ, C2 = famCost τ SK fuel c1 [c3, iq1 c1 c2 c3, c2] 1 (lim - C1) := ⟨_, rfl⟩
  rw [← hC2] at hB hC ⊢
  obtain ⟨C3, hC3⟩ : ∃ C3 : ℕ, C3 = kids (cellQ τ SK fuel c1 c2 c3 (mlo c1 c2 c3) (mhi c1 c2 c3))
      (topQ c1 c2 c3) [] false (cq c3.1 (topQ c1 c2 c3)) c3.1 (lim - C1 - C2) := ⟨_, rfl⟩
  rw [← hC3] at hC ⊢
  have F1 : FamBd c1 [c3, c2, iq1 c1 c2 c3] C1 := by
    rw [hC1]
    refine famCost_sound hτ SK fuel hctx [c3, c2, iq1 c1 c2 c3] ?_ (by simp) 2 (by simp) h31 hyh (by rw [← hC1]; exact hA)
    intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hk3.1
    · exact hk2.1
    · exact hiq0
  have F2 : FamBd c1 [c3, iq1 c1 c2 c3, c2] C2 := by
    rw [hC2]
    refine famCost_sound hτ SK fuel hctx [c3, iq1 c1 c2 c3, c2] ?_ (by simp) 1 (by simp) h31 hyh (by rw [← hC2]; exact hB)
    intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hk3.1
    · exact hiq0
    · exact hk2.1
  have FQ : QBd c1 c2 c3 (c3.1, topQ c1 c2 c3) C3 := by
    have hsplit : ∀ {a m top : ℕ} {bl : List Cell} {par : Bool} {x y : ℕ}, a < m → m < top →
        PQ c1 c2 c3 ((a, m) :: bl) par x → PQ c1 c2 c3 ((m, top) :: bl) par y →
          PQ c1 c2 c3 ((a, top) :: bl) par (x + y) := by
      intro a m top bl par x y ham hmt hl hr d hd hd1
      simp only [List.cons.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      exact qbd_split hsum (by omega) (by omega) ham.le hmt.le (hl (a, m) rfl hd1)
        (hr (m, top) rfl (hd1.trans ham.le))
    have hrec : RecP (PQ c1 c2 c3) (cellQ τ SK fuel c1 c2 c3 (mlo c1 c2 c3) (mhi c1 c2 c3)) := by
      intro bl par lim hlt d hd hd1
      subst hd
      exact cellQ_sound hτ SK fuel hrev hd1 hlt
    rw [hC3]
    exact kidsP_sound hsplit hrec (topQ c1 c2 c3) [] false _ c3.1 _ (by rw [← hC3]; exact hC)
      (c3.1, topQ c1 c2 c3) rfl le_rfl
  intro η hη
  filter_upwards [F1 (η / 4) (by positivity), F2 (η / 4) (by positivity), FQ (η / 4) (by positivity),
    sq_small hk3.1 (show 0 < η / 4 by positivity), big_ev] with q h1 h2 hq3 h4 hbig a ha
  have hX := Xq_pos hbig
  have hcov := rev_cover hbig hrev (gA q a) (gA_nonneg q a)
  have hinj := rev_inject hbig hrev (gB q) (SieveDrop.gB_nonneg q) (iq1 c1 c2 c3) (c3.1, topQ c1 c2 c3)
    (iq2 c1 c2 c3 (c3.1, topQ c1 c2 c3))
  obtain ⟨IA, hIA⟩ : ∃ IA : ℝ, IA = famI (gA q a) (N1 q) (N2 q) (famB q (boxFn [c3, c2, c1] 3 rfl)) := ⟨_, rfl⟩
  obtain ⟨IB, hIB⟩ : ∃ IB : ℝ, IB = famI (gB q) (N1 q) (N2 q) (famB q (boxFn [c3, c2, c1] 3 rfl)) := ⟨_, rfl⟩
  obtain ⟨J1, hJ1⟩ : ∃ J1 : ℝ, J1 = famJ (gA q a) (N1 q) (N2 q) ⌈Xe q c3.1⌉₊
      (famK q (e1 c1) (e2 c1) 3 (boxFn [c3, c2, iq1 c1 c2 c3] 3 rfl)) := ⟨_, rfl⟩
  obtain ⟨J2, hJ2⟩ : ∃ J2 : ℝ, J2 = famJ (gA q a) (N1 q) (N2 q) ⌈Xe q c3.1⌉₊
      (famK q (e1 c1) (e2 c1) 3 (boxFn [c3, iq1 c1 c2 c3, c2] 3 rfl)) := ⟨_, rfl⟩
  obtain ⟨J3, hJ3⟩ : ∃ J3 : ℝ, J3 = famJ (gA q a) (N1 q) (N2 q) ⌈Xe q c3.1⌉₊ (famK q (e1 c1) (e2 c1) 4
      (boxFn [c3, (c3.1, topQ c1 c2 c3), iq2 c1 c2 c3 (c3.1, topQ c1 c2 c3), c2] 4 rfl)) := ⟨_, rfl⟩
  obtain ⟨J4, hJ4⟩ : ∃ J4 : ℝ, J4 = famJ (gA q a) (N1 q) (N2 q) ⌈Xe q c3.1⌉₊ (famK q (e1 c1) (e2 c1) 4
      (boxFn [c3, (c3.1, topQ c1 c2 c3), c2, iq2 c1 c2 c3 (c3.1, topQ c1 c2 c3)] 4 rfl)) := ⟨_, rfl⟩
  obtain ⟨J5, hJ5⟩ : ∃ J5 : ℝ, J5 = famJ (gA q a) (N1 q) (N2 q) ⌈Xe q c3.1⌉₊ (famK q (e1 c1) (e2 c1) 4
      (boxFn [c3, c2, (c3.1, topQ c1 c2 c3), iq2 c1 c2 c3 (c3.1, topQ c1 c2 c3)] 4 rfl)) := ⟨_, rfl⟩
  obtain ⟨P1, hP1⟩ : ∃ P1 : ℝ, P1 = famPr (gB q) (N1 q) (N2 q)
      (famK q (e1 c1 + 1) (e2 c1 - 1) 3 (boxFn [c3, c2, iq1 c1 c2 c3] 3 rfl)) := ⟨_, rfl⟩
  obtain ⟨P2, hP2⟩ : ∃ P2 : ℝ, P2 = famPr (gB q) (N1 q) (N2 q)
      (famK q (e1 c1 + 1) (e2 c1 - 1) 3 (boxFn [c3, iq1 c1 c2 c3, c2] 3 rfl)) := ⟨_, rfl⟩
  obtain ⟨P3, hP3⟩ : ∃ P3 : ℝ, P3 = famPr (gB q) (N1 q) (N2 q) (famK q (e1 c1 + 1) (e2 c1 - 1) 4
      (boxFn [c3, (c3.1, topQ c1 c2 c3), iq2 c1 c2 c3 (c3.1, topQ c1 c2 c3), c2] 4 rfl)) := ⟨_, rfl⟩
  obtain ⟨P4, hP4⟩ : ∃ P4 : ℝ, P4 = famPr (gB q) (N1 q) (N2 q) (famK q (e1 c1 + 1) (e2 c1 - 1) 4
      (boxFn [c3, (c3.1, topQ c1 c2 c3), c2, iq2 c1 c2 c3 (c3.1, topQ c1 c2 c3)] 4 rfl)) := ⟨_, rfl⟩
  obtain ⟨P5, hP5⟩ : ∃ P5 : ℝ, P5 = famPr (gB q) (N1 q) (N2 q) (famK q (e1 c1 + 1) (e2 c1 - 1) 4
      (boxFn [c3, c2, (c3.1, topQ c1 c2 c3), iq2 c1 c2 c3 (c3.1, topQ c1 c2 c3)] 4 rfl)) := ⟨_, rfl⟩
  obtain ⟨Sq, hSq⟩ : ∃ Sq : ℝ, Sq = ((DEN + 1 : ℕ) : ℝ) ^ 3 * ∑ n ∈ (Ioc (N1 q) (N2 q)).filter
      (fun n => ∃ s : ℕ, s.Prime ∧ ⌈Xe q c3.1⌉₊ ≤ s ∧ s ^ 2 ∣ n), gA q a n := ⟨_, rfl⟩
  rw [← hIA, ← hJ1, ← hJ2, ← hJ3, ← hJ4, ← hJ5, ← hSq] at hcov
  rw [← hIB, ← hP1, ← hP2, ← hP3, ← hP4, ← hP5] at hinj
  have h1' : J1 - P1 ≤ (q.totient : ℝ)⁻¹ * (((C1 : ℝ) / K + η / 4) * Xq q) := by
    rw [hJ1, hP1]
    exact h1 a ha
  have h2' : J2 - P2 ≤ (q.totient : ℝ)⁻¹ * (((C2 : ℝ) / K + η / 4) * Xq q) := by
    rw [hJ2, hP2]
    exact h2 a ha
  have h3' : (J3 - P3) + (J4 - P4) + (J5 - P5) ≤ (q.totient : ℝ)⁻¹ * (((C3 : ℝ) / K + η / 4) * Xq q) := by
    rw [hJ3, hP3, hJ4, hP4, hJ5, hP5]
    exact hq3 a ha
  have h4' : Sq ≤ (q.totient : ℝ)⁻¹ * (η / 4 * Xq q) := by
    rw [hSq]
    exact h4 a ha
  have hdI : dI q a (boxFn [c3, c2, c1] 3 h3) = IA - IB := by
    rw [hIA, hIB]
    rfl
  rw [hdI]
  simp only [sg, Bool.false_eq_true, ite_false, neg_mul, one_mul, neg_le_neg_iff]
  have e : (q.totient : ℝ)⁻¹ * ((((C1 + (C2 + C3) : ℕ) : ℝ) / K + η) * Xq q) =
      (q.totient : ℝ)⁻¹ * (((C1 : ℝ) / K + η / 4) * Xq q) + (q.totient : ℝ)⁻¹ * (((C2 : ℝ) / K + η / 4) * Xq q) +
        (q.totient : ℝ)⁻¹ * (((C3 : ℝ) / K + η / 4) * Xq q) + (q.totient : ℝ)⁻¹ * (η / 4 * Xq q) := by
    push_cast
    ring
  rw [e]
  linarith

end SieveAd

#print axioms SieveAd.bd_rev
