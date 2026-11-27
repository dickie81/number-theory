import GainLoss

/-!
# The losses

A step of the proof of the sharp frontier (`SharpInputs`, the piece `gain`; module M-G7c of the gain's numbers, second
half): `losses_le`, the frontier's asks less the gains net of the depths, at most `c_G/4`, which the assembly of the
gain's numbers reads; from the bounds at one prime of `GainLoss`.

**The statement** (`losses_le`, the spec's): at an admissible design with parameters (`Adm`, `FamAt`), under the
2-adic structure `S.TwoAdic κ e`, the clause G1 (`FewBadTops`) and the growth package `GainBig ε x`,
`Σ_t Σ_j (Σ_{p ∈ askSupp} 2 log p·askE + log d·askAtD) − Σ_{p ∈ inertPrimes(X″)} 2 log p·(Σ_j G_j(p) − τ_p) ≤
c_G/4`, in the gain's (twisted) coordinates, for every `κ`.

**The sums.** The slacks (`sum_slack_le`): the polynomial parts give `2(X″ + 1)·x^{900}·X′^{G′}` (at most `X″ + 1`
primes, `card_inertPrimes_le`), and the parts of size `a` of the candidates (all below `X′`,
`lt_scX'_of_mem_cand`) are summed with `Σ log p ≤ X′ log X′`, `Σ_{p ≥ p₀} log p/p² ≤ 2 log X′/p₀`,
`Σ log p/p ≤ log X′(1 + log X′)` and `Σ_{p < p₀} log p ≤ p₀ log p₀` (`GainSums`). The asks beyond `X″`
(`sum_beyond_le`): at most `w″/x` per top, lift and prime `p ≤ 2X″`. The ask at `d` (`sum_atD_le`).

**The fourteen classes**, each at most `|A|·a/64`, against `c_G = x^{2ε}·|A|·a ≥ |A|·a`, with `y = x^{1/8} ≥ 10⁹`
(the ratio to `|A|·a` in brackets):
* the polynomial terms (`2c₀·|gainExps|`, the orbits' slacks, `e_p`, `D_p`, `c_dep`, `Q_p = p^{G′}`, `c₀`, `η`,
  `N_m`): `2(X″ + 1)·x^{900}·X′^{G′}`, against `a ≥ x^{1001}·X′^{G′+2}` (`class_poly`);
* at `p ≥ p₀`: `b′/x` [`4y⁵/y⁸`] (`class_bx`), `a/p²` [`800y⁶/y^{208}`] (`class_ap2`), `w″` [`8y⁵/y⁸`]
  (`class_w`);
* `La·a/(pk)`, at `p ≥ p₀` and at `p < p₀` [`160000y^{10}/y^{36}`] (`class_La`, `La ≤ 200y³`);
* at `p < p₀`: `b′` [`12928x^{74}/x^{410}`] (`class_b2`), `a/(kx^{26})⁴` [`400x²/x^{52}`] (`class_aY`), `w″` and
  `δ₁b′` [`10368x^{74}/x^{410}`] (`class_w2`);
* the small and odd orders [`1008y⁸/|A|`] (`class_OS`, `Setting.TwoAdic.sum_log_div_le`), the band
  [`460832y⁵/y⁸`] (`class_B`, `ρ_B ≤ 1800/y⁸`), the bad tops [`16y⁵/y^{16}`] (`class_G`, G1);
* beyond `X″` [`48y⁵/y⁸`] (`class_beyond`), and at `d`, where `128m·(log⌈2a⌉ + log d) ≤ d` (`class_d`).

**Against the spec.**
* The statement is the spec's: no `ι` term, the gain's (twisted) coordinates, every `κ`. `Dg` is implicit, as in
  `GainOrbit` and `GainAsk`.
* The budget is uniform and cruder than the spec's table: every class against `|A|·a/64` (the factor `x^{2ε}` of `c_G`
  is not used), with `m ≤ 2x^{1/2}`, `|TT| ≤ |A|` and the elementary sums of `GainSums`; the margins are at least
  `y³ ≥ 10^{27}`.
* The small orders and the odd orders are one class: one `Setting.TwoAdic.sum_log_div_le` at `X = X″ + 1` and
  `y = ⌈x^{ε/4}⌉`, in place of `DesignAdm.sum_log_div_smallOrder_le` below `X′`.
* The polynomial rows of the spec's table (`2c₀L`, the orbits' slacks, `Q_p`, `D_p`) are one class, absorbed by the
  growth package (`x^{1000}·X′^{G′+2} ≤ b`). The orbits' slack `c_{dl,1}·2|A|·N_m²·log_p 2a` needs it as well as
  `Q_p` does: with `N_m² ≤ x^{806}`, the margin `b/X′ ≥ x^{440}` of `DesignBig` alone is short.
-/

open Finset

namespace ZetaBalance

noncomputable section

namespace SharpDesign

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} {Dg : SharpDesign S κ x ε X}

/-! ## The slacks, summed -/

/-- **A sum against `log p`, `log p/p²` and `log p/p`**: termwise bounds `f(p) ≤ A + c₁ log p + c₂ log p/p² +
c₃ log p/p` sum to `|P|·A + c₁Σ log p + c₂Σ log p/p² + c₃Σ log p/p`. -/
theorem sum_le_of_log {P : Finset ℕ} {f : ℕ → ℝ} {A c₁ c₂ c₃ : ℝ}
    (h : ∀ p ∈ P, f p ≤ A + c₁ * Real.log p + c₂ * (Real.log p / (p : ℝ) ^ 2) + c₃ * (Real.log p / p)) :
    ∑ p ∈ P, f p ≤ P.card * A + c₁ * ∑ p ∈ P, Real.log p + c₂ * ∑ p ∈ P, Real.log p / (p : ℝ) ^ 2 +
      c₃ * ∑ p ∈ P, Real.log p / p := by
  refine (sum_le_sum h).trans (le_of_eq ?_)
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]

open scoped Classical in
/-- **The candidates lie below `X′`.** -/
theorem lt_scX'_of_mem_cand {p : ℕ} (h : p ∈ S.cand κ x ε Dg.R.k) : (p : ℝ) < scX' x ε :=
  Nat.lt_ceil.1 (mem_range.1 (mem_filter.1 (mem_filter.1 h).1).1)

/-- **The inert and signal `p ≤ X″` are at most `X″`.** -/
theorem le_cutX_of_mem_inertPrimes (hx : 0 ≤ x) {p : ℕ} (h : p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε)) :
    (p : ℝ) ≤ S.cutX x ε := by
  have hX0 : 0 ≤ S.cutX x ε := by unfold Setting.cutX; positivity
  have h2 := mem_range.1 (mem_filter.1 h).1
  exact (Nat.cast_le.2 (by omega : p ≤ ⌊S.cutX x ε⌋₊)).trans (Nat.floor_le hX0)

/-- **The number of inert and signal `p ≤ X″`** is at most `X″ + 1`. -/
theorem card_inertPrimes_le (hx : 0 ≤ x) :
    ((Setting.Ranks.inertPrimes (S := S) (S.cutX x ε)).card : ℝ) ≤ S.cutX x ε + 1 := by
  have hX0 : 0 ≤ S.cutX x ε := by unfold Setting.cutX; positivity
  have h := card_le_card (filter_subset (fun p => p.Prime ∧ ¬ p ∣ S.N ∧ S.cls p ≠ .split)
    (range (⌊S.cutX x ε⌋₊ + 1)))
  rw [card_range] at h
  have h' : ((Setting.Ranks.inertPrimes (S := S) (S.cutX x ε)).card : ℝ) ≤ ⌊S.cutX x ε⌋₊ + 1 := by
    exact_mod_cast h
  linarith [Nat.floor_le hX0]

/-- **The slacks, summed** over the inert and signal `p ≤ X″`: at most `2(X″ + 1)·x^{900}·X′^{G′}` (the polynomial
terms) plus the terms of size `a` of the candidates, summed with `Σ_{p < X′} log p ≤ X′ log X′`,
`Σ_{p₀ ≤ p < X′} log p/p² ≤ 2 log X′/p₀`, `Σ_{p < X′} log p/p ≤ log X′(1 + log X′)` and
`Σ_{p < p₀} log p ≤ p₀ log p₀`. -/
theorem sum_slack_le (hs : Dg.LossSizes) :
    ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε),
        2 * Real.log p * (Dg.R.m * (Dg.TT.card * Dg.slack1 p + Dg.slack2 p)) ≤
      2 * (S.cutX x ε + 1) * x ^ 900 * scX' x ε ^ (tilePar x ε Dg.R.k).G' +
      (Dg.R.m * Dg.TT.card * (2 * (scB' x ε / x)) + 4 * Dg.R.m * Fintype.card S.A * Kg.cPr * scW'' S x ε) *
          (scX' x ε * Real.log (scX' x ε)) +
        Dg.R.m * Dg.TT.card * (2 * Kg.cκ₁ * (tilePar x ε Dg.R.k).N₁ * scA x ε) *
          (2 * Real.log (scX' x ε) / scP0 x Dg.R.k) +
        Dg.R.m * Dg.TT.card * (2 * Kg.cκ₁ * (tilePar x ε Dg.R.k).N₁ * scLa x ε Dg.R.k * scA x ε / Dg.R.k) *
          (Real.log (scX' x ε) * (1 + Real.log (scX' x ε))) +
      (Dg.R.m * Dg.TT.card * (4 * (tilePar x ε Dg.R.k).r * (1 + Kg.ct) * scB' x ε +
          2 * Kg.ct * (tilePar x ε Dg.R.k).r * (scA x ε / ((Dg.R.k : ℝ) * x ^ 26) ^ 4)) +
        4 * Dg.R.m * Fintype.card S.A * ((tilePar x ε Dg.R.k).r * scW'' S x ε +
          80 * (tilePar x ε Dg.R.k).r * scδ₁ x ε * scB' x ε)) * (scP0 x Dg.R.k * Real.log (scP0 x Dg.R.k)) +
        Dg.R.m * Dg.TT.card * (2 * Kg.ct * (tilePar x ε Dg.R.k).r * scLa x ε Dg.R.k * scA x ε / Dg.R.k) *
          (Real.log (scX' x ε) * (1 + Real.log (scX' x ε))) := by
  classical
  set I := Setting.Ranks.inertPrimes (S := S) (S.cutX x ε) with hI
  set C := I.filter (· ∈ S.cand κ x ε Dg.R.k) with hC
  have hx0 := hs.x_pos
  have hx1 : (1 : ℝ) ≤ x := by linarith [hs.x_ge]
  have hX'1 : (1 : ℝ) ≤ scX' x ε := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hP1 : (1 : ℝ) ≤ scX' x ε ^ (tilePar x ε Dg.R.k).G' := one_le_pow₀ hX'1
  have hp₀1 : (1 : ℝ) ≤ scP0 x Dg.R.k := by
    unfold scP0
    have : (1 : ℝ) ≤ Dg.R.k := Dg.one_le_k
    have : (1 : ℝ) ≤ x ^ 26 := one_le_pow₀ hx1
    nlinarith
  have hI2 : ∀ p ∈ I, 2 ≤ p := fun p hp => (mem_filter.1 hp).2.1.two_le
  -- split off the candidates
  have hsplit : ∑ p ∈ I, 2 * Real.log p * (Dg.R.m * (Dg.TT.card * Dg.slack1 p + Dg.slack2 p)) =
      ∑ p ∈ I, 2 * Real.log p * (Dg.R.m * (Dg.TT.card * (2 * Dg.c0 * (gainExps x ε p).card) +
        (Kg.cdl₁ * (2 * Fintype.card S.A) * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.logb p (2 * scA x ε) +
          Kg.cdl₂ * Dg.TT.card * Real.logb p (2 * scA x ε) ^ 2))) +
      (∑ p ∈ C.filter (fun p : ℕ => scP0 x Dg.R.k ≤ (p : ℝ)),
          2 * Real.log p * (Dg.R.m * (Dg.TT.card * Dg.topAllow p +
            (2 * Fintype.card S.A * Dg.orbAllow p + Dg.eSand p))) +
        ∑ p ∈ C.filter (fun p : ℕ => ¬ scP0 x Dg.R.k ≤ (p : ℝ)),
          2 * Real.log p * (Dg.R.m * (Dg.TT.card * Dg.topAllow p +
            (2 * Fintype.card S.A * Dg.orbAllow p + Dg.eSand p)))) := by
    rw [sum_filter_add_sum_filter_not, hC, sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [Dg.slack_eq p]
    split_ifs <;> ring
  rw [hsplit]
  -- the polynomial part off the candidates
  have hbase : ∑ p ∈ I, 2 * Real.log p * (Dg.R.m * (Dg.TT.card * (2 * Dg.c0 * (gainExps x ε p).card) +
      (Kg.cdl₁ * (2 * Fintype.card S.A) * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.logb p (2 * scA x ε) +
        Kg.cdl₂ * Dg.TT.card * Real.logb p (2 * scA x ε) ^ 2))) ≤ I.card * x ^ 900 := by
    refine (sum_le_card_nsmul _ _ _ fun p hp => Dg.base_le hs (hI2 p hp) ?_).trans (nsmul_eq_mul _ _).le
    have := le_cutX_of_mem_inertPrimes hx0.le hp
    linarith [hs.one_le_cutX]
  -- the candidates
  set C₂ := C.filter (fun p : ℕ => scP0 x Dg.R.k ≤ (p : ℝ)) with hC₂
  set C₃ := C.filter (fun p : ℕ => ¬ scP0 x Dg.R.k ≤ (p : ℝ)) with hC₃
  have hmemC : ∀ p ∈ C, 2 ≤ p ∧ (p : ℝ) < scX' x ε := fun p hp =>
    ⟨hI2 p (mem_filter.1 hp).1, lt_scX'_of_mem_cand (mem_filter.1 hp).2⟩
  have hb' : 0 ≤ scB' x ε := (scB'_pos ε hx0).le
  have hw : 0 ≤ scW'' S x ε := (scW''_pos S ε hx0).le
  have ha : 0 ≤ scA x ε := (scA_pos ε hx0).le
  have hla : 0 ≤ Real.log (scA x ε) := Real.log_nonneg (one_le_scA ε hx1)
  have hLa : 0 ≤ scLa x ε Dg.R.k := by unfold scLa; positivity
  have hδ : 0 ≤ scδ₁ x ε := Real.rpow_nonneg hx0.le _
  have hLX : 0 ≤ Real.log (scX' x ε) := Real.log_nonneg hX'1
  have hC2 := sum_le_of_log (P := C₂) (A := x ^ 900 * scX' x ε ^ (tilePar x ε Dg.R.k).G')
    (c₁ := Dg.R.m * Dg.TT.card * (2 * (scB' x ε / x)) + 4 * Dg.R.m * Fintype.card S.A * Kg.cPr * scW'' S x ε)
    (c₂ := Dg.R.m * Dg.TT.card * (2 * Kg.cκ₁ * (tilePar x ε Dg.R.k).N₁ * scA x ε))
    (c₃ := Dg.R.m * Dg.TT.card * (2 * Kg.cκ₁ * (tilePar x ε Dg.R.k).N₁ * scLa x ε Dg.R.k * scA x ε / Dg.R.k))
    (f := fun p => 2 * Real.log p * (Dg.R.m * (Dg.TT.card * Dg.topAllow p +
      (2 * Fintype.card S.A * Dg.orbAllow p + Dg.eSand p)))) fun p hp => by
    obtain ⟨hp2, hpX⟩ := hmemC p (mem_filter.1 hp).1
    exact (Dg.cpart_ge_le hs hp2 hpX (mem_filter.1 hp).2).trans (le_of_eq (by ring))
  have hC3 := sum_le_of_log (P := C₃) (A := x ^ 900 * scX' x ε ^ (tilePar x ε Dg.R.k).G')
    (c₁ := Dg.R.m * Dg.TT.card * (4 * (tilePar x ε Dg.R.k).r * (1 + Kg.ct) * scB' x ε +
          2 * Kg.ct * (tilePar x ε Dg.R.k).r * (scA x ε / ((Dg.R.k : ℝ) * x ^ 26) ^ 4)) +
        4 * Dg.R.m * Fintype.card S.A * ((tilePar x ε Dg.R.k).r * scW'' S x ε +
          80 * (tilePar x ε Dg.R.k).r * scδ₁ x ε * scB' x ε))
    (c₂ := 0)
    (c₃ := Dg.R.m * Dg.TT.card * (2 * Kg.ct * (tilePar x ε Dg.R.k).r * scLa x ε Dg.R.k * scA x ε / Dg.R.k))
    (f := fun p => 2 * Real.log p * (Dg.R.m * (Dg.TT.card * Dg.topAllow p +
      (2 * Fintype.card S.A * Dg.orbAllow p + Dg.eSand p)))) fun p hp => by
    obtain ⟨hp2, hpX⟩ := hmemC p (mem_filter.1 hp).1
    exact (Dg.cpart_lt_le hs hp2 hpX (mem_filter.1 hp).2).trans (le_of_eq (by ring))
  -- the elementary sums
  have s1 : ∑ p ∈ C₂, Real.log p ≤ scX' x ε * Real.log (scX' x ε) := sum_log_le_of_mem hX'1 fun p hp =>
    ⟨by have := (hmemC p (mem_filter.1 hp).1).1; omega, (hmemC p (mem_filter.1 hp).1).2.le⟩
  have s2 : ∑ p ∈ C₂, Real.log p / (p : ℝ) ^ 2 ≤ 2 * Real.log (scX' x ε) / scP0 x Dg.R.k :=
    sum_log_div_sq_le_of_mem (by linarith) hX'1 fun p hp => ⟨(mem_filter.1 hp).2, (hmemC p (mem_filter.1 hp).1).2.le⟩
  have s3 : ∑ p ∈ C₂, Real.log p / p ≤ Real.log (scX' x ε) * (1 + Real.log (scX' x ε)) :=
    sum_log_div_le_of_mem hX'1 fun p hp =>
      ⟨by have := (hmemC p (mem_filter.1 hp).1).1; omega, (hmemC p (mem_filter.1 hp).1).2.le⟩
  have t1 : ∑ p ∈ C₃, Real.log p ≤ scP0 x Dg.R.k * Real.log (scP0 x Dg.R.k) := sum_log_le_of_mem hp₀1 fun p hp =>
    ⟨by have := (hmemC p (mem_filter.1 hp).1).1; omega, (not_le.1 (mem_filter.1 hp).2).le⟩
  have t3 : ∑ p ∈ C₃, Real.log p / p ≤ Real.log (scX' x ε) * (1 + Real.log (scX' x ε)) :=
    sum_log_div_le_of_mem hX'1 fun p hp =>
      ⟨by have := (hmemC p (mem_filter.1 hp).1).1; omega, (hmemC p (mem_filter.1 hp).1).2.le⟩
  have m1 := mul_le_mul_of_nonneg_left s1 (by positivity : (0 : ℝ) ≤ Dg.R.m * Dg.TT.card * (2 * (scB' x ε / x)) +
    4 * Dg.R.m * Fintype.card S.A * Kg.cPr * scW'' S x ε)
  have m2 := mul_le_mul_of_nonneg_left s2 (by positivity : (0 : ℝ) ≤
    Dg.R.m * Dg.TT.card * (2 * Kg.cκ₁ * (tilePar x ε Dg.R.k).N₁ * scA x ε))
  have m3 := mul_le_mul_of_nonneg_left s3 (by positivity : (0 : ℝ) ≤
    Dg.R.m * Dg.TT.card * (2 * Kg.cκ₁ * (tilePar x ε Dg.R.k).N₁ * scLa x ε Dg.R.k * scA x ε / Dg.R.k))
  have n1 := mul_le_mul_of_nonneg_left t1 (by positivity : (0 : ℝ) ≤
    Dg.R.m * Dg.TT.card * (4 * (tilePar x ε Dg.R.k).r * (1 + Kg.ct) * scB' x ε +
          2 * Kg.ct * (tilePar x ε Dg.R.k).r * (scA x ε / ((Dg.R.k : ℝ) * x ^ 26) ^ 4)) +
        4 * Dg.R.m * Fintype.card S.A * ((tilePar x ε Dg.R.k).r * scW'' S x ε +
          80 * (tilePar x ε Dg.R.k).r * scδ₁ x ε * scB' x ε))
  have n3 := mul_le_mul_of_nonneg_left t3 (by positivity : (0 : ℝ) ≤
    Dg.R.m * Dg.TT.card * (2 * Kg.ct * (tilePar x ε Dg.R.k).r * scLa x ε Dg.R.k * scA x ε / Dg.R.k))
  -- the counts
  have hcard : (I.card : ℝ) * x ^ 900 + (C₂.card * (x ^ 900 * scX' x ε ^ (tilePar x ε Dg.R.k).G') +
      C₃.card * (x ^ 900 * scX' x ε ^ (tilePar x ε Dg.R.k).G')) ≤
      2 * (S.cutX x ε + 1) * x ^ 900 * scX' x ε ^ (tilePar x ε Dg.R.k).G' := by
    have h1 : C₂.card + C₃.card = C.card := card_filter_add_card_filter_not _
    have h2 : C.card ≤ I.card := card_filter_le _ _
    have h3 : ((C₂.card : ℝ) + C₃.card) ≤ S.cutX x ε + 1 := by
      have : ((C₂.card + C₃.card : ℕ) : ℝ) ≤ I.card := by rw [h1]; exact_mod_cast h2
      push_cast at this
      linarith [card_inertPrimes_le (S := S) (ε := ε) hx0.le]
    have h4 := card_inertPrimes_le (S := S) (ε := ε) hx0.le
    have hx9 : 0 ≤ x ^ 900 := by positivity
    have hX0 : 0 ≤ S.cutX x ε := by linarith [hs.one_le_cutX]
    have h5 : (I.card : ℝ) * x ^ 900 ≤ (S.cutX x ε + 1) * x ^ 900 * scX' x ε ^ (tilePar x ε Dg.R.k).G' := by
      calc (I.card : ℝ) * x ^ 900 ≤ (S.cutX x ε + 1) * x ^ 900 := by gcongr
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hP1
    have h6 : ((C₂.card : ℝ) + C₃.card) * (x ^ 900 * scX' x ε ^ (tilePar x ε Dg.R.k).G') ≤
        (S.cutX x ε + 1) * (x ^ 900 * scX' x ε ^ (tilePar x ε Dg.R.k).G') := by gcongr
    linarith
  linear_combination hbase + hC2 + hC3 + m1 + m2 + m3 + n1 + n3 + hcard

/-! ## Beyond the cut-off, and at `d` -/

/-- **The asks beyond `X″`**: at the primes of the ask above `X″` each ask is at most `w″/x` (`askE_le_of_gt`), so
their sum is at most `2m|TT|·(w″/x)·Σ_{p ≤ 2X″} log p ≤ 2m|TT|·(w″/x)·2X″ log 2X″`. -/
theorem sum_beyond_le (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (hs : Dg.LossSizes) (u : S.A) :
    ∑ p ∈ S.askSupp x ε \ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε),
        2 * Real.log p * ∑ J, ∑ t ∈ Dg.TT, Dg.askE u J p t ≤
      2 * (Dg.R.m * Dg.TT.card * (scW'' S x ε / x)) * (2 * S.cutX x ε * Real.log (2 * S.cutX x ε)) := by
  have hx0 := hs.x_pos
  have hX1 := hs.one_le_cutX
  have hw : 0 ≤ scW'' S x ε / x := div_nonneg (scW''_pos S ε hx0).le hx0.le
  have hmem : ∀ p ∈ S.askSupp x ε \ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε),
      2 ≤ p ∧ S.cutX x ε < p ∧ (p : ℝ) ≤ 2 * S.cutX x ε := by
    intro p hp
    obtain ⟨hpa, hpi⟩ := mem_sdiff.1 hp
    obtain ⟨hpr, hp', hN, hcls⟩ := mem_filter.1 hpa
    refine ⟨hp'.two_le, ?_, ?_⟩
    · have h1 : ¬ p < ⌊S.cutX x ε⌋₊ + 1 := fun h => hpi (mem_filter.2 ⟨mem_range.2 h, hp', hN, hcls⟩)
      have h2 : ⌊S.cutX x ε⌋₊ + 1 ≤ p := by omega
      have h3 := Nat.lt_floor_add_one (S.cutX x ε)
      have h4 : ((⌊S.cutX x ε⌋₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast h2
      push_cast at h4
      linarith
    · have h1 := mem_range.1 hpr
      exact (Nat.cast_le.2 (by omega : p ≤ ⌊2 * S.cutX x ε⌋₊)).trans (Nat.floor_le (by linarith))
  have hpt : ∀ p ∈ S.askSupp x ε \ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε),
      2 * Real.log p * ∑ J, ∑ t ∈ Dg.TT, Dg.askE u J p t ≤
        2 * (Dg.R.m * Dg.TT.card * (scW'' S x ε / x)) * Real.log p := by
    intro p hp
    obtain ⟨hp2, hpX, -⟩ := hmem p hp
    have h1 : ∑ J, ∑ t ∈ Dg.TT, Dg.askE u J p t ≤ Dg.R.m * Dg.TT.card * (scW'' S x ε / x) := by
      calc ∑ J, ∑ t ∈ Dg.TT, Dg.askE u J p t ≤ ∑ _J : Fin Dg.R.m, Dg.TT.card * (scW'' S x ε / x) := by
            refine sum_le_sum fun J _ => ?_
            calc ∑ t ∈ Dg.TT, Dg.askE u J p t ≤ Dg.TT.card • (scW'' S x ε / x) :=
                  sum_le_card_nsmul _ _ _ fun t ht => askE_le_of_gt hA hF u J hp2 hpX ht
              _ = _ := nsmul_eq_mul _ _
        _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    have hl : 0 ≤ 2 * Real.log p := by have := Real.log_natCast_nonneg p; linarith
    calc 2 * Real.log p * ∑ J, ∑ t ∈ Dg.TT, Dg.askE u J p t ≤
        2 * Real.log p * (Dg.R.m * Dg.TT.card * (scW'' S x ε / x)) := mul_le_mul_of_nonneg_left h1 hl
      _ = _ := by ring
  have hs1 : ∑ p ∈ S.askSupp x ε \ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε), Real.log p ≤
      2 * S.cutX x ε * Real.log (2 * S.cutX x ε) :=
    sum_log_le_of_mem (by linarith) fun p hp => ⟨by have := (hmem p hp).1; omega, (hmem p hp).2.2⟩
  calc _ ≤ ∑ p ∈ S.askSupp x ε \ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε),
        2 * (Dg.R.m * Dg.TT.card * (scW'' S x ε / x)) * Real.log p := sum_le_sum hpt
    _ = 2 * (Dg.R.m * Dg.TT.card * (scW'' S x ε / x)) *
        ∑ p ∈ S.askSupp x ε \ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε), Real.log p := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hs1 (by positivity)

/-- **The ask at `d`, summed**: `Σ_t Σ_j log d·askAtD ≤ m|TT|·(log⌈2a⌉ + log d)·2a/d` (`log_mul_askAtD_le`). -/
theorem sum_atD_le (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (u : S.A) :
    ∑ t ∈ Dg.TT, ∑ J, Real.log S.d * Dg.askAtD u J t ≤
      Dg.R.m * Dg.TT.card * ((Real.log ⌈2 * scA x ε⌉₊ + Real.log S.d) * (2 * scA x ε / S.d)) := by
  calc ∑ t ∈ Dg.TT, ∑ J, Real.log S.d * Dg.askAtD u J t ≤
      ∑ _t ∈ Dg.TT, ∑ _J : Fin Dg.R.m, (Real.log ⌈2 * scA x ε⌉₊ + Real.log S.d) * (2 * scA x ε / S.d) :=
        sum_le_sum fun t ht => sum_le_sum fun J _ => log_mul_askAtD_le hA hF u J ht
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-! ## The classes against the budget

Each class is at most `|A|·a/64` (`c_G ≥ |A|·a`), with `y = x^{1/8} ≥ 10⁹`: the terms of size `a` by a power of `y`
(`m ≤ 2y⁴`, `|TT| ≤ |A|`, `|A| ≥ y^{16}`, `k ≥ y^{36}`, every power `x^{cε}` and `N₁, r, log x ≤ y`), the terms with
`b′ = a/X′` or `a/(kx^{26})⁴` by `X′ ≥ x^{410}`, and the polynomial terms by `b ≥ x^{1000}X′^{G′+2}`. -/

/-- `A·a·K ≤ A·a/64` for `64K ≤ 1`, `A·a ≥ 0`. -/
theorem mul_le_div64 {A a K : ℝ} (hAa : 0 ≤ A * a) (hK : 64 * K ≤ 1) : A * a * K ≤ A * a / 64 := by
  nlinarith

namespace LossSizes

variable (hs : Dg.LossSizes)
include hs

/-- `c·y^m ≤ y^n` for `c ≤ 10⁹`, `m < n`. -/
theorem cy_le {c : ℝ} (hc : c ≤ 10 ^ 9) {m n : ℕ} (h : m + 1 ≤ n) :
    c * (x ^ (1 / 8 : ℝ)) ^ m ≤ (x ^ (1 / 8 : ℝ)) ^ n :=
  mul_pow_le_pow hs.one_le_y (k := 1) (by rw [pow_one]; linarith [hs.y_ge]) h

/-- `La ≤ 200y³`. -/
theorem scLa_le : scLa x ε Dg.R.k ≤ 200 * (x ^ (1 / 8 : ℝ)) ^ 3 := by
  have hN1 : ((tilePar x ε Dg.R.k).N₁ : ℝ) ≤ x ^ (1 / 8 : ℝ) := by
    linarith [hs.N₁r_le, (Nat.cast_nonneg _ : (0 : ℝ) ≤ (tilePar x ε Dg.R.k).r)]
  have hla := hs.log_scA_le
  have hc : (Kg.cLa : ℝ) = 100 := by norm_num [Kg]
  unfold scLa
  rw [hc]
  calc 100 * ((tilePar x ε Dg.R.k).N₁ : ℝ) ^ 2 * Real.log (scA x ε) ≤
      100 * (x ^ (1 / 8 : ℝ)) ^ 2 * (2 * x ^ (1 / 8 : ℝ)) := by
        have : 0 ≤ Real.log (scA x ε) := Real.log_nonneg (one_le_scA ε (by linarith [hs.x_ge]))
        gcongr
  _ = 200 * (x ^ (1 / 8 : ℝ)) ^ 3 := by ring

/-- `La ≥ 0`. -/
theorem scLa_nonneg : 0 ≤ scLa x ε Dg.R.k := by
  have : 0 ≤ Real.log (scA x ε) := Real.log_nonneg (one_le_scA ε (by linarith [hs.x_ge]))
  unfold scLa; positivity

/-- **The band is thin**: `ρ_B ≤ 1800/y⁸`, as `N_⋆ ≤ 2|A| ≤ 2y^{24}`, `x^ε ≤ y`, `La ≤ 200y³` and `k ≥ y^{36}`. -/
theorem rhoB_le : scRhoB S x ε Dg.R.k * (x ^ (1 / 8 : ℝ)) ^ 8 ≤ 1800 := by
  set y := x ^ (1 / 8 : ℝ) with hy
  have hy1 := hs.one_le_y
  have hy9 := hs.y_ge
  have hk := hs.k_ge
  have hk0 : 0 < (Dg.R.k : ℝ) := lt_of_lt_of_le (by positivity) hk
  have hLa := hs.scLa_le
  have hLa0 := hs.scLa_nonneg
  have hA : (Fintype.card S.A : ℝ) ≤ y ^ 24 := by
    have := hs.A_le; rw [← hs.y_pow] at this; linarith [show (y ^ 8) ^ 3 = y ^ 24 by ring]
  have hN : scNstar S x ε ≤ 2 * y ^ 24 := by
    unfold scNstar
    have := hs.δ_le
    have : 0 ≤ (Fintype.card S.A : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hN0 : 0 ≤ scNstar S x ε := by unfold scNstar; have := Real.rpow_nonneg hs.x_pos.le (-(ε / 8)); positivity
  have hxe := hs.xε_le
  have hxe0 : 0 ≤ x ^ ε := Real.rpow_nonneg hs.x_pos.le ε
  have hlx := hs.log_le
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith [hs.x_ge])
  have hc : (Kg.cρ : ℝ) * Kg.cN = 10000 := by norm_num [Kg]
  have h1 : 4 * scNstar S x ε * x ^ ε * scLa x ε Dg.R.k + Kg.cρ * Kg.cN * Real.log x * scLa x ε Dg.R.k ≤
      1800 * y ^ 28 := by
    rw [mul_assoc (Kg.cρ : ℝ), ← mul_assoc, hc]
    have a1 : 4 * scNstar S x ε * x ^ ε * scLa x ε Dg.R.k ≤ 4 * (2 * y ^ 24) * y * (200 * y ^ 3) := by gcongr
    have a2 : 10000 * Real.log x * scLa x ε Dg.R.k ≤ 10000 * y * (200 * y ^ 3) := by gcongr
    have a3 : 10000 * y * (200 * y ^ 3) ≤ 200 * y ^ 28 := by
      have := hs.cy_le (c := 10000) (by norm_num) (show 4 + 1 ≤ 28 by norm_num)
      nlinarith
    nlinarith
  have e : scRhoB S x ε Dg.R.k = (4 * scNstar S x ε * x ^ ε * scLa x ε Dg.R.k +
      Kg.cρ * Kg.cN * Real.log x * scLa x ε Dg.R.k) / Dg.R.k := by unfold scRhoB; ring
  rw [e, div_mul_eq_mul_div, div_le_iff₀ hk0]
  calc (4 * scNstar S x ε * x ^ ε * scLa x ε Dg.R.k + Kg.cρ * Kg.cN * Real.log x * scLa x ε Dg.R.k) * y ^ 8 ≤
      1800 * y ^ 28 * y ^ 8 := by gcongr
    _ = 1800 * y ^ 36 := by ring
    _ ≤ 1800 * Dg.R.k := by gcongr

/-- `ρ_B ≥ 0`. -/
theorem rhoB_nonneg : 0 ≤ scRhoB S x ε Dg.R.k := by
  have := hs.scLa_nonneg
  have : 0 ≤ Real.log x := Real.log_nonneg (by linarith [hs.x_ge])
  have : 0 ≤ scNstar S x ε := by unfold scNstar; have := Real.rpow_nonneg hs.x_pos.le (-(ε / 8)); positivity
  have : 0 ≤ x ^ ε := Real.rpow_nonneg hs.x_pos.le ε
  unfold scRhoB; positivity

/-- `p₀ ≥ x^{26}`. -/
theorem scP0_ge : x ^ 26 ≤ scP0 x Dg.R.k := by
  have h1 : (1 : ℝ) ≤ (Dg.R.k : ℝ) ^ 2 := one_le_pow₀ Dg.one_le_k
  unfold scP0
  have : 0 ≤ x ^ 26 := by have := hs.x_pos; positivity
  exact le_mul_of_one_le_left this h1

/-- `p₀ ≤ 4x^{36}`. -/
theorem scP0_le : scP0 x Dg.R.k ≤ 4 * x ^ 36 := by
  have hk := hs.k_le
  have : (0 : ℝ) ≤ Dg.R.k := Nat.cast_nonneg _
  unfold scP0
  calc (Dg.R.k : ℝ) ^ 2 * x ^ 26 ≤ (2 * x ^ 5) ^ 2 * x ^ 26 := by gcongr
    _ = 4 * x ^ 36 := by ring

/-- `64·(K·y^m/y^n) ≤ 1` for `64K ≤ 10⁹`, `m < n`. -/
theorem frac_le {K : ℝ} (hK' : 64 * K ≤ 10 ^ 9) {m n : ℕ} (h : m + 1 ≤ n) :
    64 * (K * (x ^ (1 / 8 : ℝ)) ^ m / (x ^ (1 / 8 : ℝ)) ^ n) ≤ 1 := by
  have hy0 : 0 < (x ^ (1 / 8 : ℝ)) ^ n := pow_pos (by linarith [hs.one_le_y]) n
  rw [← mul_div_assoc, div_le_one hy0, ← mul_assoc]
  exact hs.cy_le hK' h

/-- `64·(K·x^m/x^n) ≤ 1` for `64K ≤ 4096²`, `m + 2 ≤ n`. -/
theorem frac_le_x {K : ℝ} (hK' : 64 * K ≤ 16777216) {m n : ℕ} (h : m + 2 ≤ n) :
    64 * (K * x ^ m / x ^ n) ≤ 1 := by
  have hx1 : (1 : ℝ) ≤ x := by linarith [hs.x_ge]
  have hy0 : 0 < x ^ n := pow_pos (by linarith) n
  rw [← mul_div_assoc, div_le_one hy0, ← mul_assoc]
  exact mul_pow_le_pow hx1 (k := 2) (const_le_sq hs.x_ge hK') h

/-- `X′ ≥ x`. -/
theorem x_le_scX' : x ≤ scX' x ε :=
  (le_self_pow₀ (by linarith [hs.x_ge]) (by norm_num)).trans hs.X'_ge

/-- `x^{1000}·X′^{G′+1}·x ≤ a`, from the growth package. -/
theorem pow_le_scA : x ^ 1001 * scX' x ε ^ ((tilePar x ε Dg.R.k).G' + 2) ≤ scA x ε := by
  have h := hs.b_ge
  unfold scA
  have hx0 := hs.x_pos
  calc x ^ 1001 * scX' x ε ^ ((tilePar x ε Dg.R.k).G' + 2) =
      x * (x ^ 1000 * scX' x ε ^ ((tilePar x ε Dg.R.k).G' + 2)) := by ring
    _ ≤ x * scB x ε := by gcongr

/-- **The polynomial class**: `2(X″ + 1)·x^{900}·X′^{G′} ≤ |A|a/64`, as `X″ + 1 ≤ 2x|A|X′` and
`a ≥ x^{1001}X′^{G′+2}`. -/
theorem class_poly :
    2 * (S.cutX x ε + 1) * x ^ 900 * scX' x ε ^ (tilePar x ε Dg.R.k).G' ≤ Fintype.card S.A * scA x ε / 64 := by
  have hx0 := hs.x_pos
  have hx1 : (1 : ℝ) ≤ x := by linarith [hs.x_ge]
  have hX1 := hs.one_le_cutX
  have hA1 : (1 : ℝ) ≤ Fintype.card S.A := by exact_mod_cast Fintype.card_pos
  have hX'0 : 0 < scX' x ε := Real.exp_pos _
  set G := (tilePar x ε Dg.R.k).G'
  have hP0 : 0 ≤ scX' x ε ^ G := by positivity
  have h1 : S.cutX x ε + 1 ≤ 2 * x * Fintype.card S.A * scX' x ε := by
    have : S.cutX x ε = x * Fintype.card S.A * scX' x ε := rfl
    linarith
  have h2 := hs.pow_le_scA
  have h3 : 256 * x ^ 901 ≤ x ^ 1001 * scX' x ε := by
    have : 256 * x ^ 901 ≤ x ^ 1001 := mul_pow_le_pow hx1 (k := 1) (by linarith [hs.x_ge]) (by norm_num)
    nlinarith [hs.x_le_scX', pow_pos hx0 1001]
  calc 2 * (S.cutX x ε + 1) * x ^ 900 * scX' x ε ^ G ≤
      2 * (2 * x * Fintype.card S.A * scX' x ε) * x ^ 900 * scX' x ε ^ G := by gcongr
    _ = Fintype.card S.A * (256 * x ^ 901 * scX' x ε ^ (G + 1)) / 64 := by ring
    _ ≤ Fintype.card S.A * (x ^ 1001 * scX' x ε * scX' x ε ^ (G + 1)) / 64 := by gcongr
    _ = Fintype.card S.A * (x ^ 1001 * scX' x ε ^ (G + 2)) / 64 := by ring
    _ ≤ Fintype.card S.A * scA x ε / 64 := by gcongr

/-- **The class `b′/x`** (the per-top window `b′/x` of `topAllow` at `p ≥ p₀`): `m|TT|·2(b′/x)·X′ log X′ =
2m|TT|·a·x^{ε/3}/x ≤ |A|a·4y⁵/y⁸`. -/
theorem class_bx :
    Dg.R.m * Dg.TT.card * (2 * (scB' x ε / x)) * (scX' x ε * Real.log (scX' x ε)) ≤
      Fintype.card S.A * scA x ε / 64 := by
  have hx0 := hs.x_pos
  have hy1 := hs.one_le_y
  have hm := hs.m_le
  have ha0 : 0 ≤ scA x ε := (scA_pos ε hx0).le
  have hAa : 0 ≤ (Fintype.card S.A : ℝ) * scA x ε := by positivity
  have hL : Real.log (scX' x ε) ≤ x ^ (1 / 8 : ℝ) := by rw [scX', Real.log_exp]; exact hs.L_le
  have hL0 : 0 ≤ Real.log (scX' x ε) := by rw [scX', Real.log_exp]; positivity
  have e : scB' x ε / x * scX' x ε = scA x ε / x := by rw [← scX'_mul_scB']; field_simp
  calc Dg.R.m * Dg.TT.card * (2 * (scB' x ε / x)) * (scX' x ε * Real.log (scX' x ε)) =
      Dg.TT.card * scA x ε * (2 * Dg.R.m * Real.log (scX' x ε) / x) := by
        rw [show (Dg.R.m : ℝ) * Dg.TT.card * (2 * (scB' x ε / x)) * (scX' x ε * Real.log (scX' x ε)) =
          Dg.R.m * Dg.TT.card * 2 * (scB' x ε / x * scX' x ε) * Real.log (scX' x ε) by ring, e]
        ring
    _ ≤ Fintype.card S.A * scA x ε * (4 * (x ^ (1 / 8 : ℝ)) ^ 5 / (x ^ (1 / 8 : ℝ)) ^ 8) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hs.TT_le ha0) ?_ (by positivity) hAa
        rw [hs.y_pow]
        refine div_le_div_of_nonneg_right ?_ hx0.le
        calc 2 * (Dg.R.m : ℝ) * Real.log (scX' x ε) ≤ 2 * (2 * (x ^ (1 / 8 : ℝ)) ^ 4) * x ^ (1 / 8 : ℝ) := by
              gcongr
          _ = 4 * (x ^ (1 / 8 : ℝ)) ^ 5 := by ring
    _ ≤ _ := mul_le_div64 hAa (hs.frac_le (by norm_num) (by norm_num))

/-- **The class `a/p²`** (`p ≥ p₀`): `m|TT|·2c_{κ,1}N₁a·2 log X′/p₀ ≤ |A|a·800y⁶/y^{208}`. -/
theorem class_ap2 :
    Dg.R.m * Dg.TT.card * (2 * Kg.cκ₁ * (tilePar x ε Dg.R.k).N₁ * scA x ε) *
      (2 * Real.log (scX' x ε) / scP0 x Dg.R.k) ≤ Fintype.card S.A * scA x ε / 64 := by
  have hx0 := hs.x_pos
  have hy1 := hs.one_le_y
  have hm := hs.m_le
  have ha0 : 0 ≤ scA x ε := (scA_pos ε hx0).le
  have hAa : 0 ≤ (Fintype.card S.A : ℝ) * scA x ε := by positivity
  have hL : Real.log (scX' x ε) ≤ x ^ (1 / 8 : ℝ) := by rw [scX', Real.log_exp]; exact hs.L_le
  have hL0 : 0 ≤ Real.log (scX' x ε) := by rw [scX', Real.log_exp]; positivity
  have hN1 : ((tilePar x ε Dg.R.k).N₁ : ℝ) ≤ x ^ (1 / 8 : ℝ) := by
    linarith [hs.N₁r_le, (Nat.cast_nonneg _ : (0 : ℝ) ≤ (tilePar x ε Dg.R.k).r)]
  have hc : (Kg.cκ₁ : ℝ) = 100 := by norm_num [Kg]
  have hy0 : 0 < x ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hp₀ : (x ^ (1 / 8 : ℝ)) ^ 208 ≤ scP0 x Dg.R.k :=
    calc (x ^ (1 / 8 : ℝ)) ^ 208 = ((x ^ (1 / 8 : ℝ)) ^ 8) ^ 26 := by ring
      _ = x ^ 26 := by rw [hs.y_pow]
      _ ≤ _ := hs.scP0_ge
  have hp₀0 : 0 < scP0 x Dg.R.k := lt_of_lt_of_le (pow_pos hy0 _) hp₀
  calc Dg.R.m * Dg.TT.card * (2 * Kg.cκ₁ * (tilePar x ε Dg.R.k).N₁ * scA x ε) *
      (2 * Real.log (scX' x ε) / scP0 x Dg.R.k) =
      Dg.TT.card * scA x ε * (4 * Kg.cκ₁ * Dg.R.m * (tilePar x ε Dg.R.k).N₁ * Real.log (scX' x ε) /
        scP0 x Dg.R.k) := by ring
    _ ≤ Fintype.card S.A * scA x ε * (800 * (x ^ (1 / 8 : ℝ)) ^ 6 / (x ^ (1 / 8 : ℝ)) ^ 208) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hs.TT_le ha0) ?_ (by positivity) hAa
        refine div_le_div₀ (by positivity) ?_ (pow_pos hy0 _) hp₀
        rw [hc]
        calc 4 * 100 * (Dg.R.m : ℝ) * (tilePar x ε Dg.R.k).N₁ * Real.log (scX' x ε) ≤
            4 * 100 * (2 * (x ^ (1 / 8 : ℝ)) ^ 4) * x ^ (1 / 8 : ℝ) * x ^ (1 / 8 : ℝ) := by gcongr
          _ = 800 * (x ^ (1 / 8 : ℝ)) ^ 6 := by ring
    _ ≤ _ := mul_le_div64 hAa (hs.frac_le (by norm_num) (by norm_num))

/-- **The classes `La·a/(pk)`**: for a coefficient `c ≤ 100y` (`c_{κ,1}N₁` or `c_t·r`),
`m|TT|·2c·La·a/k·log X′(1 + log X′) ≤ |A|a·160000y^{10}/y^{36}`. -/
theorem class_La {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 100 * x ^ (1 / 8 : ℝ)) :
    Dg.R.m * Dg.TT.card * (2 * c * scLa x ε Dg.R.k * scA x ε / Dg.R.k) *
      (Real.log (scX' x ε) * (1 + Real.log (scX' x ε))) ≤ Fintype.card S.A * scA x ε / 64 := by
  have hx0 := hs.x_pos
  have hy1 := hs.one_le_y
  have hm := hs.m_le
  have ha0 : 0 ≤ scA x ε := (scA_pos ε hx0).le
  have hAa : 0 ≤ (Fintype.card S.A : ℝ) * scA x ε := by positivity
  have hL : Real.log (scX' x ε) ≤ x ^ (1 / 8 : ℝ) := by rw [scX', Real.log_exp]; exact hs.L_le
  have hL0 : 0 ≤ Real.log (scX' x ε) := by rw [scX', Real.log_exp]; positivity
  have hLa := hs.scLa_le
  have hLa0 := hs.scLa_nonneg
  have hk := hs.k_ge
  calc Dg.R.m * Dg.TT.card * (2 * c * scLa x ε Dg.R.k * scA x ε / Dg.R.k) *
      (Real.log (scX' x ε) * (1 + Real.log (scX' x ε))) =
      Dg.TT.card * scA x ε * (2 * c * Dg.R.m * scLa x ε Dg.R.k *
        (Real.log (scX' x ε) * (1 + Real.log (scX' x ε))) / Dg.R.k) := by ring
    _ ≤ Fintype.card S.A * scA x ε * (160000 * (x ^ (1 / 8 : ℝ)) ^ 10 / (x ^ (1 / 8 : ℝ)) ^ 36) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hs.TT_le ha0) ?_ (by positivity) hAa
        refine div_le_div₀ (by positivity) ?_ (by positivity) hk
        calc 2 * c * Dg.R.m * scLa x ε Dg.R.k * (Real.log (scX' x ε) * (1 + Real.log (scX' x ε))) ≤
            2 * (100 * x ^ (1 / 8 : ℝ)) * (2 * (x ^ (1 / 8 : ℝ)) ^ 4) * (200 * (x ^ (1 / 8 : ℝ)) ^ 3) *
              (x ^ (1 / 8 : ℝ) * (x ^ (1 / 8 : ℝ) + x ^ (1 / 8 : ℝ))) := by gcongr
          _ = 160000 * (x ^ (1 / 8 : ℝ)) ^ 10 := by ring
    _ ≤ _ := mul_le_div64 hAa (hs.frac_le (by norm_num) (by norm_num))

/-- **The class `w″` at `p ≥ p₀`**: `4m|A|·c_Pr·w″·X′ log X′ = 4m·c_Pr·a·x^{ε/3}/x ≤ |A|a·8y⁵/y⁸`. -/
theorem class_w :
    4 * Dg.R.m * Fintype.card S.A * Kg.cPr * scW'' S x ε * (scX' x ε * Real.log (scX' x ε)) ≤
      Fintype.card S.A * scA x ε / 64 := by
  have hx0 := hs.x_pos
  have hy1 := hs.one_le_y
  have hm := hs.m_le
  have ha0 : 0 ≤ scA x ε := (scA_pos ε hx0).le
  have hA1 : (1 : ℝ) ≤ Fintype.card S.A := by exact_mod_cast Fintype.card_pos
  have hAa : 0 ≤ (Fintype.card S.A : ℝ) * scA x ε := by positivity
  have hL : Real.log (scX' x ε) ≤ x ^ (1 / 8 : ℝ) := by rw [scX', Real.log_exp]; exact hs.L_le
  have hL0 : 0 ≤ Real.log (scX' x ε) := by rw [scX', Real.log_exp]; positivity
  have hc : (Kg.cPr : ℝ) = 1 := by norm_num [Kg]
  have e : Fintype.card S.A * scW'' S x ε * scX' x ε = scA x ε / x := by
    unfold scW''; rw [← scX'_mul_scB']; field_simp
  calc 4 * Dg.R.m * Fintype.card S.A * Kg.cPr * scW'' S x ε * (scX' x ε * Real.log (scX' x ε)) =
      Fintype.card S.A * scA x ε * (4 * Dg.R.m * Real.log (scX' x ε) / (x * Fintype.card S.A)) := by
        rw [hc, show 4 * (Dg.R.m : ℝ) * Fintype.card S.A * 1 * scW'' S x ε * (scX' x ε * Real.log (scX' x ε)) =
          4 * Dg.R.m * (Fintype.card S.A * scW'' S x ε * scX' x ε) * Real.log (scX' x ε) by ring, e]
        field_simp
    _ ≤ Fintype.card S.A * scA x ε * (8 * (x ^ (1 / 8 : ℝ)) ^ 5 / (x ^ (1 / 8 : ℝ)) ^ 8) := by
        refine mul_le_mul_of_nonneg_left ?_ hAa
        rw [hs.y_pow]
        refine div_le_div₀ (by positivity) ?_ hx0 (le_mul_of_one_le_right hx0.le hA1)
        calc 4 * (Dg.R.m : ℝ) * Real.log (scX' x ε) ≤ 4 * (2 * (x ^ (1 / 8 : ℝ)) ^ 4) * x ^ (1 / 8 : ℝ) := by
              gcongr
          _ = 8 * (x ^ (1 / 8 : ℝ)) ^ 5 := by ring
    _ ≤ _ := mul_le_div64 hAa (hs.frac_le (by norm_num) (by norm_num))

/-- `p₀ log p₀ ≤ p₀²`. -/
theorem scP0_log_le : scP0 x Dg.R.k * Real.log (scP0 x Dg.R.k) ≤ scP0 x Dg.R.k ^ 2 := by
  have h0 : 0 < scP0 x Dg.R.k := lt_of_lt_of_le (by have := hs.x_pos; positivity) hs.scP0_ge
  have := Real.log_le_sub_one_of_pos h0
  nlinarith

/-- **The class `b′` at `p < p₀`**: `m|TT|·4r(1 + c_t)·b′·p₀ log p₀ ≤ |A|a·12928x^{74}/x^{410}`. -/
theorem class_b2 :
    Dg.R.m * Dg.TT.card * (4 * (tilePar x ε Dg.R.k).r * (1 + Kg.ct) * scB' x ε) *
      (scP0 x Dg.R.k * Real.log (scP0 x Dg.R.k)) ≤ Fintype.card S.A * scA x ε / 64 := by
  have hx0 := hs.x_pos
  have hx1 : (1 : ℝ) ≤ x := by linarith [hs.x_ge]
  have hm := hs.m_le_x
  have ha0 : 0 ≤ scA x ε := (scA_pos ε hx0).le
  have hAa : 0 ≤ (Fintype.card S.A : ℝ) * scA x ε := by positivity
  have hr : ((tilePar x ε Dg.R.k).r : ℝ) ≤ x := by
    linarith [hs.N₁r_le, (Nat.cast_nonneg _ : (0 : ℝ) ≤ (tilePar x ε Dg.R.k).N₁), hs.y_le_x]
  have hc : (Kg.ct : ℝ) = 100 := by norm_num [Kg]
  have hp₀0 : 0 ≤ scP0 x Dg.R.k * Real.log (scP0 x Dg.R.k) := by
    have h1 : 1 ≤ scP0 x Dg.R.k := le_trans (one_le_pow₀ hx1) hs.scP0_ge
    have := Real.log_nonneg h1
    positivity
  have hΛ : scP0 x Dg.R.k * Real.log (scP0 x Dg.R.k) ≤ 16 * x ^ 72 := by
    have h1 := hs.scP0_log_le
    have h2 := hs.scP0_le
    have h3 : 0 ≤ scP0 x Dg.R.k := le_trans (by positivity) hs.scP0_ge
    nlinarith
  have hX' := hs.X'_ge
  have hX'0 : 0 < scX' x ε := Real.exp_pos _
  have e : scB' x ε = scA x ε / scX' x ε := rfl
  calc Dg.R.m * Dg.TT.card * (4 * (tilePar x ε Dg.R.k).r * (1 + Kg.ct) * scB' x ε) *
      (scP0 x Dg.R.k * Real.log (scP0 x Dg.R.k)) =
      Dg.TT.card * scA x ε * (4 * (tilePar x ε Dg.R.k).r * (1 + Kg.ct) * Dg.R.m *
        (scP0 x Dg.R.k * Real.log (scP0 x Dg.R.k)) / scX' x ε) := by rw [e]; ring
    _ ≤ Fintype.card S.A * scA x ε * (12928 * x ^ 74 / x ^ 410) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hs.TT_le ha0) ?_ (by positivity) hAa
        refine div_le_div₀ (by positivity) ?_ (by positivity) hX'
        rw [hc]
        calc 4 * ((tilePar x ε Dg.R.k).r : ℝ) * (1 + 100) * Dg.R.m * (scP0 x Dg.R.k * Real.log (scP0 x Dg.R.k)) ≤
            4 * x * (1 + 100) * (2 * x) * (16 * x ^ 72) := by gcongr
          _ = 12928 * x ^ 74 := by ring
    _ ≤ _ := mul_le_div64 hAa (hs.frac_le_x (by norm_num) (by norm_num))

/-- **The class `a/(kx^{26})⁴`** (`p < p₀`): `m|TT|·2c_t·r·a/(kx^{26})⁴·p₀ log p₀ ≤ |A|a·400x²/x^{52}`, as
`p₀² x^{52} = (kx^{26})⁴`. -/
theorem class_aY :
    Dg.R.m * Dg.TT.card * (2 * Kg.ct * (tilePar x ε Dg.R.k).r * (scA x ε / ((Dg.R.k : ℝ) * x ^ 26) ^ 4)) *
      (scP0 x Dg.R.k * Real.log (scP0 x Dg.R.k)) ≤ Fintype.card S.A * scA x ε / 64 := by
  have hx0 := hs.x_pos
  have hx1 : (1 : ℝ) ≤ x := by linarith [hs.x_ge]
  have hm := hs.m_le_x
  have ha0 : 0 ≤ scA x ε := (scA_pos ε hx0).le
  have hAa : 0 ≤ (Fintype.card S.A : ℝ) * scA x ε := by positivity
  have hr : ((tilePar x ε Dg.R.k).r : ℝ) ≤ x := by
    linarith [hs.N₁r_le, (Nat.cast_nonneg _ : (0 : ℝ) ≤ (tilePar x ε Dg.R.k).N₁), hs.y_le_x]
  have hc : (Kg.ct : ℝ) = 100 := by norm_num [Kg]
  have hp₀0 : 0 < scP0 x Dg.R.k := lt_of_lt_of_le (by positivity) hs.scP0_ge
  have hl0 : 0 ≤ Real.log (scP0 x Dg.R.k) := Real.log_nonneg (le_trans (one_le_pow₀ hx1) hs.scP0_ge)
  have hΛ := hs.scP0_log_le
  have hY : ((Dg.R.k : ℝ) * x ^ 26) ^ 4 = scP0 x Dg.R.k ^ 2 * x ^ 52 := by unfold scP0; ring
  calc Dg.R.m * Dg.TT.card * (2 * Kg.ct * (tilePar x ε Dg.R.k).r * (scA x ε / ((Dg.R.k : ℝ) * x ^ 26) ^ 4)) *
      (scP0 x Dg.R.k * Real.log (scP0 x Dg.R.k)) =
      Dg.TT.card * scA x ε * (2 * Kg.ct * (tilePar x ε Dg.R.k).r * Dg.R.m *
        (scP0 x Dg.R.k * Real.log (scP0 x Dg.R.k)) / (scP0 x Dg.R.k ^ 2 * x ^ 52)) := by rw [hY]; ring
    _ ≤ Fintype.card S.A * scA x ε * (400 * x ^ 2 * scP0 x Dg.R.k ^ 2 / (scP0 x Dg.R.k ^ 2 * x ^ 52)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hs.TT_le ha0) ?_ (by positivity) hAa
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        rw [hc]
        calc 2 * 100 * ((tilePar x ε Dg.R.k).r : ℝ) * Dg.R.m * (scP0 x Dg.R.k * Real.log (scP0 x Dg.R.k)) ≤
            2 * 100 * x * (2 * x) * scP0 x Dg.R.k ^ 2 := by gcongr
          _ = 400 * x ^ 2 * scP0 x Dg.R.k ^ 2 := by ring
    _ = Fintype.card S.A * scA x ε * (400 * x ^ 2 / x ^ 52) := by
        congr 1; field_simp
    _ ≤ _ := mul_le_div64 hAa (hs.frac_le_x (by norm_num) (by norm_num))

/-- **The class `w″, δ₁b′` at `p < p₀`**: `4m|A|·(r·w″ + 80rδ₁b′)·p₀ log p₀ ≤ |A|a·10368x^{74}/x^{410}`
(`w″ ≤ b′`, `δ₁ ≤ 1`). -/
theorem class_w2 :
    4 * Dg.R.m * Fintype.card S.A * ((tilePar x ε Dg.R.k).r * scW'' S x ε +
      80 * (tilePar x ε Dg.R.k).r * scδ₁ x ε * scB' x ε) * (scP0 x Dg.R.k * Real.log (scP0 x Dg.R.k)) ≤
      Fintype.card S.A * scA x ε / 64 := by
  have hx0 := hs.x_pos
  have hx1 : (1 : ℝ) ≤ x := by linarith [hs.x_ge]
  have hm := hs.m_le_x
  have ha0 : 0 ≤ scA x ε := (scA_pos ε hx0).le
  have hA0 : (0 : ℝ) ≤ Fintype.card S.A := Nat.cast_nonneg _
  have hAa : 0 ≤ (Fintype.card S.A : ℝ) * scA x ε := by positivity
  have hr : ((tilePar x ε Dg.R.k).r : ℝ) ≤ x := by
    linarith [hs.N₁r_le, (Nat.cast_nonneg _ : (0 : ℝ) ≤ (tilePar x ε Dg.R.k).N₁), hs.y_le_x]
  have hp₀0 : 0 ≤ scP0 x Dg.R.k * Real.log (scP0 x Dg.R.k) := by
    have h1 : 1 ≤ scP0 x Dg.R.k := le_trans (one_le_pow₀ hx1) hs.scP0_ge
    have := Real.log_nonneg h1
    positivity
  have hΛ : scP0 x Dg.R.k * Real.log (scP0 x Dg.R.k) ≤ 16 * x ^ 72 := by
    have h1 := hs.scP0_log_le
    have h2 := hs.scP0_le
    have h3 : 0 ≤ scP0 x Dg.R.k := le_trans (by positivity) hs.scP0_ge
    nlinarith
  have hX' := hs.X'_ge
  have hX'0 : 0 < scX' x ε := Real.exp_pos _
  have hb' : 0 ≤ scB' x ε := (scB'_pos ε hx0).le
  have hw : scW'' S x ε ≤ scB' x ε := by
    have h2 : (1 : ℝ) ≤ Fintype.card S.A := by exact_mod_cast Fintype.card_pos
    unfold scW''
    exact div_le_self hb' (by nlinarith [hs.x_ge])
  have hw0 : 0 ≤ scW'' S x ε := (scW''_pos S ε hx0).le
  have hδ := hs.δ_le
  have hδ0 : 0 ≤ scδ₁ x ε := Real.rpow_nonneg hx0.le _
  have hr0 : (0 : ℝ) ≤ (tilePar x ε Dg.R.k).r := Nat.cast_nonneg _
  have h1 : ((tilePar x ε Dg.R.k).r : ℝ) * scW'' S x ε + 80 * (tilePar x ε Dg.R.k).r * scδ₁ x ε * scB' x ε ≤
      81 * x * scB' x ε := by
    have a1 : ((tilePar x ε Dg.R.k).r : ℝ) * scW'' S x ε ≤ x * scB' x ε := by gcongr
    have a2 : 80 * ((tilePar x ε Dg.R.k).r : ℝ) * scδ₁ x ε * scB' x ε ≤ 80 * x * 1 * scB' x ε := by gcongr
    linarith
  have e : scB' x ε = scA x ε / scX' x ε := rfl
  calc 4 * Dg.R.m * Fintype.card S.A * ((tilePar x ε Dg.R.k).r * scW'' S x ε +
      80 * (tilePar x ε Dg.R.k).r * scδ₁ x ε * scB' x ε) * (scP0 x Dg.R.k * Real.log (scP0 x Dg.R.k)) ≤
      4 * (2 * x) * Fintype.card S.A * (81 * x * scB' x ε) * (16 * x ^ 72) := by gcongr
    _ = Fintype.card S.A * scA x ε * (10368 * x ^ 74 / scX' x ε) := by rw [e]; field_simp; ring
    _ ≤ Fintype.card S.A * scA x ε * (10368 * x ^ 74 / x ^ 410) := by
        gcongr
    _ ≤ _ := mul_le_div64 hAa (hs.frac_le_x (by norm_num) (by norm_num))

/-- **The class of the small and odd orders** (`TwoAdic`): `8ma·|TT|·3 ord κ·⌈x^{ε/4}⌉·log X(1 + log X)/(4|A|)`,
`X = X″ + 1`, is at most `1008y⁸·a ≤ |A|a/64` (`|A| ≥ y^{16}`). -/
theorem class_OS :
    8 * Dg.R.m * scA x ε * (Dg.TT.card * (3 * orderOf κ * (⌈x ^ (ε / 4)⌉₊ : ℝ) *
      (Real.log (S.cutX x ε + 1) * (1 + Real.log (S.cutX x ε + 1))) / (4 * Fintype.card S.A))) ≤
      Fintype.card S.A * scA x ε / 64 := by
  set y := x ^ (1 / 8 : ℝ) with hy
  have hx0 := hs.x_pos
  have hy1 : 1 ≤ y := hs.one_le_y
  have hm := hs.m_le
  have ha0 : 0 ≤ scA x ε := (scA_pos ε hx0).le
  have hA0 : (0 : ℝ) < Fintype.card S.A := Nat.cast_pos.2 Fintype.card_pos
  have hX1 := hs.one_le_cutX
  have hLX : Real.log (S.cutX x ε + 1) ≤ 6 * y :=
    (Real.log_le_log (by linarith) (by linarith)).trans hs.log_two_cutX_le
  have hLX0 : 0 ≤ Real.log (S.cutX x ε + 1) := Real.log_nonneg (by linarith)
  have hY : (⌈x ^ (ε / 4)⌉₊ : ℝ) ≤ 2 * y := by
    have := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le (ε / 4))
    linarith [hs.quarter_le]
  have ho : (orderOf κ : ℝ) ≤ y := hs.ord_le
  have hTA : (Dg.TT.card : ℝ) / Fintype.card S.A ≤ 1 := (div_le_one hA0).2 hs.TT_le
  calc 8 * Dg.R.m * scA x ε * (Dg.TT.card * (3 * orderOf κ * (⌈x ^ (ε / 4)⌉₊ : ℝ) *
      (Real.log (S.cutX x ε + 1) * (1 + Real.log (S.cutX x ε + 1))) / (4 * Fintype.card S.A))) =
      (Dg.TT.card / Fintype.card S.A) * (6 * Dg.R.m * orderOf κ * (⌈x ^ (ε / 4)⌉₊ : ℝ) *
        (Real.log (S.cutX x ε + 1) * (1 + Real.log (S.cutX x ε + 1)))) * scA x ε := by
        field_simp; ring
    _ ≤ 1 * (6 * (2 * y ^ 4) * y * (2 * y) * (6 * y * (1 + 6 * y))) * scA x ε := by gcongr
    _ ≤ 1 * (6 * (2 * y ^ 4) * y * (2 * y) * (6 * y * (7 * y))) * scA x ε := by gcongr; linarith
    _ = 1008 * y ^ 8 * scA x ε := by ring
    _ ≤ Fintype.card S.A * scA x ε / 64 := by
        have h1 : 64 * 1008 * y ^ 8 ≤ y ^ 16 := by
          have := hs.cy_le (c := 64 * 1008) (by norm_num) (show 8 + 1 ≤ 16 by norm_num)
          linarith
        have h2 := hs.A_ge
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 64)]
        nlinarith

/-- **The class of the band**: `8ma·|TT|·(8ρ_B + 1/p₀)·log 2X′ ≤ |A|a·460832y⁵/y⁸` (`ρ_B ≤ 1800/y⁸`, `p₀ ≥ y⁸`). -/
theorem class_B :
    8 * Dg.R.m * scA x ε * (Dg.TT.card * (8 * scRhoB S x ε Dg.R.k + 1 / scP0 x Dg.R.k) *
      Real.log (2 * scX' x ε)) ≤ Fintype.card S.A * scA x ε / 64 := by
  set y := x ^ (1 / 8 : ℝ) with hy
  have hx0 := hs.x_pos
  have hx1 : (1 : ℝ) ≤ x := by linarith [hs.x_ge]
  have hy1 : 1 ≤ y := hs.one_le_y
  have hy0 : 0 < y := by linarith
  have hm := hs.m_le
  have ha0 : 0 ≤ scA x ε := (scA_pos ε hx0).le
  have hAa : 0 ≤ (Fintype.card S.A : ℝ) * scA x ε := by positivity
  have hρ := hs.rhoB_le
  have hρ0 := hs.rhoB_nonneg
  have hp₀ : x ≤ scP0 x Dg.R.k := (le_self_pow₀ hx1 (by norm_num)).trans hs.scP0_ge
  have hp₀0 : 0 < scP0 x Dg.R.k := lt_of_lt_of_le hx0 hp₀
  have hy8 : y ^ 8 = x := hs.y_pow
  have hp : 1 / scP0 x Dg.R.k * y ^ 8 ≤ 1 := by
    rw [hy8, div_mul_eq_mul_div, one_mul, div_le_one hp₀0]; exact hp₀
  have hB : (8 * scRhoB S x ε Dg.R.k + 1 / scP0 x Dg.R.k) * y ^ 8 ≤ 14401 := by nlinarith
  have hB0 : 0 ≤ 8 * scRhoB S x ε Dg.R.k + 1 / scP0 x Dg.R.k := by positivity
  have hl : Real.log (2 * scX' x ε) ≤ 2 * y := by
    rw [scX', Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp]
    linarith [hs.L_le, Real.log_two_lt_d9]
  have hX'1 : 1 ≤ scX' x ε := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hl0 : 0 ≤ Real.log (2 * scX' x ε) := Real.log_nonneg (by linarith)
  calc 8 * Dg.R.m * scA x ε * (Dg.TT.card * (8 * scRhoB S x ε Dg.R.k + 1 / scP0 x Dg.R.k) *
      Real.log (2 * scX' x ε)) =
      Dg.TT.card * scA x ε * (8 * Dg.R.m * Real.log (2 * scX' x ε) *
        ((8 * scRhoB S x ε Dg.R.k + 1 / scP0 x Dg.R.k) * y ^ 8) / y ^ 8) := by
        field_simp
    _ ≤ Fintype.card S.A * scA x ε * (8 * (2 * y ^ 4) * (2 * y) * 14401 / y ^ 8) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hs.TT_le ha0) ?_ (by positivity) hAa
        gcongr
    _ = Fintype.card S.A * scA x ε * (460832 * y ^ 5 / y ^ 8) := by ring
    _ ≤ _ := mul_le_div64 hAa (hs.frac_le (by norm_num) (by norm_num))

/-- **The class of the bad tops** (G1): `8ma·|TT|·x^{−2+ε} ≤ |A|a·16y⁵/y^{16}`. -/
theorem class_G :
    8 * Dg.R.m * scA x ε * (Dg.TT.card * x ^ (-2 + ε)) ≤ Fintype.card S.A * scA x ε / 64 := by
  set y := x ^ (1 / 8 : ℝ) with hy
  have hx0 := hs.x_pos
  have hy1 : 1 ≤ y := hs.one_le_y
  have hy0 : 0 < y := by linarith
  have hm := hs.m_le
  have ha0 : 0 ≤ scA x ε := (scA_pos ε hx0).le
  have hAa : 0 ≤ (Fintype.card S.A : ℝ) * scA x ε := by positivity
  have h := hs.rpow_neg_le
  have h0 : 0 ≤ x ^ (-2 + ε) := Real.rpow_nonneg hx0.le _
  calc 8 * Dg.R.m * scA x ε * (Dg.TT.card * x ^ (-2 + ε)) =
      Dg.TT.card * scA x ε * (8 * Dg.R.m * (x ^ (-2 + ε) * y ^ 16) / y ^ 16) := by field_simp
    _ ≤ Fintype.card S.A * scA x ε * (8 * (2 * y ^ 4) * y / y ^ 16) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hs.TT_le ha0) ?_ (by positivity) hAa
        gcongr
    _ = Fintype.card S.A * scA x ε * (16 * y ^ 5 / y ^ 16) := by ring
    _ ≤ _ := mul_le_div64 hAa (hs.frac_le (by norm_num) (by norm_num))

/-- **The class beyond the cut-off**: `2m|TT|·(w″/x)·2X″ log 2X″ = 4m|TT|·a·log 2X″/x ≤ |A|a·48y⁵/y⁸`. -/
theorem class_beyond :
    2 * (Dg.R.m * Dg.TT.card * (scW'' S x ε / x)) * (2 * S.cutX x ε * Real.log (2 * S.cutX x ε)) ≤
      Fintype.card S.A * scA x ε / 64 := by
  set y := x ^ (1 / 8 : ℝ) with hy
  have hx0 := hs.x_pos
  have hy1 : 1 ≤ y := hs.one_le_y
  have hm := hs.m_le
  have ha0 : 0 ≤ scA x ε := (scA_pos ε hx0).le
  have hAa : 0 ≤ (Fintype.card S.A : ℝ) * scA x ε := by positivity
  have hl := hs.log_two_cutX_le
  have hl0 : 0 ≤ Real.log (2 * S.cutX x ε) := Real.log_nonneg (by linarith [hs.one_le_cutX])
  have e := cutX_mul_scW'' S ε hx0
  calc 2 * (Dg.R.m * Dg.TT.card * (scW'' S x ε / x)) * (2 * S.cutX x ε * Real.log (2 * S.cutX x ε)) =
      Dg.TT.card * (S.cutX x ε * scW'' S x ε) * (4 * Dg.R.m * Real.log (2 * S.cutX x ε) / x) := by ring
    _ = Dg.TT.card * scA x ε * (4 * Dg.R.m * Real.log (2 * S.cutX x ε) / x) := by rw [e]
    _ ≤ Fintype.card S.A * scA x ε * (48 * y ^ 5 / y ^ 8) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hs.TT_le ha0) ?_ (by positivity) hAa
        have hy8 : y ^ 8 = x := hs.y_pow
        rw [hy8]
        refine div_le_div_of_nonneg_right ?_ hx0.le
        calc 4 * (Dg.R.m : ℝ) * Real.log (2 * S.cutX x ε) ≤ 4 * (2 * y ^ 4) * (6 * y) := by gcongr
          _ = 48 * y ^ 5 := by ring
    _ ≤ _ := mul_le_div64 hAa (hs.frac_le (by norm_num) (by norm_num))

/-- **The class at `d`**: `m|TT|·(log⌈2a⌉ + log d)·2a/d ≤ |A|a/64`, as `log d ≤ d/(512x) + 512x` and
`d > 2^{12}x^{406}`. -/
theorem class_d :
    Dg.R.m * Dg.TT.card * ((Real.log ⌈2 * scA x ε⌉₊ + Real.log S.d) * (2 * scA x ε / S.d)) ≤
      Fintype.card S.A * scA x ε / 64 := by
  have hx0 := hs.x_pos
  have hx := hs.x_ge
  have hm := hs.m_le_x
  have ha0 : 0 ≤ scA x ε := (scA_pos ε hx0).le
  have hAa : 0 ≤ (Fintype.card S.A : ℝ) * scA x ε := by positivity
  have hd := hs.d_gt
  have hd0 : 0 < (S.d : ℝ) := lt_of_lt_of_le (by positivity) hd.le
  have hlc : Real.log ⌈2 * scA x ε⌉₊ ≤ 3 * x := by linarith [hs.log_ceil_le, hs.y_le_x]
  have hlc0 : 0 ≤ Real.log ⌈2 * scA x ε⌉₊ := Real.log_natCast_nonneg _
  have hld0 : 0 ≤ Real.log S.d := Real.log_natCast_nonneg _
  have hlogd : Real.log S.d ≤ S.d / (512 * x) + 512 * x := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < 512 * x by positivity)
    have h2 := Real.log_le_sub_one_of_pos (show 0 < (S.d : ℝ) / (512 * x) by positivity)
    have h3 : Real.log S.d = Real.log (512 * x) + Real.log (S.d / (512 * x)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    linarith
  have hkey : 128 * Dg.R.m * (Real.log ⌈2 * scA x ε⌉₊ + Real.log S.d) ≤ S.d := by
    have h1 : 128 * (Dg.R.m : ℝ) * (Real.log ⌈2 * scA x ε⌉₊ + Real.log S.d) ≤
        128 * (2 * x) * (3 * x + (S.d / (512 * x) + 512 * x)) := by gcongr
    have h2 : 128 * (2 * x) * (3 * x + (S.d / (512 * x) + 512 * x)) = S.d / 2 + 131840 * x ^ 2 := by
      field_simp; ring
    have h3 : 263680 * x ^ 2 ≤ 2 ^ 12 * x ^ 406 := by
      have : 263680 * x ^ 2 ≤ x ^ 406 := mul_pow_le_pow (by linarith) (k := 2) (const_le_sq hx (by norm_num))
        (by norm_num)
      nlinarith [pow_pos hx0 406]
    linarith
  calc Dg.R.m * Dg.TT.card * ((Real.log ⌈2 * scA x ε⌉₊ + Real.log S.d) * (2 * scA x ε / S.d)) =
      Dg.TT.card * scA x ε * (2 * Dg.R.m * (Real.log ⌈2 * scA x ε⌉₊ + Real.log S.d) / S.d) := by ring
    _ ≤ Fintype.card S.A * scA x ε * (1 / 64) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hs.TT_le ha0) ?_ (by positivity) hAa
        rw [div_le_iff₀ hd0]
        linarith
    _ = _ := by ring

/-- `ρ_B ≤ 1/2`. -/
theorem rhoB_le_half : scRhoB S x ε Dg.R.k ≤ 1 / 2 := by
  have h := hs.rhoB_le
  have h0 := hs.rhoB_nonneg
  have hy : 3600 ≤ (x ^ (1 / 8 : ℝ)) ^ 8 := by
    have := hs.cy_le (c := 3600) (by norm_num) (show 0 + 1 ≤ 8 by norm_num)
    rw [pow_zero, mul_one] at this; exact this
  nlinarith

/-- `p₀ ≥ e`. -/
theorem exp_one_le_scP0 : Real.exp 1 ≤ scP0 x Dg.R.k := by
  have hx1 : (1 : ℝ) ≤ x := by linarith [hs.x_ge]
  have h1 : x ≤ x ^ 26 := le_self_pow₀ hx1 (by norm_num)
  linarith [Real.exp_one_lt_d9, hs.scP0_ge, hs.x_ge]

end LossSizes

/-! ## The losses -/

/-- **The losses** (M-G7c, Step D): the frontier's asks, in the gain's (twisted) coordinates, less the gains net of
the depths over the inert and signal `p ≤ X″`, are at most `c_G/4`. By `losses_eq`, the left side is the sum over
the inert and signal `p ≤ X″` of `2 log p·(asks − gain)` (at most `2 log p·m·(|TT|·slack₁ + slack₂)` plus `4a/p` per
lift and uncovered top, `loss_at_le`), plus the asks beyond `X″` and at `d`. The slacks (`sum_slack_le`), the
uncovered tops (`sum_uncov_le`, with `TwoAdic` for the small and odd orders, the band sum, and G1 for the bad tops),
and the asks beyond `X″` and at `d` make fourteen classes, each at most `|A|·a/64`, and `c_G ≥ |A|·a`. True for
every `κ`; the hypotheses beyond `Adm` and `FamAt` are G1 (`FewBadTops`), `TwoAdic` and the growth package
`GainBig`. -/
theorem losses_le (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) {e : ℕ} (h2 : S.TwoAdic κ e)
    (hG1 : Dg.FewBadTops) (hB : GainBig ε x) (u : S.A) :
    (∑ t ∈ Dg.TT, ∑ J, ((∑ p ∈ S.askSupp x ε, 2 * Real.log p * Dg.askE u J p t) +
        Real.log S.d * Dg.askAtD u J t)) -
      ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε),
        2 * Real.log p * (∑ J, Dg.gainG pr u J p - Dg.tau pr p) ≤ S.cGform x ε / 4 := by
  have hs := lossSizes hA hB
  have hx0 := hs.x_pos
  have ha0 : 0 ≤ scA x ε := (scA_pos ε hx0).le
  have hm0 : (0 : ℝ) ≤ Dg.R.m := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) ≤ Dg.TT.card := Nat.cast_nonneg _
  rw [Dg.losses_eq hA pr u]
  -- the inert and signal primes: slacks and uncovered tops
  have hT1 : ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε), 2 * Real.log p *
      (∑ J, ∑ t ∈ Dg.TT, Dg.askE u J p t - (∑ J, Dg.gainG pr u J p - Dg.tau pr p)) ≤
      ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε),
        2 * Real.log p * (Dg.R.m * (Dg.TT.card * Dg.slack1 p + Dg.slack2 p)) +
      8 * Dg.R.m * scA x ε * ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε),
        Real.log p / p * ((Dg.TT \ Dg.coveredTops p).card : ℝ) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun p hp => ?_
    have hp2 : 2 ≤ p := (mem_filter.1 hp).2.1.two_le
    have hl : 0 ≤ 2 * Real.log p := by have := Real.log_natCast_nonneg p; linarith
    have h := mul_le_mul_of_nonneg_left (loss_at_le hA hF u hp2) hl
    have hp0 : (p : ℝ) ≠ 0 := by have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
                                 linarith
    calc _ ≤ _ := h
      _ = _ := by field_simp; ring
  have hS := sum_slack_le hs
  have hU := Dg.sum_uncov_le hx0.le hs.rhoB_nonneg hs.rhoB_le_half hs.exp_one_le_scP0
  have hU8 := mul_le_mul_of_nonneg_left hU (by positivity : (0 : ℝ) ≤ 8 * Dg.R.m * scA x ε)
  have hOS := h2.sum_log_div_le (y := ⌈x ^ (ε / 4)⌉₊) (Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2
    (Real.rpow_pos_of_pos hx0 _)).ne') (X := S.cutX x ε + 1) (by linarith [hs.one_le_cutX])
  have hOS8 := mul_le_mul_of_nonneg_left hOS (by positivity : (0 : ℝ) ≤ 8 * Dg.R.m * scA x ε * Dg.TT.card)
  have hG8 := mul_le_mul_of_nonneg_left hG1 (by positivity : (0 : ℝ) ≤ 8 * Dg.R.m * scA x ε)
  -- beyond `X″` and at `d`
  have hT2 := sum_beyond_le hA hF hs u
  have hT3 := sum_atD_le hA hF u
  -- the fourteen classes
  have hN1 : ((tilePar x ε Dg.R.k).N₁ : ℝ) ≤ x ^ (1 / 8 : ℝ) := by
    linarith [hs.N₁r_le, (Nat.cast_nonneg _ : (0 : ℝ) ≤ (tilePar x ε Dg.R.k).r)]
  have hr : ((tilePar x ε Dg.R.k).r : ℝ) ≤ x ^ (1 / 8 : ℝ) := by
    linarith [hs.N₁r_le, (Nat.cast_nonneg _ : (0 : ℝ) ≤ (tilePar x ε Dg.R.k).N₁)]
  have k1 : (Kg.cκ₁ : ℝ) = 100 := by norm_num [Kg]
  have k2 : (Kg.ct : ℝ) = 100 := by norm_num [Kg]
  have c1 := hs.class_poly
  have c2 := hs.class_bx
  have c3 := hs.class_ap2
  have c4 := hs.class_La (c := Kg.cκ₁ * (tilePar x ε Dg.R.k).N₁) (by positivity) (by rw [k1]; gcongr)
  have c5 := hs.class_w
  have c6 := hs.class_b2
  have c7 := hs.class_aY
  have c8 := hs.class_w2
  have c9 := hs.class_La (c := Kg.ct * (tilePar x ε Dg.R.k).r) (by positivity) (by rw [k2]; gcongr)
  have c10 := hs.class_OS
  have c11 := hs.class_B
  have c12 := hs.class_G
  have c13 := hs.class_beyond
  have c14 := hs.class_d
  have hfin : 14 * (Fintype.card S.A * scA x ε / 64) ≤ S.cGform x ε / 4 := by
    have := hs.cG_ge
    have : 0 ≤ (Fintype.card S.A : ℝ) * scA x ε := by positivity
    linarith
  linear_combination hT1 + hS + hU8 + hOS8 + hG8 + hT2 + hT3 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 +
    c10 + c11 + c12 + c13 + c14 + hfin


end SharpDesign

end

end ZetaBalance
