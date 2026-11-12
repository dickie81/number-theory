/-
# The two comparisons at a floor for a family of tuples of distinct primes, on bounds for its products

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdFillCore.lean` evaluates the terms at a floor of a box from a few sums of the ends of
its cells; `SieveAdFamSet.lean` evaluates those of a family of tuples of distinct primes, in any order, when its
boxes of cells of side `1/DEN` are. Together: a family cut out by atoms whose tuples have a few products, over
fixed sets of their indices, between fixed powers of `x` is evaluated when the exponents pass the checks with
`Kb ≥ K` cells of room, `K` the number of primes.

* `pre σ S`: the indices that a permutation sends into `S` (`mem_pre`, `sum_pre`, `pre_compl`).
* `SumsOK bx f S₀ Sr S₁ ρ₁ ρ₂ c0lo c0hi h1s h2s`: the box has `f ≤ lo ≤ hi ≤ DEN` and the six bounds on its sums
  that the two comparisons read. `sumsOK_perm`: it passes to `bx ∘ σ` with the sets `pre σ ·`. `sumsOK_ucell`:
  it holds, with `Kb ≥ K` cells of room, for the cells of side `1/DEN` of a tuple with entries in
  `[x^{f/DEN}, x)` and the products in their ranges.
* `evJ_fam_fill`: **the comparison with the rest among the tree's primes, for a family of tuples of distinct
  primes.** `evJ_fam_two`: **the comparison with the rest among the tuple's primes.** `evJ_fam_fill_at`,
  `evJ_fam_two_at`: with the route and its exponent as variables.

The file imports `SieveAdFillCore.lean` and `SieveAdFamSet.lean`.
-/
import SieveAdFillCore
import SieveAdFamSet

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN DEN_pos')

/-! ### Sets of indices under a permutation -/

/-- The indices that a permutation sends into a set. -/
def pre {k : ℕ} (σ : Equiv.Perm (Fin k)) (S : Finset (Fin k)) : Finset (Fin k) := S.map σ.symm.toEmbedding

theorem mem_pre {k : ℕ} (σ : Equiv.Perm (Fin k)) (S : Finset (Fin k)) (i : Fin k) : i ∈ pre σ S ↔ σ i ∈ S := by
  unfold pre
  rw [Finset.mem_map]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa using hj
  · intro h
    exact ⟨σ i, h, by simp⟩

theorem sum_pre {k : ℕ} (σ : Equiv.Perm (Fin k)) (S : Finset (Fin k)) (g : Fin k → ℕ) :
    ∑ i ∈ pre σ S, g (σ i) = ∑ j ∈ S, g j := by
  unfold pre
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

theorem pre_compl {k : ℕ} (σ : Equiv.Perm (Fin k)) (S : Finset (Fin k)) : (pre σ S)ᶜ = pre σ Sᶜ := by
  ext i
  simp only [Finset.mem_compl, mem_pre]

/-! ### The sums that the comparisons read -/

/-- The box has `f ≤ lo ≤ hi ≤ DEN`, and its sums are bounded as the two comparisons at a floor ask: `ρ₁` at most
the sum of the lower ends over `Sr` and `ρ₂` at least that of the upper ends, `c0lo` and `c0hi` the same over `S₀`,
`h1s` at least the sum of the upper ends over `S₁` and `h2s` at least that over the other indices. -/
def SumsOK {k : ℕ} (bx : Fin k → Cell) (f : ℕ) (S₀ Sr S₁ : Finset (Fin k)) (ρ₁ ρ₂ c0lo c0hi h1s h2s : ℕ) : Prop :=
  (∀ i, f ≤ (bx i).1 ∧ (bx i).1 ≤ (bx i).2 ∧ (bx i).2 ≤ DEN) ∧
    ρ₁ ≤ ∑ i ∈ Sr, (bx i).1 ∧ ∑ i ∈ Sr, (bx i).2 ≤ ρ₂ ∧ c0lo ≤ ∑ i ∈ S₀, (bx i).1 ∧ ∑ i ∈ S₀, (bx i).2 ≤ c0hi ∧
      ∑ i ∈ S₁, (bx i).2 ≤ h1s ∧ ∑ i ∈ S₁ᶜ, (bx i).2 ≤ h2s

/-- The bounds pass to the box in another order, with the sets of indices carried along. -/
theorem sumsOK_perm {k : ℕ} {bx : Fin k → Cell} {f : ℕ} {S₀ Sr S₁ : Finset (Fin k)}
    {ρ₁ ρ₂ c0lo c0hi h1s h2s : ℕ} (σ : Equiv.Perm (Fin k)) (h : SumsOK bx f S₀ Sr S₁ ρ₁ ρ₂ c0lo c0hi h1s h2s) :
    SumsOK (bx ∘ σ) f (pre σ S₀) (pre σ Sr) (pre σ S₁) ρ₁ ρ₂ c0lo c0hi h1s h2s := by
  obtain ⟨hc, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun i => hc (σ i), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h1.trans (sum_pre σ Sr fun j => (bx j).1).ge
  · exact (sum_pre σ Sr fun j => (bx j).2).le.trans h2
  · exact h3.trans (sum_pre σ S₀ fun j => (bx j).1).ge
  · exact (sum_pre σ S₀ fun j => (bx j).2).le.trans h4
  · exact (sum_pre σ S₁ fun j => (bx j).2).le.trans h5
  · rw [pre_compl]
    exact (sum_pre σ S₁ᶜ fun j => (bx j).2).le.trans h6

variable [Route]

/-- **The bounds hold for the cells of side `1/DEN` of a tuple, with `K` cells of room.** For `x > 1` and a tuple
with entries in `[x^{f/DEN}, x)`, `f ≤ DEN`: if its products over `Sr`, `S₀` lie in `[x^{ρlo/DEN}, x^{ρhi/DEN}]`
and `[x^{lo₀/DEN}, x^{hi₀/DEN}]` and those over `S₁` and over the other indices are at most `x^{hi₁/DEN}` and
`x^{hi₂/DEN}`, the box of its cells has the bounds `ρlo − K`, `ρhi + K`, `lo₀ − K`, `hi₀ + K`, `hi₁ + K`,
`hi₂ + K`. -/
theorem sumsOK_ucell {q : ℕ} (hx1 : 1 < xq q) {K : ℕ} {w : Fin K → ℕ} {f : ℕ} (hfD : f ≤ DEN)
    (hw : ∀ i, Xe q f ≤ w i ∧ (w i : ℝ) < Xe q DEN) (S₀ Sr S₁ : Finset (Fin K)) {Kb : ℕ} (hKb : K ≤ Kb)
    {ρlo ρhi lo₀ hi₀ hi₁ hi₂ : ℕ}
    (hr1 : Xe q ρlo ≤ ∏ i ∈ Sr, (w i : ℝ)) (hr2 : ∏ i ∈ Sr, (w i : ℝ) ≤ Xe q ρhi)
    (h01 : Xe q lo₀ ≤ ∏ i ∈ S₀, (w i : ℝ)) (h02 : ∏ i ∈ S₀, (w i : ℝ) ≤ Xe q hi₀)
    (h1 : ∏ i ∈ S₁, (w i : ℝ) ≤ Xe q hi₁) (h2 : ∏ i ∈ S₁ᶜ, (w i : ℝ) ≤ Xe q hi₂) :
    SumsOK (ubox fun i => ucell q (w i)) f S₀ Sr S₁ (ρlo - Kb) (ρhi + Kb) (lo₀ - Kb) (hi₀ + Kb) (hi₁ + Kb)
      (hi₂ + Kb) := by
  have hx0 : 0 < xq q := by linarith
  have hw1 : ∀ i, 1 ≤ w i ∧ (w i : ℝ) < Xe q DEN := by
    intro i
    refine ⟨?_, (hw i).2⟩
    have h : (0 : ℝ) < w i := lt_of_lt_of_le (Xe_pos hx0 f) (hw i).1
    have h' : 0 < w i := by exact_mod_cast h
    exact h'
  have hcard : ∀ S : Finset (Fin K), S.card ≤ K := fun S => by
    have := Finset.card_le_univ S
    rwa [Fintype.card_fin] at this
  have hup : ∀ S : Finset (Fin K), ∑ i ∈ S, ((ubox fun i => ucell q (w i)) i).2 = ∑ i ∈ S, ucell q (w i) + S.card := by
    intro S
    show ∑ i ∈ S, (ucell q (w i) + 1) = _
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have hlo : ∀ S : Finset (Fin K), ∑ i ∈ S, ((ubox fun i => ucell q (w i)) i).1 = ∑ i ∈ S, ucell q (w i) :=
    fun S => rfl
  have hge : ∀ (S : Finset (Fin K)) (lo : ℕ), Xe q lo ≤ ∏ i ∈ S, (w i : ℝ) → lo - Kb ≤ ∑ i ∈ S, ucell q (w i) := by
    intro S lo h
    have h' := le_ucell_sum hx1 S (fun i _ => hw1 i) h
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at h'
    have := hcard S
    omega
  have hle : ∀ (S : Finset (Fin K)) (hi : ℕ), ∏ i ∈ S, (w i : ℝ) ≤ Xe q hi →
      ∑ i ∈ S, ucell q (w i) + S.card ≤ hi + Kb := by
    intro S hi h
    have h' := ucell_sum_le hx1 S (fun i _ => hw1 i) h
    have := hcard S
    omega
  refine ⟨fun i => ⟨le_ucell hfD (hw i).1, Nat.le_succ _, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ucell_spec (hw1 i).1 (hw1 i).2).2.2
  · rw [hlo]
    exact hge Sr ρlo hr1
  · rw [hup]
    exact hle Sr ρhi hr2
  · rw [hlo]
    exact hge S₀ lo₀ h01
  · rw [hup]
    exact hle S₀ hi₀ h02
  · rw [hup]
    exact hle S₁ hi₁ h1
  · rw [hup]
    exact hle S₁ᶜ hi₂ h2

variable [RouteOK] [SieveCert.IBPar] [IBFits]

/-! ### The two comparisons for a family -/

/-- **The comparison with the rest among the tree's primes, for a family of tuples of distinct primes.** Let
`E q` be at most `m` atoms on `K` indices with thresholds as in `ThrOK`, `S₀` and `S₁` sets of indices, and suppose
that at a large modulus every injective tuple of the family has its entries in `[x^{f/DEN}, x)`, its product over
`S₀` in `[x^{lo₀/DEN}, x^{hi₀/DEN}]` and its products over `S₁` and over the other indices at most `x^{hi₁/DEN}`
and `x^{hi₂/DEN}`. If the exponents pass `coreJ3` at the floor `f ≤ DEN` with `Kb ≥ K` cells of room, the terms
at the floor `x^{f/DEN}` of the injective tuples of the family, in `𝒜` minus the comparison set, are evaluated. -/
theorem evJ_fam_fill {K : ℕ} (f : ℕ) (hfD : f ≤ DEN) (S₀ S₁ : Finset (Fin K)) (e : Bool)
    (u v t r1 r2 lo₀ hi₀ hi₁ hi₂ Kb : ℕ) (hKb : K ≤ Kb)
    (hok : coreJ3 f e u v t r1 r2 (lo₀ - Kb) (hi₀ + Kb) (hi₁ + Kb) (hi₂ + Kb) = true) {m : ℕ}
    (E : ℕ → List (Atom K)) (hEl : ∀ q, (E q).length ≤ m) (hEt : ∀ᶠ q : ℕ in atTop, ThrOK q (E q))
    (hfam : ∀ᶠ q : ℕ in atTop, ∀ w ∈ famSet K (N2 q) (E q), Function.Injective w →
      (∀ i, Xe q f ≤ w i ∧ (w i : ℝ) < Xe q DEN) ∧ Xe q lo₀ ≤ ∏ i ∈ S₀, (w i : ℝ) ∧
        ∏ i ∈ S₀, (w i : ℝ) ≤ Xe q hi₀ ∧ ∏ i ∈ S₁, (w i : ℝ) ≤ Xe q hi₁ ∧ ∏ i ∈ S₁ᶜ, (w i : ℝ) ≤ Xe q hi₂) :
    ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
      |famJ (gA q a) (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊
          ((famSet K (N2 q) (E q)).filter Function.Injective) -
        famJ (gB q) (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊
          ((famSet K (N2 q) (E q)).filter Function.Injective)| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q) := by
  refine evJ_famSet f (m := m)
    (fun bx => ∃ S₀' Sr' S₁' : Finset (Fin K),
      SumsOK bx f S₀' Sr' S₁' (0 - Kb) (0 + Kb) (lo₀ - Kb) (hi₀ + Kb) (hi₁ + Kb) (hi₂ + Kb)) ?_ E hEl hEt ?_
  · rintro bx ⟨S₀', Sr', S₁', hc, -, -, h3, h4, h5, h6⟩
    exact evJ_fill_core bx f S₀' S₁' e u v t r1 r2 _ _ _ _ hok hc h3 h4 h5 h6 (le_refl (3 * K + m))
  · filter_upwards [hfam, big_ev] with q hq hbig w hw hinj
    obtain ⟨-, hx3, -⟩ := big_facts hbig
    obtain ⟨hwc, h01, h02, h1, h2⟩ := hq w hw hinj
    refine ⟨fun i => (hwc i).2, fun σ _ => ?_⟩
    have hs := sumsOK_ucell (by linarith) hfD hwc S₀ ∅ S₁ hKb (ρlo := 0) (ρhi := 0)
      (by rw [Finset.prod_empty, Xe_zero]) (by rw [Finset.prod_empty, Xe_zero]) h01 h02 h1 h2
    exact ⟨_, _, _, sumsOK_perm σ hs⟩

/-- **The comparison with the rest among the tuple's primes, for a family of tuples of distinct primes.** As
`evJ_fam_fill`, with a set `Sr` of indices for the rest, disjoint from `S₀`, whose product lies in
`[x^{ρlo/DEN}, x^{ρhi/DEN}]`, `ρlo > 0`, and the checks `coreJ2`. -/
theorem evJ_fam_two {K : ℕ} (f : ℕ) (hfD : f ≤ DEN) (S₀ Sr S₁ : Finset (Fin K)) (hdisj : Disjoint S₀ Sr)
    (e : Bool) (u v t ρlo ρhi lo₀ hi₀ hi₁ hi₂ Kb : ℕ) (hKb : K ≤ Kb) (hρ : 0 < ρlo)
    (hok : coreJ2 f e u v t (ρlo - Kb) (ρhi + Kb) (lo₀ - Kb) (hi₀ + Kb) (hi₁ + Kb) (hi₂ + Kb) = true) {m : ℕ}
    (E : ℕ → List (Atom K)) (hEl : ∀ q, (E q).length ≤ m) (hEt : ∀ᶠ q : ℕ in atTop, ThrOK q (E q))
    (hfam : ∀ᶠ q : ℕ in atTop, ∀ w ∈ famSet K (N2 q) (E q), Function.Injective w →
      (∀ i, Xe q f ≤ w i ∧ (w i : ℝ) < Xe q DEN) ∧ Xe q ρlo ≤ ∏ i ∈ Sr, (w i : ℝ) ∧
        ∏ i ∈ Sr, (w i : ℝ) ≤ Xe q ρhi ∧ Xe q lo₀ ≤ ∏ i ∈ S₀, (w i : ℝ) ∧
        ∏ i ∈ S₀, (w i : ℝ) ≤ Xe q hi₀ ∧ ∏ i ∈ S₁, (w i : ℝ) ≤ Xe q hi₁ ∧ ∏ i ∈ S₁ᶜ, (w i : ℝ) ≤ Xe q hi₂) :
    ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
      |famJ (gA q a) (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊
          ((famSet K (N2 q) (E q)).filter Function.Injective) -
        famJ (gB q) (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊
          ((famSet K (N2 q) (E q)).filter Function.Injective)| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q) := by
  refine evJ_famSet f (m := m)
    (fun bx => ∃ S₀' Sr' S₁' : Finset (Fin K), Disjoint S₀' Sr' ∧ Sr'.Nonempty ∧
      SumsOK bx f S₀' Sr' S₁' (ρlo - Kb) (ρhi + Kb) (lo₀ - Kb) (hi₀ + Kb) (hi₁ + Kb) (hi₂ + Kb)) ?_ E hEl hEt ?_
  · rintro bx ⟨S₀', Sr', S₁', hd, hne, hc, h1, h2, h3, h4, h5, h6⟩
    exact evJ_two_core bx f S₀' Sr' S₁' hd hne e u v t _ _ _ _ _ _ hok hc h1 h2 h3 h4 h5 h6
      (le_refl (3 * K + m))
  · filter_upwards [hfam, big_ev] with q hq hbig w hw hinj
    obtain ⟨-, hx3, -⟩ := big_facts hbig
    obtain ⟨hwc, hr1, hr2, h01, h02, h1, h2⟩ := hq w hw hinj
    refine ⟨fun i => (hwc i).2, fun σ _ => ?_⟩
    have hs := sumsOK_ucell (by linarith) hfD hwc S₀ Sr S₁ hKb hr1 hr2 h01 h02 h1 h2
    have hSr : Sr.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      rw [h0, Finset.prod_empty, ← Xe_zero q, Xe_le_iff (by linarith)] at hr1
      omega
    refine ⟨_, _, _, ?_, ?_, sumsOK_perm σ hs⟩
    · unfold pre
      exact (Finset.disjoint_map _).2 hdisj
    · unfold pre
      exact hSr.map

omit [Route] [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- **The comparison with the rest among the tree's primes, for a family of tuples of distinct primes, for any
route**: `evJ_fam_fill` with the route and its exponent as variables. -/
theorem evJ_fam_fill_at (Rt : Route) (hRt : @RouteOK Rt) (Pr : SieveCert.IBPar) (hPr : @IBFits Rt Pr) {K : ℕ}
    (f : ℕ) (hfD : f ≤ DEN) (S₀ S₁ : Finset (Fin K)) (e : Bool) (u v t r1 r2 lo₀ hi₀ hi₁ hi₂ Kb : ℕ)
    (hKb : K ≤ Kb) (hok : @coreJ3 Pr f e u v t r1 r2 (lo₀ - Kb) (hi₀ + Kb) (hi₁ + Kb) (hi₂ + Kb) = true) {m : ℕ}
    (E : ℕ → List (Atom K)) (hEl : ∀ q, (E q).length ≤ m) (hEt : ∀ᶠ q : ℕ in atTop, @ThrOK Rt q K (E q))
    (hfam : ∀ᶠ q : ℕ in atTop, ∀ w ∈ famSet K (@N2 Rt q) (E q), Function.Injective w →
      (∀ i, @Xe Rt q f ≤ w i ∧ (w i : ℝ) < @Xe Rt q DEN) ∧ @Xe Rt q lo₀ ≤ ∏ i ∈ S₀, (w i : ℝ) ∧
        ∏ i ∈ S₀, (w i : ℝ) ≤ @Xe Rt q hi₀ ∧ ∏ i ∈ S₁, (w i : ℝ) ≤ @Xe Rt q hi₁ ∧
        ∏ i ∈ S₁ᶜ, (w i : ℝ) ≤ @Xe Rt q hi₂) :
    ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
      |famJ (gA q a) (@N1 Rt q) (@N2 Rt q) ⌈@xq Rt q ^ ((f : ℝ) / DEN)⌉₊
          ((famSet K (@N2 Rt q) (E q)).filter Function.Injective) -
        famJ (gB q) (@N1 Rt q) (@N2 Rt q) ⌈@xq Rt q ^ ((f : ℝ) / DEN)⌉₊
          ((famSet K (@N2 Rt q) (E q)).filter Function.Injective)| ≤ (q.totient : ℝ)⁻¹ * (η * @Xq Rt q) :=
  @evJ_fam_fill Rt hRt Pr hPr K f hfD S₀ S₁ e u v t r1 r2 lo₀ hi₀ hi₁ hi₂ Kb hKb hok m E hEl hEt hfam

omit [Route] [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- **The comparison with the rest among the tuple's primes, for a family of tuples of distinct primes, for any
route**: `evJ_fam_two` with the route and its exponent as variables. -/
theorem evJ_fam_two_at (Rt : Route) (hRt : @RouteOK Rt) (Pr : SieveCert.IBPar) (hPr : @IBFits Rt Pr) {K : ℕ}
    (f : ℕ) (hfD : f ≤ DEN) (S₀ Sr S₁ : Finset (Fin K)) (hdisj : Disjoint S₀ Sr) (e : Bool)
    (u v t ρlo ρhi lo₀ hi₀ hi₁ hi₂ Kb : ℕ) (hKb : K ≤ Kb) (hρ : 0 < ρlo)
    (hok : @coreJ2 Pr f e u v t (ρlo - Kb) (ρhi + Kb) (lo₀ - Kb) (hi₀ + Kb) (hi₁ + Kb) (hi₂ + Kb) = true)
    {m : ℕ}
    (E : ℕ → List (Atom K)) (hEl : ∀ q, (E q).length ≤ m) (hEt : ∀ᶠ q : ℕ in atTop, @ThrOK Rt q K (E q))
    (hfam : ∀ᶠ q : ℕ in atTop, ∀ w ∈ famSet K (@N2 Rt q) (E q), Function.Injective w →
      (∀ i, @Xe Rt q f ≤ w i ∧ (w i : ℝ) < @Xe Rt q DEN) ∧ @Xe Rt q ρlo ≤ ∏ i ∈ Sr, (w i : ℝ) ∧
        ∏ i ∈ Sr, (w i : ℝ) ≤ @Xe Rt q ρhi ∧ @Xe Rt q lo₀ ≤ ∏ i ∈ S₀, (w i : ℝ) ∧
        ∏ i ∈ S₀, (w i : ℝ) ≤ @Xe Rt q hi₀ ∧ ∏ i ∈ S₁, (w i : ℝ) ≤ @Xe Rt q hi₁ ∧
        ∏ i ∈ S₁ᶜ, (w i : ℝ) ≤ @Xe Rt q hi₂) :
    ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
      |famJ (gA q a) (@N1 Rt q) (@N2 Rt q) ⌈@xq Rt q ^ ((f : ℝ) / DEN)⌉₊
          ((famSet K (@N2 Rt q) (E q)).filter Function.Injective) -
        famJ (gB q) (@N1 Rt q) (@N2 Rt q) ⌈@xq Rt q ^ ((f : ℝ) / DEN)⌉₊
          ((famSet K (@N2 Rt q) (E q)).filter Function.Injective)| ≤ (q.totient : ℝ)⁻¹ * (η * @Xq Rt q) :=
  @evJ_fam_two Rt hRt Pr hPr K f hfD S₀ Sr S₁ hdisj e u v t ρlo ρhi lo₀ hi₀ hi₁ hi₂ Kb hKb hρ hok m E hEl hEt
    hfam

end SieveAd

#print axioms SieveAd.evJ_fam_fill_at
#print axioms SieveAd.evJ_fam_two_at
