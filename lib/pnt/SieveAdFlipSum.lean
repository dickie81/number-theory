/-
# Role reversal through the largest prime, as an identity: the weights and the bound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdFlip.lean` puts the term of a box `(p₁, a)`, the cell of `p₁` being `ctx = (l₁, h₁)`,
between the terms at a level `Z = ⌈x^{t/DEN}⌉` over two frozen parts. Here:

* `ShareLe bx B`: the share of a box, the sum over its tuples of the rough numbers `Ψ(x/∏rt, rt_last)`, is at most
  `(B + o(1))x/log x`. `shareLe_of_box`: for `B` at least the bound of `SieveRough.shareBox`, as the cost of a
  dropped box is.
* `card_primes_le_famJR`: the primes of `(x/R, 2x/R]` are among the `n/R` of the terms at a level `Z` below them.
* `froz_weight_le`: **the weight of the narrower frozen part is at most `h₁/DEN` times the share of the box**: each
  `R` carries at least `(1 − ε)(DEN/h₁)(x/R)/log x` primes `P` of `(x/R, 2x/R]`, and the `n = RP` are counted by
  the box (`flip_inject`), at most its share.
* `sum_frozS_split`: a sum over a frozen part is the sum over the two parts that a cut of the range of `R` makes.
* `famJR_gB_zero_le`, `froz_ends_le`: for a frozen part in the range of `r'`, the terms at the level `Z` in the
  comparison set are at most `((bd + ε)·Σ 1/R)x/(φ(q) log x)`, `bd` the bound of `SieveAd.psi_level` for the rough
  numbers of `(x/R, 2x/R]`.
* `froz_top_le`, `froz_top_ge`: what a tree over a frozen part gives at its top: from the terms at a floor
  evaluated and a bound for the chain of one prime between the floor and the level, the terms at the level in `𝒜`
  minus the comparison set are at most, or at least minus, `(C·Σ 1/R + o(1))x/(φ(q) log x)`.
* `bd_flip_neg`, `bd_flip_pos`: **the reversal bounds the term of the box**, for a term that needs an upper bound
  and for one that needs a lower bound: with weights `w₀`, `w₁`, `w₂` of the narrower frozen part and of the `R`
  within `x^{1/DEN}` of the two ends, a tree of cost `C` over the wider (or the narrower) frozen part gives
  `Bd false (C(w₀ + w₁ + w₂) + bd(w₁ + w₂))` (or `Bd true (C w₀ + bd(w₁ + w₂))`).

The file imports `SieveAdFlip.lean`.
-/
import SieveAdFlip

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K omKw cdiv trB exB DEN_pos' K_pos')

variable [Route]

/-! ### The share of a box -/

/-- The share of a box is at most `B`: the sum over its tuples of the rough numbers `Ψ(x/∏rt, rt_last)` is at
most `(B + δ)x/log x` at a large modulus, for every `δ > 0`. -/
def ShareLe {k' : ℕ} (bx : Fin (k' + 1) → Cell) (B : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ q : ℕ in atTop,
    ∑ rt ∈ famB q bx, (Psi (xq q / (∏ i, rt i : ℕ)) (rt (Fin.last k')) : ℝ) ≤ (B + δ) * Xq q

/-- **The share of a box that may be dropped.** For a box whose cells have `0 < lo ≤ hi` and whose upper ends sum
to at most `DEN`, and `B` at least the bound of `SieveRough.shareBox`. -/
theorem shareLe_of_box [RouteOK] {m : ℕ} (bx : Fin (m + 1) → Cell) (hlo : ∀ i, 0 < (bx i).1)
    (hle : ∀ i, (bx i).1 ≤ (bx i).2) (hfit : ∑ i, (bx i).2 ≤ DEN) {B : ℝ}
    (hB : (omKw (∑ t : Fin m, (bx t.castSucc).1) (bx (Fin.last m)).1 (∑ i, ((bx i).2 - (bx i).1))
        ((bx (Fin.last m)).2 - (bx (Fin.last m)).1) : ℝ) / K *
      ((∏ t : Fin m, trB (bx t.castSucc).1 ((bx t.castSucc).2 - (bx t.castSucc).1)) *
        exB (bx (Fin.last m)).1 ((bx (Fin.last m)).2 - (bx (Fin.last m)).1)) ≤ B) : ShareLe bx B := by
  intro δ hδ
  have hfit' : (∑ t : Fin m, (bx t.castSucc).1) + (bx (Fin.last m)).1 + ∑ i, ((bx i).2 - (bx i).1) ≤ DEN := by
    have e : (∑ t : Fin m, (bx t.castSucc).1) + (bx (Fin.last m)).1 = ∑ i, (bx i).1 :=
      (Fin.sum_univ_castSucc fun i => (bx i).1).symm
    have e2 : ∑ i, (bx i).1 + ∑ i, ((bx i).2 - (bx i).1) = ∑ i, (bx i).2 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Nat.add_sub_cancel' (hle i)
    omega
  have hsh := SieveRough.shareBox (fun i => (bx i).1) (fun i => (bx i).2 - (bx i).1) hlo hfit' hB hδ
  filter_upwards [SieveDrop.tendsto_xq.eventually hsh] with q hq
  refine le_trans ?_ hq
  unfold SB
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.cast_nonneg _)
  intro rt hrt
  obtain ⟨hp, -, hc⟩ := mem_famB.1 hrt
  rw [Fintype.mem_piFinset]
  intro t
  rw [boxP, mem_primesIn]
  refine ⟨(hp t).2, (hc t).1, ?_⟩
  have : (((bx t).1 : ℝ) + ((bx t).2 - (bx t).1 : ℕ)) = ((bx t).2 : ℝ) := by
    rw [← Nat.cast_add, Nat.add_sub_cancel' (hle t)]
  rw [this]
  exact (hc t).2

/-! ### The weight of a frozen part -/

/-- The primes `P` of `(x/R, 2x/R]` give the numbers `n = RP` of the terms at a level `Z` that is at most each of
them, with the weight `1`. -/
theorem card_primes_le_famJR {q : ℕ} (hx0 : 0 < xq q) {R Z : ℕ} (hR : 0 < R)
    (hZ : ∀ P : ℕ, xq q / R < P → Z ≤ P) :
    (((Ioc ⌊xq q / R⌋₊ ⌊2 * (xq q / R)⌋₊).filter Nat.Prime).card : ℝ) ≤
      famJR (fun _ => 1) (N1 q) (N2 q) Z R (famB q (boxFn [] 0 rfl)) := by
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have hY0 : 0 ≤ xq q / R := (div_pos hx0 hRr).le
  rw [famJR_zero _ _ _ _ hR q]
  simp only [one_mul]
  rw [Finset.sum_boole]
  have hcard : ((Ioc ⌊xq q / R⌋₊ ⌊2 * (xq q / R)⌋₊).filter Nat.Prime).card ≤
      ((Ioc (N1 q) (N2 q)).filter fun n => R ∣ n ∧ SieveTree.rough Z (n / R)).card := by
    refine Finset.card_le_card_of_injOn (fun P => R * P) ?_ ?_
    · intro P hP
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hP
      obtain ⟨⟨h1, h2⟩, hPp⟩ := hP
      have h1' : xq q / R < P := Nat.lt_of_floor_lt h1
      have h2' : (P : ℝ) ≤ 2 * (xq q / R) := (Nat.le_floor_iff (by positivity)).1 h2
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨?_, ?_⟩, dvd_mul_right R P, ?_⟩
      · rw [Nat.floor_lt hx0.le]
        rw [div_lt_iff₀ hRr] at h1'
        push_cast
        linarith
      · refine Nat.le_floor ?_
        have h3 : (P : ℝ) * R ≤ 2 * xq q := by
          have := mul_le_mul_of_nonneg_right h2' hRr.le
          rwa [mul_assoc, div_mul_cancel₀ _ hRr.ne'] at this
        push_cast
        linarith
      · rw [Nat.mul_div_cancel_left P hR]
        exact rough_prime hPp (hZ P h1')
    · intro P _ P' _ h
      exact Nat.eq_of_mul_eq_mul_left hR h
  exact_mod_cast hcard

/-- **The weight of the narrower frozen part is at most `h₁/DEN` times the share of the box.** For
`0 < l₁ ≤ h₁ ≤ DEN` with `h₁ ≤ 2l₁`, the first cell of `βx` below `x^{l₁/DEN}`, and a share `B ≥ 0` of the box:
for every `δ > 0`, `Σ 1/R ≤ (h₁/DEN)B + δ` at a large modulus. -/
theorem froz_weight_le [RouteOK] {ctx : Cell} (hctx : 0 < ctx.1 ∧ ctx.1 ≤ ctx.2 ∧ ctx.2 ≤ DEN)
    (h2 : ctx.2 ≤ 2 * ctx.1) {s : ℕ} (βx : Fin (s + 1) → Cell) (hβ : (βx 0).2 ≤ ctx.1) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ShareLe (Fin.cons (α := fun _ => Cell) ctx βx) B) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, WF (frozS q (e1 ctx + 1) (e2 ctx - 1) βx) frozR ≤ (ctx.2 : ℝ) / DEN * B + δ := by
  have hD := DEN_pos'
  have hh : 0 < ctx.2 := by omega
  have hh' : (0 : ℝ) < ctx.2 := by exact_mod_cast hh
  have hhD : (ctx.2 : ℝ) / DEN ≤ 1 := by rw [div_le_one hD]; exact_mod_cast hctx.2.2
  have hhD0 : 0 ≤ (ctx.2 : ℝ) / DEN := by positivity
  -- the margins
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (1 / 2) (δ / (8 * (B + 1))) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hεdef]; exact lt_min (by norm_num) (by positivity)
  have hε2 : ε ≤ 1 / 2 := by rw [hεdef]; exact min_le_left _ _
  have hεB : ε * (B + 1) ≤ δ / 8 := by
    have h1 : ε ≤ δ / (8 * (B + 1)) := by rw [hεdef]; exact min_le_right _ _
    calc ε * (B + 1) ≤ δ / (8 * (B + 1)) * (B + 1) := mul_le_mul_of_nonneg_right h1 (by linarith)
      _ = δ / 8 := by field_simp
  obtain ⟨δ₁, hδ₁def⟩ : ∃ δ₁ : ℝ, δ₁ = min 1 (δ / 4) := ⟨_, rfl⟩
  have hδ₁0 : 0 < δ₁ := by rw [hδ₁def]; exact lt_min one_pos (by positivity)
  have hδ₁1 : δ₁ ≤ 1 := by rw [hδ₁def]; exact min_le_left _ _
  have hδ₁4 : δ₁ ≤ δ / 4 := by rw [hδ₁def]; exact min_le_right _ _
  have hc : (0 : ℝ) < (ctx.1 : ℝ) / DEN := div_pos (by exact_mod_cast hctx.1) hD
  filter_upwards [big_ev, hB δ₁ hδ₁0, SieveDrop.tendsto_xq.eventually (primes_level hh hc hε0),
    eventually_ge_atTop 1] with q hq hBq hprimes hq1
  obtain ⟨-, hx3, -, -, h3⟩ := big_facts hq
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 ≤ xq q := by linarith
  have hlx : 0 < Real.log (xq q) := Real.log_pos (by linarith)
  have hX := Xq_pos hq
  have hxhi : Xe q ctx.1 * Xe q (e2 ctx - 1) = xq q := by
    rw [← Xe_add hx0, ← Xe_DEN]
    congr 1
    unfold e2
    omega
  have hxlo : Xe q (ctx.2 - 1) * Xe q (e1 ctx + 1) = xq q := by
    rw [← Xe_add hx0, ← Xe_DEN]
    congr 1
    unfold e1
    omega
  -- each `R`
  have hterm : ∀ am ∈ frozS q (e1 ctx + 1) (e2 ctx - 1) βx,
      (1 - ε) * ((DEN : ℝ) / ctx.2) * (1 / (frozR am : ℝ) * Xq q) ≤
        famJR (fun _ => 1) (N1 q) (N2 q) ⌈xq q ^ ((ctx.1 : ℝ) / DEN)⌉₊ (frozR am) (famB q (boxFn [] 0 rfl)) := by
    intro am ham
    have hR0 := frozR_pos ham
    have hRr : (0 : ℝ) < frozR am := by exact_mod_cast hR0
    obtain ⟨-, -, hlo, hhi⟩ := mem_frozS.1 ham
    have hY1 : xq q ^ ((ctx.1 : ℝ) / DEN) ≤ xq q / frozR am := by
      rw [le_div_iff₀ hRr]
      calc xq q ^ ((ctx.1 : ℝ) / DEN) * (frozR am : ℝ) ≤ Xe q ctx.1 * Xe q (e2 ctx - 1) :=
            mul_le_mul_of_nonneg_left hhi (Xe_pos hx0 _).le
        _ = xq q := hxhi
    have hY2 : xq q / frozR am ≤ xq q ^ ((ctx.2 : ℝ) / DEN) := by
      rw [div_le_iff₀ hRr]
      calc xq q = Xe q (ctx.2 - 1) * Xe q (e1 ctx + 1) := hxlo.symm
        _ ≤ Xe q ctx.2 * (frozR am : ℝ) :=
            mul_le_mul (Xe_mono hx1 (Nat.sub_le _ _)) hlo.le (Xe_pos hx0 _).le (Xe_pos hx0 _).le
    have h1 := hprimes (xq q / frozR am) hY1 hY2
    have h2 := card_primes_le_famJR hx0 (Z := ⌈xq q ^ ((ctx.1 : ℝ) / DEN)⌉₊) hR0 fun P hP =>
      Nat.ceil_le.2 (hY1.trans hP.le)
    refine le_trans (le_of_eq ?_) (h1.trans h2)
    unfold Xq
    field_simp
  -- the sum
  have hsum : (1 - ε) * ((DEN : ℝ) / ctx.2) * (WF (frozS q (e1 ctx + 1) (e2 ctx - 1) βx) frozR * Xq q) ≤
      (B + δ₁) * Xq q := by
    have h1 : (1 - ε) * ((DEN : ℝ) / ctx.2) * (WF (frozS q (e1 ctx + 1) (e2 ctx - 1) βx) frozR * Xq q) =
        ∑ am ∈ frozS q (e1 ctx + 1) (e2 ctx - 1) βx,
          (1 - ε) * ((DEN : ℝ) / ctx.2) * (1 / (frozR am : ℝ) * Xq q) := by
      unfold WF
      rw [Finset.sum_mul, Finset.mul_sum]
    rw [h1]
    refine (Finset.sum_le_sum hterm).trans ?_
    refine (flip_inject hq hctx (le_refl _) h2 βx hβ (fun _ => 1) fun _ => zero_le_one).trans ?_
    refine le_trans ?_ hBq
    unfold famI
    refine Finset.sum_le_sum fun rt hrt => ?_
    have hW : 0 < ∏ i, rt i := Finset.prod_pos fun i _ => ((mem_famB.1 hrt).1 i).2.pos
    simp only [one_mul]
    rw [Finset.sum_boole]
    exact_mod_cast SieveDrop.card_le_Psi hx0 hW
  -- so
  have h1e : 0 < 1 - ε := by linarith
  have hW0 := WF_nonneg (frozS q (e1 ctx + 1) (e2 ctx - 1) βx) frozR
  have hW1 : (1 - ε) * ((DEN : ℝ) / ctx.2) * WF (frozS q (e1 ctx + 1) (e2 ctx - 1) βx) frozR ≤ B + δ₁ := by
    have := hsum
    rw [← mul_assoc] at this
    exact le_of_mul_le_mul_right this hX
  have hW2 : WF (frozS q (e1 ctx + 1) (e2 ctx - 1) βx) frozR ≤ (ctx.2 : ℝ) / DEN * ((B + δ₁) / (1 - ε)) := by
    rw [mul_div_assoc', le_div_iff₀ h1e]
    have e : WF (frozS q (e1 ctx + 1) (e2 ctx - 1) βx) frozR * (1 - ε) =
        (ctx.2 : ℝ) / DEN * ((1 - ε) * ((DEN : ℝ) / ctx.2) * WF (frozS q (e1 ctx + 1) (e2 ctx - 1) βx) frozR) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hW1 hhD0
  have hdiv : (B + δ₁) / (1 - ε) ≤ B + δ := by
    rw [div_le_iff₀ h1e]
    nlinarith
  calc WF (frozS q (e1 ctx + 1) (e2 ctx - 1) βx) frozR ≤ (ctx.2 : ℝ) / DEN * ((B + δ₁) / (1 - ε)) := hW2
    _ ≤ (ctx.2 : ℝ) / DEN * (B + δ) := mul_le_mul_of_nonneg_left hdiv hhD0
    _ ≤ (ctx.2 : ℝ) / DEN * B + δ := by nlinarith

/-! ### A cut of the range of `R` -/

/-- A sum over a frozen part is the sum over the two parts that a cut of the range of `R` makes. -/
theorem sum_frozS_split {q : ℕ} (hx1 : 1 ≤ xq q) {e₁ e₂ e₃ : ℕ} (h12 : e₁ ≤ e₂) (h23 : e₂ ≤ e₃) {s : ℕ}
    (βx : Fin (s + 1) → Cell) (F : (Fin (s + 1) → ℕ) × ℕ → ℝ) :
    ∑ am ∈ frozS q e₁ e₃ βx, F am = ∑ am ∈ frozS q e₁ e₂ βx, F am + ∑ am ∈ frozS q e₂ e₃ βx, F am := by
  have el : frozS q e₁ e₂ βx =
      (frozS q e₁ e₃ βx).filter fun am => (frozR am : ℝ) ≤ xq q ^ ((e₂ : ℝ) / DEN) := by
    ext am
    simp only [Finset.mem_filter, mem_frozS]
    constructor
    · rintro ⟨h, hr, hlo, hhi⟩
      exact ⟨⟨h, hr, hlo, hhi.trans (pow_mono hx1 h23)⟩, hhi⟩
    · rintro ⟨⟨h, hr, hlo, -⟩, hhi⟩
      exact ⟨h, hr, hlo, hhi⟩
  have er : frozS q e₂ e₃ βx =
      (frozS q e₁ e₃ βx).filter fun am => ¬ (frozR am : ℝ) ≤ xq q ^ ((e₂ : ℝ) / DEN) := by
    ext am
    simp only [Finset.mem_filter, mem_frozS, not_le]
    constructor
    · rintro ⟨h, hr, hlo, hhi⟩
      exact ⟨⟨h, hr, lt_of_le_of_lt (pow_mono hx1 h12) hlo, hhi⟩, hlo⟩
    · rintro ⟨⟨h, hr, -, hhi⟩, hlo⟩
      exact ⟨h, hr, hlo, hhi⟩
  rw [el, er, Finset.sum_filter_add_sum_filter_not]

/-! ### The terms at the level in the comparison set -/

/-- For `q ≥ 1` and `R > 0`: the terms at a level `Z` of the chain with no prime, on the multiples of `R`, in the
comparison set, are at most `Ψ(x/R, Z)/φ(q)`. -/
theorem famJR_gB_zero_le (q : ℕ) (hq1 : 1 ≤ q) {R : ℕ} (hR : 0 < R) (Z : ℕ) :
    famJR (gB q) (N1 q) (N2 q) Z R (famB q (boxFn [] 0 rfl)) ≤ (q.totient : ℝ)⁻¹ * (Psi (xq q / R) Z : ℝ) := by
  have hx : 0 < xq q := by
    have : (0 : ℝ) < q := by exact_mod_cast hq1
    positivity
  rw [famJR_zero _ _ _ _ hR q]
  calc ∑ n ∈ Ioc (N1 q) (N2 q), gB q n * (if R ∣ n ∧ SieveTree.rough Z (n / R) then 1 else 0)
      ≤ ∑ n ∈ Ioc (N1 q) (N2 q), (q.totient : ℝ)⁻¹ * (if R ∣ n ∧ SieveTree.rough Z (n / R) then 1 else 0) :=
        Finset.sum_le_sum fun n _ =>
          mul_le_mul_of_nonneg_right (SieveDrop.gB_le q n) (by split_ifs <;> norm_num)
    _ = (q.totient : ℝ)⁻¹ * (((Ioc (N1 q) (N2 q)).filter
          (fun n => R ∣ n ∧ SieveTree.rough Z (n / R))).card : ℝ) := by
        rw [← Finset.mul_sum, Finset.card_filter]
        push_cast
        rfl
    _ ≤ (q.totient : ℝ)⁻¹ * (Psi (xq q / R) Z : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h := card_le_PsiR hx (z := Z) hR (W := 1) one_pos
        simp only [Nat.mul_one] at h
        exact_mod_cast h

/-- **The terms at the level in the comparison set, over a frozen part in the range of `r'`.** For `0 < t` with
`h₁ + t + 1 ≤ DEN` and `bd` at least the bound of `SieveAd.psi_level` for the rough numbers of `(x/R, 2x/R]` at the
level `x^{t/DEN}`: for every `ε > 0` and large `q` they are at most `((bd + ε)·Σ 1/R)x/(φ(q) log x)`. -/
theorem froz_ends_le [RouteOK] {ι : Type} {S : ℕ → Finset ι} {R : ι → ℕ} {ctx : Cell}
    (hctx : 0 < ctx.1 ∧ ctx.1 ≤ ctx.2) (hS : InSlab S R ctx) {t : ℕ} (ht0 : 0 < t) (htD : ctx.2 + t + 1 ≤ DEN)
    {bd : ℝ} (hbd : (omKw (DEN - ctx.2 - t - 1) t (ctx.2 - ctx.1 + 2) 1 : ℝ) / K * ((DEN : ℝ) / t) ≤ bd)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, ∑ i ∈ S q,
        famJR (gB q) (N1 q) (N2 q) ⌈xq q ^ ((t : ℝ) / DEN)⌉₊ (R i) (famB q (boxFn [] 0 rfl)) ≤
      (q.totient : ℝ)⁻¹ * ((bd + ε) * WF (S q) R * Xq q) := by
  have hfit : (DEN - ctx.2 - t - 1) + t + (ctx.2 - ctx.1 + 2) ≤ DEN := by omega
  have hpsi := psi_level (y := t) (s := DEN - ctx.2 - t - 1) (W := ctx.2 - ctx.1 + 2) ht0 hfit hε
  filter_upwards [big_ev, hS, SieveDrop.tendsto_xq.eventually hpsi, eventually_ge_atTop 1] with q hq hSq hpq hq1
  obtain ⟨-, hx3, -⟩ := big_facts hq
  have hx0 : 0 < xq q := by linarith
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hterm : ∀ i ∈ S q, famJR (gB q) (N1 q) (N2 q) ⌈xq q ^ ((t : ℝ) / DEN)⌉₊ (R i) (famB q (boxFn [] 0 rfl)) ≤
      (q.totient : ℝ)⁻¹ * ((bd + ε) * (1 / (R i : ℝ) * Xq q)) := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := hSq i hi
    have hR0 : (0 : ℝ) < R i := lt_of_le_of_lt (Real.rpow_nonneg hx0.le _) hlo
    have hRpos : 0 < R i := by exact_mod_cast hR0
    have e1' : ((DEN - ctx.2 - t - 1 + t + 1 : ℕ) : ℝ) = (e1 ctx : ℝ) := by
      congr 1
      unfold e1
      omega
    have e2' : ((DEN - ctx.2 - t - 1 + t + (ctx.2 - ctx.1 + 2) : ℕ) : ℝ) = (e2 ctx : ℝ) := by
      congr 1
      unfold e2
      omega
    have h1 := hpq (R i : ℝ) (by rw [e1']; exact hlo.le) (by rw [e2']; exact hhi)
    refine (famJR_gB_zero_le q hq1 hRpos _).trans (mul_le_mul_of_nonneg_left (h1.trans ?_) hφ)
    have h2 : 0 ≤ xq q / (R i : ℝ) / Real.log (xq q) :=
      div_nonneg (div_pos hx0 hR0).le (Real.log_pos (by linarith)).le
    calc ((omKw (DEN - ctx.2 - t - 1) t (ctx.2 - ctx.1 + 2) 1 : ℝ) / K * ((DEN : ℝ) / t) + ε) *
          (xq q / (R i : ℝ) / Real.log (xq q))
        ≤ (bd + ε) * (xq q / (R i : ℝ) / Real.log (xq q)) := mul_le_mul_of_nonneg_right (by linarith) h2
      _ = (bd + ε) * (1 / (R i : ℝ) * Xq q) := by unfold Xq; field_simp
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  unfold WF
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-! ### The top of the tree -/

/-- **What a tree gives at its top, for a term that needs an upper bound.** Over a frozen part, for `f ≤ t ≤ DEN`:
if the terms at the floor `x^{f/DEN}` are evaluated and the chain of one prime in `[x^{f/DEN}, x^{t/DEN})` has
`BdF` at the cost `C` with the sign `+`, the terms at the level `x^{t/DEN}`, in `𝒜` minus the comparison set, are
at most `(C·Σ 1/R + o(1))x/(φ(q) log x)`. -/
theorem froz_top_le [RouteOK] {ι : Type} {S : ℕ → Finset ι} {R : ι → ℕ} {f t : ℕ} (hft : f ≤ t) (ht : t ≤ DEN)
    {C : ℝ} (hJ : EvJF S R f (boxFn [] 0 rfl)) (hT : BdF S R true C (boxFn [(f, t)] 1 rfl)) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
      dJF q a t (S q) R (boxFn [] 0 rfl) ≤ (q.totient : ℝ)⁻¹ * ((C * WF (S q) R + η) * Xq q) := by
  filter_upwards [hJ (η / 2) (by positivity), hT (η / 2) (by positivity), big_ev] with q hq1 hq2 hbig a ha
  rw [dJF_level hbig a (S q) R hft ht]
  have h1 := (abs_le.1 (hq1 a ha)).2
  have h2 := hq2 a ha
  simp only [sg, ite_true, one_mul] at h2
  have e : (q.totient : ℝ)⁻¹ * ((C * WF (S q) R + η) * Xq q) =
      (q.totient : ℝ)⁻¹ * (η / 2 * Xq q) + (q.totient : ℝ)⁻¹ * ((C * WF (S q) R + η / 2) * Xq q) := by ring
  rw [e]
  linarith

/-- **What a tree gives at its top, for a term that needs a lower bound**: with the chain of one prime bounded
with the sign `−`, the terms at the level are at least `−(C·Σ 1/R + o(1))x/(φ(q) log x)`. -/
theorem froz_top_ge [RouteOK] {ι : Type} {S : ℕ → Finset ι} {R : ι → ℕ} {f t : ℕ} (hft : f ≤ t) (ht : t ≤ DEN)
    {C : ℝ} (hJ : EvJF S R f (boxFn [] 0 rfl)) (hT : BdF S R false C (boxFn [(f, t)] 1 rfl)) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
      -((q.totient : ℝ)⁻¹ * ((C * WF (S q) R + η) * Xq q)) ≤ dJF q a t (S q) R (boxFn [] 0 rfl) := by
  filter_upwards [hJ (η / 2) (by positivity), hT (η / 2) (by positivity), big_ev] with q hq1 hq2 hbig a ha
  rw [dJF_level hbig a (S q) R hft ht]
  have h1 := (abs_le.1 (hq1 a ha)).1
  have h2 := hq2 a ha
  simp only [sg, Bool.false_eq_true, ite_false, neg_mul, one_mul] at h2
  have e : (q.totient : ℝ)⁻¹ * ((C * WF (S q) R + η) * Xq q) =
      (q.totient : ℝ)⁻¹ * (η / 2 * Xq q) + (q.totient : ℝ)⁻¹ * ((C * WF (S q) R + η / 2) * Xq q) := by ring
  rw [e]
  linarith

/-! ### The reversal bounds the term of the box -/

omit [Route] in
/-- The arithmetic of the two bounds: with `Wo ≤ wo + 3δ` and `Wb ≤ wb + 2δ`, `δ ≤ 1`. -/
theorem flip_arith {C bd wo wb Wo Wb η δ ε : ℝ} (hC : 0 ≤ C) (hbd : 0 ≤ bd) (hwb : 0 ≤ wb) (hη : 0 < η)
    (hδ : δ = min 1 (η / (16 * (C + bd + 1)))) (hε : ε = η / (8 * (wb + 3)))
    (hWo : Wo ≤ wo + 3 * δ) (hWb : Wb ≤ wb + 2 * δ) :
    C * Wo + (bd + ε) * Wb + η / 4 + η / 4 ≤ C * wo + bd * wb + η := by
  have hM : 0 < C + bd + 1 := by linarith
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := by rw [hδ]; exact min_le_left _ _
  have hδM : δ * (C + bd + 1) ≤ η / 16 := by
    have h1 : δ ≤ η / (16 * (C + bd + 1)) := by rw [hδ]; exact min_le_right _ _
    calc δ * (C + bd + 1) ≤ η / (16 * (C + bd + 1)) * (C + bd + 1) := mul_le_mul_of_nonneg_right h1 hM.le
      _ = η / 16 := by field_simp
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεw : ε * (wb + 3) = η / 8 := by rw [hε]; field_simp
  have h1 : C * Wo ≤ C * wo + 3 * (C * δ) := by nlinarith
  have h2 : bd * Wb ≤ bd * wb + 2 * (bd * δ) := by nlinarith
  have h3 : ε * Wb ≤ ε * (wb + 3) := mul_le_mul_of_nonneg_left (by linarith) hε0.le
  have h4 : C * δ ≤ η / 16 := by nlinarith
  have h5 : bd * δ ≤ η / 16 := by nlinarith
  nlinarith

/-- The `R` within `x^{1/DEN}` of the lower end of the range lie in the range of `r'` for `ctx`. -/
theorem inSlab_ends_lo [RouteOK] {ctx : Cell} (hctx : 0 < ctx.1 ∧ ctx.1 < ctx.2 ∧ ctx.2 ≤ DEN) {s : ℕ}
    (βx : Fin (s + 1) → Cell) : InSlab (fun q => frozS q (e1 ctx) (e1 ctx + 1) βx) frozR ctx := by
  filter_upwards [big_ev] with q hq am ham
  obtain ⟨-, hx3, -⟩ := big_facts hq
  obtain ⟨-, -, hlo, hhi⟩ := mem_frozS.1 ham
  exact ⟨hlo, hhi.trans (pow_mono (by linarith) (show e1 ctx + 1 ≤ e2 ctx by unfold e1 e2; omega))⟩

/-- The `R` within `x^{1/DEN}` of the upper end of the range lie in the range of `r'` for `ctx`. -/
theorem inSlab_ends_hi [RouteOK] {ctx : Cell} (hctx : 0 < ctx.1 ∧ ctx.1 < ctx.2 ∧ ctx.2 ≤ DEN) {s : ℕ}
    (βx : Fin (s + 1) → Cell) : InSlab (fun q => frozS q (e2 ctx - 1) (e2 ctx) βx) frozR ctx := by
  filter_upwards [big_ev] with q hq am ham
  obtain ⟨-, hx3, -⟩ := big_facts hq
  obtain ⟨-, -, hlo, hhi⟩ := mem_frozS.1 ham
  exact ⟨lt_of_le_of_lt (pow_mono (by linarith) (show e1 ctx ≤ e2 ctx - 1 by unfold e1 e2; omega)) hlo, hhi⟩

/-- A sum over the frozen part of `ctx` is the sum over the `R` near the lower end, those of the narrower frozen
part, and those near the upper end. -/
theorem sum_frozS_three {q : ℕ} (hx1 : 1 ≤ xq q) {ctx : Cell} (hctx : 0 < ctx.1 ∧ ctx.1 < ctx.2 ∧ ctx.2 ≤ DEN)
    {s : ℕ} (βx : Fin (s + 1) → Cell) (F : (Fin (s + 1) → ℕ) × ℕ → ℝ) :
    ∑ am ∈ frozS q (e1 ctx) (e2 ctx) βx, F am =
      ∑ am ∈ frozS q (e1 ctx) (e1 ctx + 1) βx, F am + ∑ am ∈ frozS q (e1 ctx + 1) (e2 ctx - 1) βx, F am +
        ∑ am ∈ frozS q (e2 ctx - 1) (e2 ctx) βx, F am := by
  have he12 : e1 ctx + 1 ≤ e2 ctx - 1 := by unfold e1 e2; omega
  rw [sum_frozS_split hx1 (Nat.le_succ _) (show e1 ctx + 1 ≤ e2 ctx by omega) βx F,
    sum_frozS_split hx1 he12 (Nat.sub_le _ _) βx F, add_assoc]

/-- **The reversal bounds a term that needs an upper bound.** For a box `(p₁, a)`, the cell of `p₁` being
`ctx = (l₁, h₁)` with `0 < l₁ < h₁ ≤ DEN`, a level `t` with `t ≤ l₁`, `h₁ ≤ 2t` and `h₁ + t + 1 ≤ DEN`, a floor
`f ≤ t`, and the first cell of `βx` below `x^{l₁/DEN}`: if over the frozen part of `ctx` the terms at the floor are
evaluated and the chain of one prime in `[x^{f/DEN}, x^{t/DEN})` has `BdF` at the cost `C ≥ 0` with the sign `+`,
then the term of the box has `Bd false` at the cost `C(w₀ + w₁ + w₂) + bd(w₁ + w₂)`: `w₀`, `w₁`, `w₂` bound the
weights of the `R` in `(x^{(DEN−h₁+1)/DEN}, x^{(DEN−l₁)/DEN}]` and within `x^{1/DEN}` of the two ends, and `bd` the
rough numbers of `(x/R, 2x/R]` at the level. -/
theorem bd_flip_neg [RouteOK] {ctx : Cell} (hctx : 0 < ctx.1 ∧ ctx.1 < ctx.2 ∧ ctx.2 ≤ DEN) {t f : ℕ}
    (hft : f ≤ t) (ht0 : 0 < t) (ht : t ≤ ctx.1) (ht2 : ctx.2 ≤ 2 * t) (htD : ctx.2 + t + 1 ≤ DEN) {s : ℕ}
    (βx : Fin (s + 1) → Cell) (hβ : (βx 0).2 ≤ ctx.1) {C : ℝ} (hC : 0 ≤ C)
    (hJ : EvJF (fun q => frozS q (e1 ctx) (e2 ctx) βx) frozR f (boxFn [] 0 rfl))
    (hT : BdF (fun q => frozS q (e1 ctx) (e2 ctx) βx) frozR true C (boxFn [(f, t)] 1 rfl)) {bd : ℝ}
    (hbd : (omKw (DEN - ctx.2 - t - 1) t (ctx.2 - ctx.1 + 2) 1 : ℝ) / K * ((DEN : ℝ) / t) ≤ bd)
    {w₀ w₁ w₂ : ℝ} (hw₁0 : 0 ≤ w₁) (hw₂0 : 0 ≤ w₂)
    (hw₀ : ∀ δ : ℝ, 0 < δ → ∀ᶠ q : ℕ in atTop, WF (frozS q (e1 ctx + 1) (e2 ctx - 1) βx) frozR ≤ w₀ + δ)
    (hw₁ : ∀ δ : ℝ, 0 < δ → ∀ᶠ q : ℕ in atTop, WF (frozS q (e1 ctx) (e1 ctx + 1) βx) frozR ≤ w₁ + δ)
    (hw₂ : ∀ δ : ℝ, 0 < δ → ∀ᶠ q : ℕ in atTop, WF (frozS q (e2 ctx - 1) (e2 ctx) βx) frozR ≤ w₂ + δ) :
    Bd false (C * (w₀ + w₁ + w₂) + bd * (w₁ + w₂)) (Fin.cons (α := fun _ => Cell) ctx βx) := by
  intro η hη
  have hD := DEN_pos'
  have hK := K_pos'
  have hbd0 : 0 ≤ bd := le_trans (by positivity) hbd
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min 1 (η / (16 * (C + bd + 1))) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min one_pos (by positivity)
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = η / (8 * (w₁ + w₂ + 3)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hεdef]; positivity
  have he12 : e1 ctx + 1 ≤ e2 ctx - 1 := by unfold e1 e2; omega
  have hend1 := froz_ends_le ⟨hctx.1, hctx.2.1.le⟩ (inSlab_ends_lo hctx βx) ht0 htD hbd hε0
  have hend2 := froz_ends_le ⟨hctx.1, hctx.2.1.le⟩ (inSlab_ends_hi hctx βx) ht0 htD hbd hε0
  filter_upwards [big_ev, froz_top_le hft (by omega) hJ hT (η := η / 4) (by positivity), hw₀ δ hδ0, hw₁ δ hδ0,
    hw₂ δ hδ0, hend1, hend2] with q hq htop hW₀ hW₁ hW₂ he1 he2 a ha
  obtain ⟨-, hx3, -⟩ := big_facts hq
  have hx1 : 1 ≤ xq q := by linarith
  have hX := Xq_pos hq
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hsplit := sum_frozS_three hx1 hctx βx
  have hWo : WF (frozS q (e1 ctx) (e2 ctx) βx) frozR ≤ (w₀ + w₁ + w₂) + 3 * δ := by
    unfold WF at hW₀ hW₁ hW₂ ⊢
    rw [hsplit]
    linarith
  have hWb0 : 0 ≤ WF (frozS q (e1 ctx) (e1 ctx + 1) βx) frozR + WF (frozS q (e2 ctx - 1) (e2 ctx) βx) frozR :=
    add_nonneg (WF_nonneg _ _) (WF_nonneg _ _)
  have hcov := flip_cover hq ⟨hctx.2.1.le, hctx.2.2⟩ ht βx (gA q a) (gA_nonneg q a)
  have hinj := flip_inject hq ⟨hctx.1, hctx.2.1.le, hctx.2.2⟩ ht ht2 βx hβ (gB q) (SieveDrop.gB_nonneg q)
  have hJB := hsplit fun am =>
    famJR (gB q) (N1 q) (N2 q) ⌈xq q ^ ((t : ℝ) / DEN)⌉₊ (frozR am) (famB q (boxFn [] 0 rfl))
  have htop' := htop a ha
  unfold dJF at htop'
  rw [Finset.sum_sub_distrib] at htop'
  have harith := flip_arith hC hbd0 (add_nonneg hw₁0 hw₂0) hη hδdef hεdef hWo
    (by linarith : WF (frozS q (e1 ctx) (e1 ctx + 1) βx) frozR + WF (frozS q (e2 ctx - 1) (e2 ctx) βx) frozR ≤
      (w₁ + w₂) + 2 * δ)
  have hfin : (q.totient : ℝ)⁻¹ * ((C * WF (frozS q (e1 ctx) (e2 ctx) βx) frozR + η / 4) * Xq q) +
      (q.totient : ℝ)⁻¹ * ((bd + ε) * WF (frozS q (e1 ctx) (e1 ctx + 1) βx) frozR * Xq q) +
      (q.totient : ℝ)⁻¹ * ((bd + ε) * WF (frozS q (e2 ctx - 1) (e2 ctx) βx) frozR * Xq q) ≤
        (q.totient : ℝ)⁻¹ * ((C * (w₀ + w₁ + w₂) + bd * (w₁ + w₂) + η) * Xq q) := by
    have e : (q.totient : ℝ)⁻¹ * ((C * WF (frozS q (e1 ctx) (e2 ctx) βx) frozR + η / 4) * Xq q) +
        (q.totient : ℝ)⁻¹ * ((bd + ε) * WF (frozS q (e1 ctx) (e1 ctx + 1) βx) frozR * Xq q) +
        (q.totient : ℝ)⁻¹ * ((bd + ε) * WF (frozS q (e2 ctx - 1) (e2 ctx) βx) frozR * Xq q) =
          (q.totient : ℝ)⁻¹ * ((C * WF (frozS q (e1 ctx) (e2 ctx) βx) frozR + (bd + ε) *
            (WF (frozS q (e1 ctx) (e1 ctx + 1) βx) frozR + WF (frozS q (e2 ctx - 1) (e2 ctx) βx) frozR) +
              η / 4) * Xq q) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hX.le) hφ
    linarith
  unfold dI
  simp only [sg, Bool.false_eq_true, ite_false, neg_mul, one_mul, neg_le_neg_iff]
  linarith

/-- **The reversal bounds a term that needs a lower bound**: with the tree over the narrower frozen part, the
chain of one prime bounded with the sign `−`, the term of the box has `Bd true` at the cost
`C·w₀ + bd(w₁ + w₂)`. -/
theorem bd_flip_pos [RouteOK] {ctx : Cell} (hctx : 0 < ctx.1 ∧ ctx.1 < ctx.2 ∧ ctx.2 ≤ DEN) {t f : ℕ}
    (hft : f ≤ t) (ht0 : 0 < t) (ht : t ≤ ctx.1) (ht2 : ctx.2 ≤ 2 * t) (htD : ctx.2 + t + 1 ≤ DEN) {s : ℕ}
    (βx : Fin (s + 1) → Cell) (hβ : (βx 0).2 ≤ ctx.1) {C : ℝ} (hC : 0 ≤ C)
    (hJ : EvJF (fun q => frozS q (e1 ctx + 1) (e2 ctx - 1) βx) frozR f (boxFn [] 0 rfl))
    (hT : BdF (fun q => frozS q (e1 ctx + 1) (e2 ctx - 1) βx) frozR false C (boxFn [(f, t)] 1 rfl)) {bd : ℝ}
    (hbd : (omKw (DEN - ctx.2 - t - 1) t (ctx.2 - ctx.1 + 2) 1 : ℝ) / K * ((DEN : ℝ) / t) ≤ bd)
    {w₀ w₁ w₂ : ℝ} (hw₁0 : 0 ≤ w₁) (hw₂0 : 0 ≤ w₂)
    (hw₀ : ∀ δ : ℝ, 0 < δ → ∀ᶠ q : ℕ in atTop, WF (frozS q (e1 ctx + 1) (e2 ctx - 1) βx) frozR ≤ w₀ + δ)
    (hw₁ : ∀ δ : ℝ, 0 < δ → ∀ᶠ q : ℕ in atTop, WF (frozS q (e1 ctx) (e1 ctx + 1) βx) frozR ≤ w₁ + δ)
    (hw₂ : ∀ δ : ℝ, 0 < δ → ∀ᶠ q : ℕ in atTop, WF (frozS q (e2 ctx - 1) (e2 ctx) βx) frozR ≤ w₂ + δ) :
    Bd true (C * w₀ + bd * (w₁ + w₂)) (Fin.cons (α := fun _ => Cell) ctx βx) := by
  intro η hη
  have hD := DEN_pos'
  have hK := K_pos'
  have hbd0 : 0 ≤ bd := le_trans (by positivity) hbd
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min 1 (η / (16 * (C + bd + 1))) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min one_pos (by positivity)
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = η / (8 * (w₁ + w₂ + 3)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hεdef]; positivity
  have hend1 := froz_ends_le ⟨hctx.1, hctx.2.1.le⟩ (inSlab_ends_lo hctx βx) ht0 htD hbd hε0
  have hend2 := froz_ends_le ⟨hctx.1, hctx.2.1.le⟩ (inSlab_ends_hi hctx βx) ht0 htD hbd hε0
  filter_upwards [big_ev, froz_top_ge hft (by omega) hJ hT (η := η / 4) (by positivity), hw₀ δ hδ0, hw₁ δ hδ0,
    hw₂ δ hδ0, hend1, hend2] with q hq htop hW₀ hW₁ hW₂ he1 he2 a ha
  obtain ⟨-, hx3, -⟩ := big_facts hq
  have hx1 : 1 ≤ xq q := by linarith
  have hX := Xq_pos hq
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hsplit := sum_frozS_three hx1 hctx βx
  have hWb0 : 0 ≤ WF (frozS q (e1 ctx) (e1 ctx + 1) βx) frozR + WF (frozS q (e2 ctx - 1) (e2 ctx) βx) frozR :=
    add_nonneg (WF_nonneg _ _) (WF_nonneg _ _)
  have hinj := flip_inject hq ⟨hctx.1, hctx.2.1.le, hctx.2.2⟩ ht ht2 βx hβ (gA q a) (gA_nonneg q a)
  have hcov := flip_cover hq ⟨hctx.2.1.le, hctx.2.2⟩ ht βx (gB q) (SieveDrop.gB_nonneg q)
  have hJB := hsplit fun am =>
    famJR (gB q) (N1 q) (N2 q) ⌈xq q ^ ((t : ℝ) / DEN)⌉₊ (frozR am) (famB q (boxFn [] 0 rfl))
  have htop' := htop a ha
  unfold dJF at htop'
  rw [Finset.sum_sub_distrib] at htop'
  have harith := flip_arith hC hbd0 (add_nonneg hw₁0 hw₂0) hη hδdef hεdef
    (by linarith : WF (frozS q (e1 ctx + 1) (e2 ctx - 1) βx) frozR ≤ w₀ + 3 * δ)
    (by linarith : WF (frozS q (e1 ctx) (e1 ctx + 1) βx) frozR + WF (frozS q (e2 ctx - 1) (e2 ctx) βx) frozR ≤
      (w₁ + w₂) + 2 * δ)
  have hfin : (q.totient : ℝ)⁻¹ * ((C * WF (frozS q (e1 ctx + 1) (e2 ctx - 1) βx) frozR + η / 4) * Xq q) +
      (q.totient : ℝ)⁻¹ * ((bd + ε) * WF (frozS q (e1 ctx) (e1 ctx + 1) βx) frozR * Xq q) +
      (q.totient : ℝ)⁻¹ * ((bd + ε) * WF (frozS q (e2 ctx - 1) (e2 ctx) βx) frozR * Xq q) ≤
        (q.totient : ℝ)⁻¹ * ((C * w₀ + bd * (w₁ + w₂) + η) * Xq q) := by
    have e : (q.totient : ℝ)⁻¹ * ((C * WF (frozS q (e1 ctx + 1) (e2 ctx - 1) βx) frozR + η / 4) * Xq q) +
        (q.totient : ℝ)⁻¹ * ((bd + ε) * WF (frozS q (e1 ctx) (e1 ctx + 1) βx) frozR * Xq q) +
        (q.totient : ℝ)⁻¹ * ((bd + ε) * WF (frozS q (e2 ctx - 1) (e2 ctx) βx) frozR * Xq q) =
          (q.totient : ℝ)⁻¹ * ((C * WF (frozS q (e1 ctx + 1) (e2 ctx - 1) βx) frozR + (bd + ε) *
            (WF (frozS q (e1 ctx) (e1 ctx + 1) βx) frozR + WF (frozS q (e2 ctx - 1) (e2 ctx) βx) frozR) +
              η / 4) * Xq q) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hX.le) hφ
    linarith
  unfold dI
  simp only [sg, ite_true, one_mul]
  linarith

omit [Route] in
/-- **The reversal bounds a term that needs an upper bound, for any route**: `bd_flip_neg` with the route as a
variable. -/
theorem bd_flip_neg_at (Rt : Route) (hRt : @RouteOK Rt) {ctx : Cell} (hctx : 0 < ctx.1 ∧ ctx.1 < ctx.2 ∧ ctx.2 ≤ DEN)
    {t f : ℕ} (hft : f ≤ t) (ht0 : 0 < t) (ht : t ≤ ctx.1) (ht2 : ctx.2 ≤ 2 * t) (htD : ctx.2 + t + 1 ≤ DEN) {s : ℕ}
    (βx : Fin (s + 1) → Cell) (hβ : (βx 0).2 ≤ ctx.1) {C : ℝ} (hC : 0 ≤ C)
    (hJ : @EvJF Rt _ (fun q => @frozS Rt q (e1 ctx) (e2 ctx) s βx) frozR f 0 (boxFn [] 0 rfl))
    (hT : @BdF Rt _ (fun q => @frozS Rt q (e1 ctx) (e2 ctx) s βx) frozR true C 0 (boxFn [(f, t)] 1 rfl)) {bd : ℝ}
    (hbd : (omKw (DEN - ctx.2 - t - 1) t (ctx.2 - ctx.1 + 2) 1 : ℝ) / K * ((DEN : ℝ) / t) ≤ bd)
    {w₀ w₁ w₂ : ℝ} (hw₁0 : 0 ≤ w₁) (hw₂0 : 0 ≤ w₂)
    (hw₀ : ∀ δ : ℝ, 0 < δ → ∀ᶠ q : ℕ in atTop, WF (@frozS Rt q (e1 ctx + 1) (e2 ctx - 1) s βx) frozR ≤ w₀ + δ)
    (hw₁ : ∀ δ : ℝ, 0 < δ → ∀ᶠ q : ℕ in atTop, WF (@frozS Rt q (e1 ctx) (e1 ctx + 1) s βx) frozR ≤ w₁ + δ)
    (hw₂ : ∀ δ : ℝ, 0 < δ → ∀ᶠ q : ℕ in atTop, WF (@frozS Rt q (e2 ctx - 1) (e2 ctx) s βx) frozR ≤ w₂ + δ) :
    @Bd Rt false (C * (w₀ + w₁ + w₂) + bd * (w₁ + w₂)) (s + 1) (Fin.cons (α := fun _ => Cell) ctx βx) :=
  @bd_flip_neg Rt hRt ctx hctx t f hft ht0 ht ht2 htD s βx hβ C hC hJ hT bd hbd w₀ w₁ w₂ hw₁0 hw₂0 hw₀ hw₁ hw₂

omit [Route] in
/-- **The reversal bounds a term that needs a lower bound, for any route**: `bd_flip_pos` with the route as a
variable. -/
theorem bd_flip_pos_at (Rt : Route) (hRt : @RouteOK Rt) {ctx : Cell} (hctx : 0 < ctx.1 ∧ ctx.1 < ctx.2 ∧ ctx.2 ≤ DEN)
    {t f : ℕ} (hft : f ≤ t) (ht0 : 0 < t) (ht : t ≤ ctx.1) (ht2 : ctx.2 ≤ 2 * t) (htD : ctx.2 + t + 1 ≤ DEN) {s : ℕ}
    (βx : Fin (s + 1) → Cell) (hβ : (βx 0).2 ≤ ctx.1) {C : ℝ} (hC : 0 ≤ C)
    (hJ : @EvJF Rt _ (fun q => @frozS Rt q (e1 ctx + 1) (e2 ctx - 1) s βx) frozR f 0 (boxFn [] 0 rfl))
    (hT : @BdF Rt _ (fun q => @frozS Rt q (e1 ctx + 1) (e2 ctx - 1) s βx) frozR false C 0 (boxFn [(f, t)] 1 rfl))
    {bd : ℝ} (hbd : (omKw (DEN - ctx.2 - t - 1) t (ctx.2 - ctx.1 + 2) 1 : ℝ) / K * ((DEN : ℝ) / t) ≤ bd)
    {w₀ w₁ w₂ : ℝ} (hw₁0 : 0 ≤ w₁) (hw₂0 : 0 ≤ w₂)
    (hw₀ : ∀ δ : ℝ, 0 < δ → ∀ᶠ q : ℕ in atTop, WF (@frozS Rt q (e1 ctx + 1) (e2 ctx - 1) s βx) frozR ≤ w₀ + δ)
    (hw₁ : ∀ δ : ℝ, 0 < δ → ∀ᶠ q : ℕ in atTop, WF (@frozS Rt q (e1 ctx) (e1 ctx + 1) s βx) frozR ≤ w₁ + δ)
    (hw₂ : ∀ δ : ℝ, 0 < δ → ∀ᶠ q : ℕ in atTop, WF (@frozS Rt q (e2 ctx - 1) (e2 ctx) s βx) frozR ≤ w₂ + δ) :
    @Bd Rt true (C * w₀ + bd * (w₁ + w₂)) (s + 1) (Fin.cons (α := fun _ => Cell) ctx βx) :=
  @bd_flip_pos Rt hRt ctx hctx t f hft ht0 ht ht2 htD s βx hβ C hC hJ hT bd hbd w₀ w₁ w₂ hw₁0 hw₂0 hw₀ hw₁ hw₂

omit [Route] in
/-- **The weight of the narrower frozen part, for any route**: `froz_weight_le` with the route as a variable. -/
theorem froz_weight_le_at (Rt : Route) (hRt : @RouteOK Rt) {ctx : Cell} (hctx : 0 < ctx.1 ∧ ctx.1 ≤ ctx.2 ∧ ctx.2 ≤ DEN)
    (h2 : ctx.2 ≤ 2 * ctx.1) {s : ℕ} (βx : Fin (s + 1) → Cell) (hβ : (βx 0).2 ≤ ctx.1) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : @ShareLe Rt (s + 1) (Fin.cons (α := fun _ => Cell) ctx βx) B) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, WF (@frozS Rt q (e1 ctx + 1) (e2 ctx - 1) s βx) frozR ≤ (ctx.2 : ℝ) / DEN * B + δ :=
  @froz_weight_le Rt hRt ctx hctx h2 s βx hβ B hB0 hB δ hδ

omit [Route] in
/-- **The share of a box that may be dropped, for any route**: `shareLe_of_box` with the route as a variable. -/
theorem shareLe_of_box_at (Rt : Route) (hRt : @RouteOK Rt) {m : ℕ} (bx : Fin (m + 1) → Cell)
    (hlo : ∀ i, 0 < (bx i).1) (hle : ∀ i, (bx i).1 ≤ (bx i).2) (hfit : ∑ i, (bx i).2 ≤ DEN) {B : ℝ}
    (hB : (omKw (∑ t : Fin m, (bx t.castSucc).1) (bx (Fin.last m)).1 (∑ i, ((bx i).2 - (bx i).1))
        ((bx (Fin.last m)).2 - (bx (Fin.last m)).1) : ℝ) / K *
      ((∏ t : Fin m, trB (bx t.castSucc).1 ((bx t.castSucc).2 - (bx t.castSucc).1)) *
        exB (bx (Fin.last m)).1 ((bx (Fin.last m)).2 - (bx (Fin.last m)).1)) ≤ B) : @ShareLe Rt m bx B :=
  @shareLe_of_box Rt hRt m bx hlo hle hfit B hB

end SieveAd

#print axioms SieveAd.shareLe_of_box_at
#print axioms SieveAd.froz_weight_le_at
#print axioms SieveAd.bd_flip_neg_at
#print axioms SieveAd.bd_flip_pos_at
