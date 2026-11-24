import Mathlib

/-!
# The frame inequality for slopes

A step of the library's proof of the Riemann hypothesis (`docs/rh-rebuild.md`, step 4): a frame version of Bost's
slope inequality, in the form that Alpöge's argument uses, proved from a few properties of slopes.

A lattice is seen through its saturated sublattices, a bounded lattice `L` with a strictly monotone rank `rk` and a
degree `deg` (for a hermitian lattice, `deg = rk·μ`, the normalised Arakelov degree). The properties used are:

* `SlopeGe a θ`: every quotient of `a` has slope at least `θ`, that is `μ_min(a) ≥ θ`;
* `SlopeLe λ`: every sublattice has slope at most `λ`, that is `μ_max ≤ λ`;
* `SupClosed`: the saturated sum of two sublattices of minimal slope at least `θ` has minimal slope at least `θ`. It
  holds when rank is modular and degree supermodular (`supClosed_of_modular`).

**The frame inequality** (`frame_inequality`). Sources `N_i` map to one target `C` with heights `h_i`. Suppose:

* **Bost's inequality** on images: `μ_min(img_i a) ≥ μ_min(a) − h_i`;
* the rank-weighted mean of `μ(N_i) − h_i` is at least `s`;
* `μ_max(N_i) − h_i ≤ s + u`;
* `μ_min(C) ≥ s − HH`;
* **rank spreading**: sublattices of total corank at most `ε'·Σ rk N_i` have images whose sum has corank at most
  `(α + β ε')·rk C`.

Then `μ(C) ≥ s − α·HH − β·u·log(1 + HH/u)`.

Proof:

1. **Steps.** At each level `τ ∈ [0, HH]`, and for `δ > 0`, take a sublattice `N_{i,τ}` maximising
   `deg − (s − τ + h_i − δ/2)·rk` up to `δ/2`. As ranks of strict sublattices drop by at least one, its minimal slope
   is at least `s − τ + h_i − δ`, and the quotient by it has slope at most `s − τ + h_i`, so
   `(u + τ)·corank ≤ rk·(s + u + h_i) − deg N_i`.
2. **Markov.** Summing gives total corank at most `u/(u + τ)·Σ rk N_i`.
3. **Images.** Bost's inequality and `SupClosed` give the image sum `M_τ` minimal slope at least `s − τ − δ`. Rank
   spreading bounds its corank.
4. **Abel summation.** Summing along a partition of `[0, HH]` into `K` steps, with cumulative sums, gives
   `μ(C) ≥ s − δ − Σ (τ_{k+1} − τ_k)·corank(M_{τ_k})/rk C`. Since `log(1 + x) ≥ x/(1 + x)`, this sum is at most
   `α·HH + β·u·log(1 + HH/u) + β·HH/K`, and `K` and `δ` are arbitrary.
-/

namespace SlopeFrame

/-- A lattice seen through its saturated sublattices: a bounded lattice with a degree and a strictly monotone rank. -/
structure SlopeLattice (L : Type*) [Lattice L] [BoundedOrder L] where
  rk : L → ℕ
  deg : L → ℝ
  rk_bot : rk ⊥ = 0
  deg_bot : deg ⊥ = 0
  rk_strictMono : StrictMono rk

namespace SlopeLattice

variable {L : Type*} [Lattice L] [BoundedOrder L] (X : SlopeLattice L)

/-- Rank is monotone. -/
theorem rk_mono : Monotone X.rk :=
  X.rk_strictMono.monotone

/-- Every quotient of `a` has slope at least `θ`: `μ_min(a) ≥ θ`. -/
def SlopeGe (a : L) (θ : ℝ) : Prop :=
  ∀ b ≤ a, θ * ((X.rk a : ℝ) - X.rk b) ≤ X.deg a - X.deg b

/-- Every sublattice has slope at most `λ`: `μ_max ≤ λ`. -/
def SlopeLe (lam : ℝ) : Prop :=
  ∀ b : L, X.deg b ≤ lam * X.rk b

/-- The sum of two sublattices of minimal slope at least `θ` has minimal slope at least `θ`. -/
def SupClosed : Prop :=
  ∀ (a b : L) (θ : ℝ), X.SlopeGe a θ → X.SlopeGe b θ → X.SlopeGe (a ⊔ b) θ

variable {X}

/-- `SlopeGe` is antitone in the slope. -/
theorem SlopeGe.anti {a : L} {θ θ' : ℝ} (h : X.SlopeGe a θ) (hθ : θ' ≤ θ) : X.SlopeGe a θ' := fun b hb =>
  (mul_le_mul_of_nonneg_right hθ (sub_nonneg.2 (Nat.cast_le.2 (X.rk_mono hb)))).trans (h b hb)

/-- **Approximate steps.** If `μ_max ≤ λ` and `θ ≤ λ`, then for `δ > 0` some `a` has minimal slope at least `θ − δ`,
while `⊤/a` has slope at most `θ`: take `a` maximising `deg − (θ − δ/2)·rk` up to `δ/2`, and use that ranks of
strict sublattices drop by at least one. -/
theorem SlopeLe.exists_step {lam θ δ : ℝ} (hX : X.SlopeLe lam) (hθ : θ ≤ lam) (hδ : 0 < δ) :
    ∃ a, X.SlopeGe a (θ - δ) ∧ X.deg ⊤ - X.deg a ≤ θ * (X.rk ⊤ - X.rk a) := by
  have : Nonempty L := ⟨⊥⟩
  have hB : BddAbove (Set.range fun b => X.deg b - (θ - δ / 2) * X.rk b) :=
    ⟨(lam - θ + δ / 2) * X.rk ⊤, Set.forall_mem_range.2 fun b => show _ - _ ≤ _ by
      nlinarith [hX b, Nat.cast_le (α := ℝ).2 (X.rk_mono (le_top : b ≤ ⊤))]⟩
  obtain ⟨a, ha⟩ : ∃ a, (⨆ b, X.deg b - (θ - δ / 2) * X.rk b) - δ / 2 < X.deg a - (θ - δ / 2) * X.rk a :=
    exists_lt_of_lt_ciSup (sub_lt_self _ (half_pos hδ))
  have hf (b : L) : X.deg b - (θ - δ / 2) * X.rk b ≤ ⨆ b, X.deg b - (θ - δ / 2) * X.rk b := le_ciSup hB b
  refine ⟨a, fun b hb => ?_, ?_⟩
  · obtain rfl | hb := hb.eq_or_lt
    · simp
    · have : (X.rk b : ℝ) + 1 ≤ X.rk a := by exact_mod_cast X.rk_strictMono hb
      nlinarith [hf b]
  · obtain rfl | ha' := (le_top : a ≤ ⊤).eq_or_lt
    · simp
    · have : (X.rk a : ℝ) + 1 ≤ X.rk ⊤ := by exact_mod_cast X.rk_strictMono ha'
      nlinarith [hf ⊤]

/-- **`SupClosed` from modularity.** If rank is modular and degree supermodular, sums of sublattices of minimal slope
at least `θ` have minimal slope at least `θ`. For `b ≤ a ⊔ a'`, put `c = a ⊔ b`: then `c/b` has the rank of
`a/(a ⊓ b)` and at least its degree, and so has `(a ⊔ a')/c` against `a'/(a' ⊓ c)`, since `a' ⊔ c = a ⊔ a'`. -/
theorem supClosed_of_modular (hrk : ∀ a b, X.rk (a ⊔ b) + X.rk (a ⊓ b) = X.rk a + X.rk b)
    (hdeg : ∀ a b, X.deg a + X.deg b ≤ X.deg (a ⊔ b) + X.deg (a ⊓ b)) : X.SupClosed := by
  intro a a' θ ha ha' b hb
  have hc : a' ⊔ (a ⊔ b) = a ⊔ a' := by rw [← sup_assoc, sup_comm a', sup_eq_left.2 hb]
  have r1 : (X.rk (a ⊔ b) : ℝ) + X.rk (a ⊓ b) = X.rk a + X.rk b := by exact_mod_cast hrk a b
  have r2 : (X.rk (a ⊔ a') : ℝ) + X.rk (a' ⊓ (a ⊔ b)) = X.rk a' + X.rk (a ⊔ b) := by
    exact_mod_cast hc ▸ hrk a' (a ⊔ b)
  have d2 := hdeg a' (a ⊔ b)
  rw [hc] at d2
  linear_combination ha _ inf_le_left + ha' _ inf_le_left + hdeg a b + d2 + θ * r1 + θ * r2

/-- A finite sup of elements of minimal slope at least `θ` has minimal slope at least `θ`. -/
theorem SupClosed.finset_sup (hX : X.SupClosed) {κ : Type*} {s : Finset κ} {f : κ → L} {θ : ℝ}
    (h : ∀ k ∈ s, X.SlopeGe (f k) θ) : X.SlopeGe (s.sup f) θ :=
  Finset.sup_induction (p := (X.SlopeGe · θ)) (fun b hb => by simp [le_bot_iff.1 hb])
    (fun a ha b hb => hX a b θ ha hb) h

/-- **Abel summation.** If `m k` has minimal slope at least `s − k·Δ` and corank at most `w k·rk ⊤`, and `⊤` has
minimal slope at least `s − K·Δ`, then `deg ⊤ ≥ (s − Σ_{k<K} Δ·w k)·rk ⊤`: the partial sups `m 0 ⊔ … ⊔ m (k − 1)`
are nested, and the slope inequalities between consecutive ones add up. -/
theorem SupClosed.abel (hX : X.SupClosed) {s Δ : ℝ} (hΔ : 0 ≤ Δ) {K : ℕ} (m : ℕ → L) (w : ℕ → ℝ)
    (hm : ∀ k, X.SlopeGe (m k) (s - k * Δ)) (hw : ∀ k, (X.rk ⊤ : ℝ) - X.rk (m k) ≤ w k * X.rk ⊤)
    (htop : X.SlopeGe ⊤ (s - K * Δ)) :
    (s - ∑ k ∈ Finset.range K, Δ * w k) * X.rk ⊤ ≤ X.deg ⊤ := by
  have key (k : ℕ) : (k * Δ - ∑ j ∈ Finset.range k, Δ * w j) * X.rk ⊤ ≤
      X.deg ((Finset.range k).sup m) - (s - k * Δ) * X.rk ((Finset.range k).sup m) := by
    induction k with
    | zero => simp [X.rk_bot, X.deg_bot]
    | succ k ih =>
      have hs : X.SlopeGe ((Finset.range (k + 1)).sup m) (s - k * Δ) :=
        hX.finset_sup fun j hj => (hm j).anti (by gcongr; exact Finset.mem_range_succ_iff.1 hj)
      have h1 := hs _ (Finset.sup_mono (Finset.range_subset_range.2 k.le_succ))
      have h2 : (X.rk (m k) : ℝ) ≤ X.rk ((Finset.range (k + 1)).sup m) :=
        Nat.cast_le.2 (X.rk_mono (Finset.le_sup (Finset.self_mem_range_succ k)))
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith [hw k]
  linarith [key K, htop ((Finset.range K).sup m) le_top]

end SlopeLattice

open SlopeLattice

/-- A left Riemann sum of `τ ↦ u/(u + τ)`: `Σ_{k ≤ n} Δ·u/(u + kΔ) ≤ Δ + u·log(1 + nΔ/u)`. Each term after the
first is at most the integral over the step before it, since `log(1 + x) ≥ x/(1 + x)`. -/
theorem sum_le_log {u Δ : ℝ} (hu : 0 < u) (hΔ : 0 ≤ Δ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Δ * (u / (u + k * Δ)) ≤ Δ + u * Real.log (1 + n * Δ / u) := by
  induction n with
  | zero => simp [hu.ne']
  | succ n ih =>
    have hA : 0 < 1 + n * Δ / u := by positivity
    have h1 := Real.log_le_sub_one_of_pos (div_pos hA (by positivity : 0 < 1 + (n + 1) * Δ / u))
    rw [Real.log_div hA.ne' (by positivity)] at h1
    have h2 : Δ * (u / (u + (n + 1) * Δ)) = u * (1 - (1 + n * Δ / u) / (1 + (n + 1) * Δ / u)) := by
      field_simp
      ring
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith

/-- **The frame inequality**: a frame of maps from sources of mean slope at least `s` into one target forces the
target's slope above `s`, up to the losses `α·HH + β·u·log(1 + HH/u)`. -/
theorem frame_inequality {ι : Type*} [Fintype ι] {L : ι → Type*} [∀ i, Lattice (L i)] [∀ i, BoundedOrder (L i)]
    (N : ∀ i, SlopeLattice (L i)) {M : Type*} [Lattice M] [BoundedOrder M] (C : SlopeLattice M)
    (img : ∀ i, L i → M) (h : ι → ℝ)
    (hbost : ∀ i (a : L i) (θ : ℝ), (N i).SlopeGe a θ → C.SlopeGe (img i a) (θ - h i))
    (hsup : C.SupClosed) (hC : 0 < C.rk ⊤)
    {s u HH α β : ℝ} (hu : 0 < u) (hHH : 0 ≤ HH) (hβ : 0 ≤ β)
    (hmean : s * ∑ i, ((N i).rk ⊤ : ℝ) ≤ ∑ i, ((N i).deg ⊤ - h i * (N i).rk ⊤))
    (hmax : ∀ i, (N i).SlopeLe (s + u + h i))
    (hmin : C.SlopeGe ⊤ (s - HH))
    (hspread : ∀ ε' : ℝ, 0 ≤ ε' → ε' ≤ 1 → ∀ a : ∀ i, L i,
      ∑ i, (((N i).rk ⊤ : ℝ) - (N i).rk (a i)) ≤ ε' * ∑ i, ((N i).rk ⊤ : ℝ) →
      (C.rk ⊤ : ℝ) - C.rk (Finset.univ.sup fun i => img i (a i)) ≤ (α + β * ε') * C.rk ⊤) :
    s - α * HH - β * u * Real.log (1 + HH / u) ≤ C.deg ⊤ / C.rk ⊤ := by
  have hc : (0 : ℝ) < C.rk ⊤ := Nat.cast_pos.2 hC
  -- Steps, Markov and images: at level `τ ≥ 0`, the sum of the images of approximate steps has minimal slope at
  -- least `s − δ − τ` and corank at most `(α + β·u/(u + τ))·rk C`.
  have level (δ τ : ℝ) (hδ : 0 < δ) (hτ : 0 ≤ τ) : ∃ m : M, C.SlopeGe m (s - δ - τ) ∧
      (C.rk ⊤ : ℝ) - C.rk m ≤ (α + β * (u / (u + τ))) * C.rk ⊤ := by
    choose a ha ha' using fun i => (hmax i).exists_step (θ := s - τ + h i) (by linarith) hδ
    refine ⟨Finset.univ.sup fun i => img i (a i), hsup.finset_sup fun i _ => (hbost i _ _ (ha i)).anti
      (by linarith), hspread _ (by positivity) ((div_le_one (by positivity)).2 (by linarith)) a ?_⟩
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
      show (u + τ) * (((N i).rk ⊤ : ℝ) - (N i).rk (a i)) + ((N i).deg ⊤ - h i * (N i).rk ⊤) ≤
        (s + u) * (N i).rk ⊤ by linarith [ha' i, hmax i (a i)]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  choose m hm hm' using level
  -- Abel summation along `τ_k = k·Δ` with `(n + 1)·Δ = HH`, then the logarithmic sum bound: the loss is `β·Δ + δ`.
  have key (n : ℕ) (Δ δ : ℝ) (hΔ : 0 ≤ Δ) (hK : (n + 1) * Δ = HH) (hδ : 0 < δ) :
      s - α * HH - β * u * Real.log (1 + HH / u) - C.deg ⊤ / C.rk ⊤ ≤ β * Δ + δ := by
    have h1 : (s - δ - ∑ k ∈ Finset.range (n + 1), Δ * (α + β * (u / (u + k * Δ)))) * C.rk ⊤ ≤ C.deg ⊤ :=
      hsup.abel hΔ (fun k => m δ (k * Δ) hδ (by positivity)) _ (fun k => hm _ _ _ _) (fun k => hm' _ _ _ _)
        (hmin.anti (by push_cast; linarith))
    rw [Finset.sum_congr rfl fun (k : ℕ) _ => show Δ * (α + β * (u / (u + k * Δ))) =
      α * Δ + β * (Δ * (u / (u + k * Δ))) by ring, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.mul_sum, ← le_div_iff₀ hc] at h1
    have h2 : β * ∑ k ∈ Finset.range (n + 1), Δ * (u / (u + k * Δ)) ≤ β * (Δ + u * Real.log (1 + HH / u)) := by
      gcongr
      refine (sum_le_log hu hΔ n).trans ?_
      gcongr
      linarith
    have h3 : ((n + 1 : ℕ) : ℝ) * (α * Δ) = α * HH := by push_cast; rw [← hK]; ring
    linarith
  -- Let `n → ∞`, with `δ = 1/(n + 1)`.
  exact sub_nonpos.1 ((ge_of_tendsto' (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (β * HH + 1)) fun n =>
    (key n (HH / (n + 1)) (1 / (n + 1)) (by positivity) (by field_simp) (by positivity)).trans_eq
      (by ring)).trans_eq (mul_zero _))

/-- **A frame**: words `ω`, each with a lattice of sublattices `N ω`, map into one target `C` by maps on sublattices
`img ω` of heights `h ω`. Bost's inequality holds on images, and sums of sublattices of `C` keep their minimal slope. -/
structure Frame where
  /-- The words. -/
  ι : Type
  [fintype : Fintype ι]
  /-- The sublattices of the source of each word. -/
  L : ι → Type
  [lattice : ∀ ω, Lattice (L ω)]
  [bounded : ∀ ω, BoundedOrder (L ω)]
  /-- The sources. -/
  N : ∀ ω, SlopeLattice (L ω)
  /-- The sublattices of the target. -/
  M : Type
  [latticeM : Lattice M]
  [boundedM : BoundedOrder M]
  /-- The target. -/
  C : SlopeLattice M
  /-- The images of sublattices. -/
  img : ∀ ω, L ω → M
  /-- The heights of the maps. -/
  h : ι → ℝ
  /-- Bost's inequality on images. -/
  bost : ∀ ω a θ, (N ω).SlopeGe a θ → C.SlopeGe (img ω a) (θ - h ω)
  /-- Sums of sublattices of `C` keep their minimal slope. -/
  supClosed : C.SupClosed
  /-- The target is not zero. -/
  rk_pos : 0 < C.rk ⊤

attribute [instance] Frame.fintype Frame.lattice Frame.bounded Frame.latticeM Frame.boundedM

/-- **Rank spreading** (RS) with constants `α` and `β`: sublattices of total corank at most `ε'·Σ rk N ω` have images
whose sum has corank at most `(α + β ε')·rk C`. -/
def Frame.RankSpread (F : Frame) (α β : ℝ) : Prop :=
  ∀ ε' : ℝ, 0 ≤ ε' → ε' ≤ 1 → ∀ a : ∀ ω, F.L ω,
    ∑ ω, (((F.N ω).rk ⊤ : ℝ) - (F.N ω).rk (a ω)) ≤ ε' * ∑ ω, ((F.N ω).rk ⊤ : ℝ) →
    (F.C.rk ⊤ : ℝ) - F.C.rk (Finset.univ.sup fun ω => F.img ω (a ω)) ≤ (α + β * ε') * F.C.rk ⊤

/-- The hypotheses of the frame inequality for a frame: the rank-weighted mean of `μ(N ω) − h ω` is at least `s`,
`μ_max(N ω) − h ω ≤ s + U`, `μ_min(C) ≥ s − H`, and the images spread their ranks with constants `α`, `β`. -/
structure Frame.Spread (F : Frame) (s U H α β : ℝ) : Prop where
  /-- The range is positive. -/
  U_pos : 0 < U
  /-- The depth is nonnegative. -/
  H_nonneg : 0 ≤ H
  /-- The spreading slope is nonnegative. -/
  β_nonneg : 0 ≤ β
  /-- The rank-weighted mean of `μ(N ω) − h ω` is at least `s`. -/
  mean : s * ∑ ω, ((F.N ω).rk ⊤ : ℝ) ≤ ∑ ω, ((F.N ω).deg ⊤ - F.h ω * (F.N ω).rk ⊤)
  /-- `μ_max(N ω) − h ω ≤ s + U`. -/
  range : ∀ ω, (F.N ω).SlopeLe (s + U + F.h ω)
  /-- `μ_min(C) ≥ s − H`. -/
  depth : F.C.SlopeGe ⊤ (s - H)
  /-- **Rank spreading** with constants `α` and `β`. -/
  spread : F.RankSpread α β

/-- **The frame inequality for a frame**: `μ(C) ≥ s − α·H − β·U·log(1 + H/U)`. -/
theorem Frame.Spread.loss_le {F : Frame} {s U H α β : ℝ} (h : F.Spread s U H α β) :
    s - α * H - β * U * Real.log (1 + H / U) ≤ F.C.deg ⊤ / F.C.rk ⊤ :=
  frame_inequality F.N F.C F.img F.h F.bost F.supClosed F.rk_pos h.U_pos h.H_nonneg h.β_nonneg h.mean h.range
    h.depth h.spread

end SlopeFrame

#print axioms SlopeFrame.frame_inequality
