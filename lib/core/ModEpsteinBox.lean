/-
# The Epstein zeta function of a rectangular lattice in `ℝ^d`

For `a : Fin d → ℝ` with every `aᵢ > 0`, the rectangular lattice `L_a = ⊕ᵢ aᵢℤ ⊂ ℝ^d` has covolume `∏ᵢ aᵢ` and dual
lattice `L_a* = L_{a⁻¹} = ⊕ᵢ aᵢ⁻¹ℤ`. Its theta function is `θ_a(t) = ∏ᵢ θ(aᵢ²t) = Σ_{v ∈ ℤ^d} e^{−πt|v|_a²}`,
`|v|_a² = Σᵢ aᵢ²vᵢ²`, with Jacobi's `θ = evenKernel 0`. This generalises `EpsteinFlat` (the case `d = 2`) to every
dimension; the general (non-rectangular) lattice needs `d`-dimensional Poisson summation, which is not built here.

* **Poisson duality** (`theta_inv`): `θ_a(1/t) = (t^{d/2}/covol)·θ_{a⁻¹}(t)`, from the one-variable functional
  equation in each coordinate.
* **The weak FE-pair** (`thetaFEPair`): `θ_a − 1` and `θ_{a⁻¹} − 1` decay faster than any power, so `(θ_a, θ_{a⁻¹})` is
  a weak FE-pair of weight `d/2` and root number `covol⁻¹`.
* **Continuation, functional equation and poles** (`Lambda`, `Lambda_functional_equation`, `differentiableAt_Lambda`,
  `Lambda_residue_zero`, `Lambda_residue_half_dim`, `hasMellin_theta`): the completed Epstein zeta function
  `Λ_a(s) = π^{−s}Γ(s)Z_a(s)` (on `Re s > d/2`, the Mellin transform of `θ_a − 1`) continues to `ℂ` with simple poles at
  `s = 0` (residue `−1`) and `s = d/2` (residue `covol⁻¹`) only, and
  `Λ_a(d/2 − s) = covol⁻¹·Λ_{a⁻¹}(s)`.
* **The lattice sum** (`hasSum_theta`, `summable_qa`, `hasSum_Lambda`): `θ_a(t) = Σ_{v ∈ ℤ^d}e^{−πt|v|_a²}`;
  `Σ'_v |v|_a^{−2σ}` converges for `σ > d/2` (by `|v|_a^{−2σ} ≤ C∏ᵢ(1 + vᵢ²)^{−σ/d}`); and on `Re s > d/2`,
  `Λ_a(s) = π^{−s}Γ(s)Σ'_v |v|_a^{−2s}` (Mathlib's `hasSum_mellin_pi_mul₀`).
-/
import Mathlib
import EpsteinFlat
import EpsteinHexagonal

open Real Complex Filter Topology Asymptotics Set MeasureTheory HurwitzZeta

noncomputable section

namespace ModEpsteinBox

variable {d : ℕ}

/-- The covolume `∏ᵢ aᵢ` of `L_a`. -/
def covol (a : Fin d → ℝ) : ℝ := ∏ i, a i

lemma covol_pos {a : Fin d → ℝ} (ha : ∀ i, 0 < a i) : 0 < covol a := Finset.prod_pos fun i _ => ha i

/-- **The theta function of the rectangular lattice `L_a`**, `θ_a(t) = ∏ᵢ θ(aᵢ²t)`. -/
def theta (a : Fin d → ℝ) (t : ℝ) : ℝ := ∏ i, evenKernel 0 (a i ^ 2 * t)

/-- **Poisson duality**: `θ_a(1/t) = (t^{d/2}/covol)·θ_{a⁻¹}(t)`. -/
theorem theta_inv {a : Fin d → ℝ} (ha : ∀ i, 0 < a i) {t : ℝ} (ht : 0 < t) :
    theta a (1 / t) = t ^ ((d : ℝ) / 2) / covol a * theta (fun i => (a i)⁻¹) t := by
  have h1 : ∀ i, evenKernel 0 (a i ^ 2 * (1 / t)) = √t / a i * evenKernel 0 ((a i)⁻¹ ^ 2 * t) := by
    intro i
    have hi := ha i
    have e : a i ^ 2 * (1 / t) = 1 / ((a i)⁻¹ ^ 2 * t) := by field_simp
    rw [e, EpsteinHexagonal.theta_inv (by positivity), Real.sqrt_mul (by positivity), inv_pow,
      Real.sqrt_inv, Real.sqrt_sq hi.le]
    field_simp
  unfold theta covol
  simp_rw [h1, Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le, show (1 / 2 : ℝ) * d = d / 2 by ring]

lemma continuousOn_theta (a : Fin d → ℝ) (ha : ∀ i, 0 < a i) : ContinuousOn (theta a) (Ioi 0) := by
  unfold theta
  refine continuousOn_finsetProd _ fun i _ => ?_
  exact (continuousOn_evenKernel 0).comp (continuous_const.mul continuous_id).continuousOn
    fun t (ht : 0 < t) => show 0 < a i ^ 2 * t by have := ha i; positivity

lemma locallyIntegrableOn_theta (a : Fin d → ℝ) (ha : ∀ i, 0 < a i) :
    LocallyIntegrableOn (fun t => (theta a t : ℂ)) (Ioi 0) :=
  (continuous_ofReal.comp_continuousOn (continuousOn_theta a ha)).locallyIntegrableOn measurableSet_Ioi

/-- A finite product of functions `1 + O(t^r)` (for every `r`) is `1 + O(t^r)`. -/
lemma isBigO_prod_sub {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ S, ∀ r : ℝ, (fun t => f i t - 1) =O[atTop] (· ^ r)) (r : ℝ) :
    (fun t => ∏ i ∈ S, f i t - 1) =O[atTop] (· ^ r) := by
  classical
  induction S using Finset.induction_on generalizing r with
  | empty => simp only [Finset.prod_empty, sub_self]; exact isBigO_zero _ _
  | insert j S hj ih =>
    have ih' := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hP : (fun t => ∏ i ∈ S, f i t) =O[atTop] fun _ => (1 : ℝ) := by
      have h1 := (ih' 0).congr_right fun t => Real.rpow_zero t
      exact (h1.add (isBigO_const_const (1 : ℝ) one_ne_zero atTop)).congr_left fun t => by ring
    have h := (((hf j (Finset.mem_insert_self j S) r).mul hP).congr_right fun t => mul_one _).add (ih' r)
    refine h.congr_left fun t => ?_
    rw [Finset.prod_insert hj]
    ring

lemma isBigO_theta_sub {a : Fin d → ℝ} (ha : ∀ i, 0 < a i) (r : ℝ) :
    (fun t => (theta a t : ℂ) - 1) =O[atTop] (· ^ r) := by
  have h : (fun t => theta a t - 1) =O[atTop] (· ^ r) := by
    refine isBigO_prod_sub Finset.univ (fun i t => evenKernel 0 (a i ^ 2 * t)) (fun i _ r => ?_) r
    have := EpsteinFlat.isBigO_evenKernel_sub (c := a i ^ 2) (by have := ha i; positivity) r
    exact this.congr_left fun t => by rw [mul_comm]
  exact (isBigO_ofReal_left.mpr h).congr_left fun t => by push_cast; ring

/-- **`(θ_a, θ_{a⁻¹})` is a weak FE-pair** of weight `d/2` and root number `covol⁻¹`. -/
def thetaFEPair (a : Fin d → ℝ) (ha : ∀ i, 0 < a i) (hd : 0 < d) : WeakFEPair ℂ where
  f t := (theta a t : ℂ)
  g t := (theta (fun i => (a i)⁻¹) t : ℂ)
  k := d / 2
  ε := ((covol a)⁻¹ : ℝ)
  f₀ := 1
  g₀ := 1
  hf_int := locallyIntegrableOn_theta a ha
  hg_int := locallyIntegrableOn_theta _ fun i => inv_pos.2 (ha i)
  hk := by positivity
  hε := by have := covol_pos ha; exact_mod_cast (inv_pos.2 this).ne'
  h_feq x hx := by
    show ((theta a (1 / x) : ℝ) : ℂ) =
      (((covol a)⁻¹ : ℝ) * ((x ^ ((d : ℝ) / 2) : ℝ) : ℂ)) • ((theta (fun i => (a i)⁻¹) x : ℝ) : ℂ)
    rw [theta_inv ha hx, smul_eq_mul]
    push_cast
    ring
  hf_top := isBigO_theta_sub ha
  hg_top := isBigO_theta_sub fun i => inv_pos.2 (ha i)

/-- **The completed Epstein zeta function of `L_a`**, `Λ_a(s) = π^{−s}Γ(s)Σ'_{ℓ ∈ L_a}|ℓ|^{−2s}`, defined for every `s`
as Mathlib's `WeakFEPair.Λ` of `θ_a`. -/
def Lambda (a : Fin d → ℝ) (ha : ∀ i, 0 < a i) (hd : 0 < d) (s : ℂ) : ℂ := (thetaFEPair a ha hd).Λ s

/-- **On `Re s > d/2`, `Λ_a(s)` is the Mellin transform** `∫₀^∞ (θ_a(t) − 1)t^s dt/t`. -/
theorem hasMellin_theta {a : Fin d → ℝ} (ha : ∀ i, 0 < a i) (hd : 0 < d) {s : ℂ} (hs : (d : ℝ) / 2 < s.re) :
    HasMellin (fun t => (theta a t : ℂ) - 1) s (Lambda a ha hd s) :=
  (thetaFEPair a ha hd).hasMellin (by simpa [thetaFEPair] using hs)

/-- **`Λ_a` is holomorphic off `s = 0` and `s = d/2`**. -/
theorem differentiableAt_Lambda {a : Fin d → ℝ} (ha : ∀ i, 0 < a i) (hd : 0 < d) {s : ℂ} (h0 : s ≠ 0)
    (h1 : s ≠ (d : ℂ) / 2) : DifferentiableAt ℂ (Lambda a ha hd) s :=
  (thetaFEPair a ha hd).differentiableAt_Λ (Or.inl h0) (Or.inl (by simpa [thetaFEPair] using h1))

/-- **The functional equation** `Λ_a(d/2 − s) = covol⁻¹·Λ_{a⁻¹}(s)`: `L_a ↔ L_a*`, `s ↔ d/2 − s`. -/
theorem Lambda_functional_equation {a : Fin d → ℝ} (ha : ∀ i, 0 < a i) (hd : 0 < d) (s : ℂ) :
    Lambda a ha hd ((d : ℂ) / 2 - s) =
      ((covol a)⁻¹ : ℝ) * Lambda (fun i => (a i)⁻¹) (fun i => inv_pos.2 (ha i)) hd s := by
  have h := (thetaFEPair a ha hd).functional_equation s
  have hsymm : (thetaFEPair a ha hd).symm.Λ = (thetaFEPair (fun i => (a i)⁻¹) (fun i => inv_pos.2 (ha i)) hd).Λ := by
    refine EpsteinFlat.Λ_congr (fun t _ => rfl) rfl ?_ rfl rfl
    simp only [WeakFEPair.symm, thetaFEPair, covol]
    rw [Finset.prod_inv_distrib, inv_inv]
    push_cast
    exact inv_inv _
  unfold Lambda
  rw [hsymm] at h
  simpa [thetaFEPair] using h

/-- **The pole at `s = 0`**: `sΛ_a(s) → −1`. -/
theorem Lambda_residue_zero {a : Fin d → ℝ} (ha : ∀ i, 0 < a i) (hd : 0 < d) :
    Tendsto (fun s => s * Lambda a ha hd s) (𝓝[≠] 0) (𝓝 (-1)) := by
  simpa [Lambda, thetaFEPair] using (thetaFEPair a ha hd).Λ_residue_zero

/-- **The pole at `s = d/2`**: `(s − d/2)Λ_a(s) → covol⁻¹`. -/
theorem Lambda_residue_half_dim {a : Fin d → ℝ} (ha : ∀ i, 0 < a i) (hd : 0 < d) :
    Tendsto (fun s => (s - (d : ℂ) / 2) * Lambda a ha hd s) (𝓝[≠] ((d : ℂ) / 2)) (𝓝 (((covol a)⁻¹ : ℝ) : ℂ)) := by
  simpa [Lambda, thetaFEPair] using (thetaFEPair a ha hd).Λ_residue_k

/-! ## The lattice sum -/

/-- `|v|_a² = Σᵢ aᵢ²vᵢ²`, the squared length of the lattice vector `(aᵢvᵢ)ᵢ ∈ L_a`. -/
def qa (a : Fin d → ℝ) (v : Fin d → ℤ) : ℝ := ∑ i, a i ^ 2 * (v i : ℝ) ^ 2

lemma qa_nonneg (a : Fin d → ℝ) (v : Fin d → ℤ) : 0 ≤ qa a v := Finset.sum_nonneg fun i _ => by positivity

lemma qa_eq_zero_iff {a : Fin d → ℝ} (ha : ∀ i, 0 < a i) (v : Fin d → ℤ) : qa a v = 0 ↔ v = 0 := by
  constructor
  · intro h
    rw [qa, Finset.sum_eq_zero_iff_of_nonneg fun i _ => by positivity] at h
    funext i
    have hi := h i (Finset.mem_univ i)
    have : (v i : ℝ) ^ 2 = 0 := by
      rcases mul_eq_zero.1 hi with h' | h'
      · exact absurd h' (by have := ha i; positivity)
      · exact h'
    exact_mod_cast pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  · rintro rfl; simp [qa]

/-- Products of nonnegative summable families over `ℤ` are summable over `ℤ^n`, with the product sum. -/
lemma hasSum_pi_prod {n : ℕ} (f : Fin n → ℤ → ℝ) (c : Fin n → ℝ) (h0 : ∀ i k, 0 ≤ f i k)
    (hf : ∀ i, HasSum (f i) (c i)) : HasSum (fun v : Fin n → ℤ => ∏ i, f i (v i)) (∏ i, c i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun i : Fin n => f (Fin.succ i)) (fun i : Fin n => c (Fin.succ i)) (fun i k => h0 _ k)
      (fun i => hf _)
    beta_reduce at ih'
    have hG0 : ∀ w : Fin n → ℤ, 0 ≤ ∏ i : Fin n, f (Fin.succ i) (w i) :=
      fun w => Finset.prod_nonneg fun i _ => h0 _ _
    have e : (fun v : Fin (n + 1) → ℤ => ∏ i, f i (v i)) ∘ (Fin.consEquiv fun _ => ℤ) =
        fun p : ℤ × (Fin n → ℤ) => f 0 p.1 * ∏ i : Fin n, f (Fin.succ i) (p.2 i) := by
      funext p
      simp only [Function.comp, Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero,
        Fin.cons_succ]
    rw [← (Fin.consEquiv fun _ => ℤ).hasSum_iff, e, Fin.prod_univ_succ]
    obtain ⟨F, hF⟩ : ∃ F, f 0 = F := ⟨_, rfl⟩
    obtain ⟨G, hG⟩ : ∃ G : (Fin n → ℤ) → ℝ, (fun w => ∏ i : Fin n, f (Fin.succ i) (w i)) = G := ⟨_, rfl⟩
    have hFs : HasSum F (c 0) := by rw [← hF]; exact hf 0
    have hGs : HasSum G (∏ i : Fin n, c (Fin.succ i)) := by rw [← hG]; exact ih'
    have hF0 : ∀ k, 0 ≤ F k := by rw [← hF]; exact h0 0
    have hG0' : ∀ w, 0 ≤ G w := by rw [← hG]; exact hG0
    have hm := HasSum.mul hFs hGs (Summable.mul_of_nonneg hFs.summable hGs.summable hF0 hG0')
    have hGw : ∀ w : Fin n → ℤ, ∏ i : Fin n, f (Fin.succ i) (w i) = G w := fun w => congrFun hG w
    simp_rw [hGw, hF]
    exact hm

/-- **`θ_a(t) = Σ_{v ∈ ℤ^d} e^{−πt|v|_a²}`**. -/
theorem hasSum_theta {a : Fin d → ℝ} (ha : ∀ i, 0 < a i) {t : ℝ} (ht : 0 < t) :
    HasSum (fun v : Fin d → ℤ => rexp (-π * qa a v * t)) (theta a t) := by
  have h := hasSum_pi_prod (fun i (n : ℤ) => rexp (-π * ((n : ℝ) + 0) ^ 2 * (a i ^ 2 * t)))
    (fun i => evenKernel 0 (a i ^ 2 * t)) (fun _ _ => (Real.exp_pos _).le)
    (fun i => hasSum_int_evenKernel 0 (by have := ha i; positivity))
  convert h using 1
  funext v
  rw [← Real.exp_sum, qa, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
  rfl

lemma summable_one_add_sq {e : ℝ} (he : 1 / 2 < e) : Summable fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ (-e) := by
  refine Summable.of_norm_bounded_eventually (summable_abs_int_rpow (b := 2 * e) (by linarith)) ?_
  filter_upwards [(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [Real.norm_of_nonneg (by positivity), show -(2 * e) = 2 * (-e) by ring, Real.rpow_mul (abs_nonneg _),
    show |(n : ℝ)| ^ (2 : ℝ) = (n : ℝ) ^ 2 by rw [Real.rpow_two, sq_abs]]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)

/-- The comparison `|v|_a^{−2σ} ≤ C∏ᵢ(1 + vᵢ²)^{−σ/d}` for `v ≠ 0`. -/
lemma qa_rpow_le {a : Fin d → ℝ} (ha : ∀ i, 0 < a i) (hd : 0 < d) {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, ∀ v : Fin d → ℤ, v ≠ 0 → qa a v ^ (-σ) ≤ C * ∏ i, (1 + (v i : ℝ) ^ 2) ^ (-(σ / d)) := by
  obtain ⟨j, -, hj⟩ := Finset.univ.exists_min_image (fun i => a i ^ 2) ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  set c := a j ^ 2
  have hc : 0 < c := by have := ha j; positivity
  refine ⟨(c / 2) ^ (-σ), fun v hv => ?_⟩
  set S := ∑ i, (v i : ℝ) ^ 2
  have hS : 1 ≤ S := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by by_contra h; push Not at h; exact hv (funext h)
    have h1 : (1 : ℝ) ≤ (v i : ℝ) ^ 2 := by
      have h := Int.one_le_abs hi
      have : (1 : ℝ) ≤ |(v i : ℝ)| := by exact_mod_cast h
      nlinarith [abs_nonneg (v i : ℝ), sq_abs (v i : ℝ)]
    exact h1.trans (Finset.single_le_sum (f := fun i => (v i : ℝ) ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ i))
  have hQ : c / 2 * (1 + S) ≤ qa a v := by
    have : c * S ≤ qa a v := by
      rw [qa, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hj i (Finset.mem_univ i)) (sq_nonneg _)
    nlinarith
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hprod : ∏ i, (1 + (v i : ℝ) ^ 2) ≤ (1 + S) ^ d := by
    calc ∏ i, (1 + (v i : ℝ) ^ 2) ≤ ∏ _i : Fin d, (1 + S) :=
          Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => by
            have := Finset.single_le_sum (f := fun i => (v i : ℝ) ^ 2) (fun i _ => sq_nonneg _)
              (Finset.mem_univ i)
            linarith
      _ = (1 + S) ^ d := by simp
  have h1 : (1 + S) ^ (-σ) ≤ ∏ i, (1 + (v i : ℝ) ^ 2) ^ (-(σ / d)) := by
    rw [Real.finsetProd_rpow _ _ fun i _ => by positivity]
    calc (1 + S) ^ (-σ) = ((1 + S) ^ d) ^ (-(σ / d)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          congr 1; field_simp
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos (Finset.prod_pos fun i _ => by positivity) hprod
          (by have : 0 ≤ σ / d := by positivity
              linarith)
  calc qa a v ^ (-σ) ≤ (c / 2 * (1 + S)) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hQ (by linarith)
    _ = (c / 2) ^ (-σ) * (1 + S) ^ (-σ) := Real.mul_rpow (by positivity) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- **Convergence**: `Σ'_{v} |v|_a^{−2σ} < ∞` for `σ > d/2`. -/
theorem summable_qa {a : Fin d → ℝ} (ha : ∀ i, 0 < a i) (hd : 0 < d) {σ : ℝ} (hσ : (d : ℝ) / 2 < σ) :
    Summable fun v : Fin d → ℤ => 1 / qa a v ^ σ := by
  have hσ0 : 0 < σ := lt_of_le_of_lt (by positivity) hσ
  obtain ⟨C, hC⟩ := qa_rpow_le ha hd hσ0
  have he : 1 / 2 < σ / d := by
    rw [lt_div_iff₀ (by exact_mod_cast hd)]; linarith
  have hP := (hasSum_pi_prod (n := d) (fun _ (n : ℤ) => (1 + (n : ℝ) ^ 2) ^ (-(σ / d))) _ (fun _ _ => by positivity)
    (fun _ => (summable_one_add_sq he).hasSum)).summable.mul_left C
  refine Summable.of_norm_bounded_eventually hP ?_
  filter_upwards [(Set.finite_singleton (0 : Fin d → ℤ)).compl_mem_cofinite] with v hv
  rw [Real.norm_of_nonneg (by have := qa_nonneg a v; positivity), one_div, ← Real.rpow_neg (qa_nonneg a v)]
  exact hC v hv

/-- **The Epstein zeta function as a lattice sum**: on `Re s > d/2`,
`Λ_a(s) = π^{−s}Γ(s)Σ'_{v ∈ ℤ^d}|v|_a^{−2s}` (the `v = 0` term `1/0^s` is `0`). -/
theorem hasSum_Lambda {a : Fin d → ℝ} (ha : ∀ i, 0 < a i) (hd : 0 < d) {s : ℂ} (hs : (d : ℝ) / 2 < s.re) :
    HasSum (fun v : Fin d → ℤ => (π : ℂ) ^ (-s) * Complex.Gamma s * 1 / (qa a v : ℂ) ^ s)
      (Lambda a ha hd s) := by
  have hs0 : 0 < s.re := lt_of_le_of_lt (by positivity) hs
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun v : Fin d → ℤ => if qa a v = 0 then 0
      else (1 : ℂ) * rexp (-π * qa a v * t)) ((theta a t : ℂ) - 1) := by
    intro t (ht : 0 < t)
    have h := (hasSum_ofReal.2 (hasSum_theta ha ht)).update 0 0
    convert h using 1
    · funext v
      rcases eq_or_ne v 0 with rfl | hv
      · simp [qa]
      · rw [Function.update_of_ne hv]
        simp [(qa_eq_zero_iff ha v).not.2 hv]
    · simp [qa]
      ring
  have hsum : Summable fun v : Fin d → ℤ => ‖(1 : ℂ)‖ / qa a v ^ s.re := by
    simpa using summable_qa ha hd hs
  have h := hasSum_mellin_pi_mul₀ (fun v => qa_nonneg a v) hs0 hF hsum
  rwa [(hasMellin_theta ha hd hs).2] at h

end ModEpsteinBox
