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

end ModEpsteinBox
