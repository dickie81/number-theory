/-
# The dilations of the ball orbit are unitary, and have no wandering vector

Plain statement. Under RH the kernel `K_H` of `BallHadamard` is realized in `ℓ²` of the nontrivial zeros of `ζ`, with
multiplicity (`BallHadamard.realizationH`): `w_r = (r^ρ/|ρ|)_ρ`, `⟨w_m, w_n⟩ = √(mn)·K_H(m/n)`, and `φ_n` multiplies
the coordinate of `ρ` by `n^ρ`. On the line `n^ρ = √n·n^{iγ}`, so the normalized dilation `U_p = φ_p/√p` multiplies
the coordinate of `ρ` by the phase `p^{iγ}`.
* **The dilation flow** (`dil`, a definition; `dil_apply`, `dil_add`, `dil_zpow`): for real `t`, `U(t)` multiplies the
  coordinate of `ρ = β + iγ` by `e^{iγt}`. It is a linear isometry equivalence of `ℓ²` (a unitary), with no
  hypothesis, and `t ↦ U(t)` is a group homomorphism: `U(s + t) = U(s)U(t)`, `U(t)^k = U(kt)` for every `k ∈ ℤ`. Its
  eigenvectors are the basis vectors, with eigenvalues `e^{iγt}` (`dil_single`): pure point spectrum.
* **`U_p` on the orbit, under RH** (`Up`, a definition; `Up_eq_phi`, `Up_orbit`, `inner_orbit`): `U_p = U(log p)` is
  `φ_p/√p`, so `U_p(w_r) = w_{pr}/√p`, and `⟨w_m, w_n⟩ = G(m, n) = √(mn)·K_H(m/n)`, the Gram matrix of `BallWeil`.
* **No wandering vector** (`weights_eq_zero`, `not_wandering_zpow`, `not_wandering`, `Up_not_wandering`): for every real
  `t` there is no nonzero `x` with `⟨U(t)^k x, x⟩ = 0` for every `k ≥ 1` (equivalently, every `k ≠ 0` in `ℤ`). So no
  `U_p` is a shift on any nonzero subspace: the Wold decomposition of `U_p` has no shift part, and the discrete orbit
  space carries no one-way arrow. The proof is Fejér's: with `a_ρ = |x_ρ|²` and `z_ρ = e^{iγt}`, the hypothesis
  makes `Σ_ρ a_ρ|Σ_{j<N}(z_ρ z̄_{ρ₀})^j|² = N‖x‖²`, while the term of `ρ₀` alone is `a_{ρ₀}N²`.
-/
import Mathlib
import BallWeil

open Real Complex Finset Filter ComplexConjugate WeilForm WeilTest
open scoped InnerProductSpace

noncomputable section

namespace BallUnitary

open BallLattice BallHadamard BallWeil

/-! ## No wandering vector for a discrete spectral measure -/

/-- **A discrete measure on the circle with vanishing Fourier coefficients is zero**: if `a ≥ 0` is summable and
`Σ_i a_i e^{iθ_i m} = 0` for every integer `m ≠ 0`, then every `a_i = 0`. The Fejér sum
`Σ_i a_i|Σ_{j<N} e^{i(θ_i − θ_{i₀})j}|²` is `N·Σ_i a_i`, and at least `a_{i₀}N²`. -/
theorem weights_eq_zero {ι : Type*} (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (θ : ι → ℝ)
    (h : ∀ m : ℤ, m ≠ 0 → ∑' i, (a i : ℂ) * cexp ((θ i * m : ℝ) * I) = 0) (i₀ : ι) : a i₀ = 0 := by
  set A := ∑' i, a i with hA
  set F : ι → ℕ → ℂ := fun i N => ∑ j ∈ range N, cexp (((θ i - θ i₀) * j : ℝ) * I) with hF
  have hE : ∀ (i : ι) (u : ℝ), ‖cexp ((u : ℂ) * I)‖ = 1 := fun i u => norm_exp_ofReal_mul_I u
  -- The Fejér sum, as a complex number.
  have hsum : ∀ N : ℕ, ∑' i, (a i : ℂ) * (F i N * conj (F i N)) = N * A := by
    intro N
    have hexp : ∀ i : ι, F i N * conj (F i N) = ∑ j ∈ range N, ∑ l ∈ range N,
        cexp (((θ i - θ i₀) * ((j : ℤ) - l : ℤ) : ℝ) * I) := by
      intro i
      simp only [hF, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      rw [← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      simp only [map_mul, conj_ofReal, conj_I]
      push_cast
      ring
    have hterm : ∀ j l : ℕ, ∑' i, (a i : ℂ) * cexp (((θ i - θ i₀) * ((j : ℤ) - l : ℤ) : ℝ) * I) =
        if j = l then (A : ℂ) else 0 := by
      intro j l
      have e : ∀ i, (a i : ℂ) * cexp (((θ i - θ i₀) * ((j : ℤ) - l : ℤ) : ℝ) * I) =
          cexp ((-(θ i₀ * ((j : ℤ) - l : ℤ)) : ℝ) * I) * ((a i : ℂ) * cexp ((θ i * ((j : ℤ) - l : ℤ) : ℝ) * I)) := by
        intro i
        rw [mul_left_comm, ← Complex.exp_add]
        congr 2
        push_cast
        ring
      simp_rw [e]
      rw [tsum_mul_left]
      split_ifs with hjl
      · subst hjl
        simp [hA, Complex.ofReal_tsum]
      · rw [h _ (by omega), mul_zero]
    have hsm : ∀ j l : ℕ, Summable fun i => (a i : ℂ) * cexp (((θ i - θ i₀) * ((j : ℤ) - l : ℤ) : ℝ) * I) :=
      fun j l => Summable.of_norm_bounded hs (fun i => le_of_eq (by
        rw [norm_mul, hE i, mul_one, Complex.norm_real, Real.norm_of_nonneg (ha i)]))
    simp_rw [hexp, Finset.mul_sum]
    rw [Summable.tsum_finsetSum (fun j _ => summable_sum fun l _ => hsm j l)]
    simp_rw [Summable.tsum_finsetSum (fun l _ => hsm _ l), hterm]
    simp only [Finset.sum_ite_eq, Finset.mem_range]
    rw [Finset.sum_ite_of_true (fun j hj => Finset.mem_range.1 hj)]
    simp
  -- The Fejér sum, as a real number.
  have hF2 : ∀ i N, F i N * conj (F i N) = ((‖F i N‖ ^ 2 : ℝ) : ℂ) := fun i N => by
    rw [Complex.mul_conj']; push_cast; rfl
  have hbound : ∀ i N, ‖F i N‖ ≤ N := fun i N => by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl fun j _ => hE i _]
    simp
  have hsR : ∀ N : ℕ, Summable fun i => a i * ‖F i N‖ ^ 2 := fun N =>
    (hs.mul_right ((N : ℝ) ^ 2)).of_nonneg_of_le (fun i => mul_nonneg (ha i) (sq_nonneg _))
      fun i => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound i N) 2) (ha i)
  have hreal : ∀ N : ℕ, ∑' i, a i * ‖F i N‖ ^ 2 = N * A := fun N => by
    have h1 := hsum N
    simp_rw [hF2, ← Complex.ofReal_mul, ← Complex.ofReal_tsum] at h1
    exact_mod_cast h1
  have hF0 : ∀ N, F i₀ N = N := fun N => by simp [hF]
  have hle : ∀ N : ℕ, a i₀ * (N : ℝ) ^ 2 ≤ N * A := fun N => by
    rw [← hreal N]
    have := (hsR N).le_tsum i₀ (fun i _ => mul_nonneg (ha i) (sq_nonneg _))
    rwa [hF0, Complex.norm_natCast] at this
  by_contra hne
  have hpos : 0 < a i₀ := lt_of_le_of_ne (ha i₀) (Ne.symm hne)
  obtain ⟨N, hN⟩ := exists_nat_gt (A / a i₀)
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (tsum_nonneg ha) hpos.le) hN
  have h1 := hle N
  have h2 : A < a i₀ * N := by rwa [div_lt_iff₀ hpos, mul_comm] at hN
  nlinarith

/-! ## The dilation flow -/

/-- The phase `e^{iγt}` of the zero `ρ = β + iγ`. -/
def phase (q : ZIdx) (t : ℝ) : ℂ := cexp (((zetaZeroFamily q).im * t : ℝ) * I)

lemma norm_phase (q : ZIdx) (t : ℝ) : ‖phase q t‖ = 1 := norm_exp_ofReal_mul_I _

lemma phase_add (q : ZIdx) (s t : ℝ) : phase q (s + t) = phase q s * phase q t := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma phase_zero (q : ZIdx) : phase q 0 = 1 := by simp [phase]

/-- Multiplication by the phases `e^{iγt}`, as a linear map of `ℓ²`. -/
def dilL (t : ℝ) : L2 →ₗ[ℂ] L2 where
  toFun x := ⟨fun q => phase q t * x q, memℓp_of_sq <| (summable_sq_of_mem x).congr fun q => by
    rw [norm_mul, norm_phase, one_mul]⟩
  map_add' x y := by
    ext q
    show phase q t * (x + y) q = phase q t * x q + phase q t * y q
    rw [lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c x := by
    ext q
    show phase q t * (c • x) q = c * (phase q t * x q)
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring

lemma dilL_apply (t : ℝ) (x : L2) (q : ZIdx) : dilL t x q = phase q t * x q := rfl

lemma dilL_add (s t : ℝ) (x : L2) : dilL (s + t) x = dilL s (dilL t x) := by
  ext q
  rw [dilL_apply, dilL_apply, dilL_apply, phase_add, mul_assoc]

lemma dilL_zero (x : L2) : dilL 0 x = x := by
  ext q
  rw [dilL_apply, phase_zero, one_mul]

/-- **The dilation `U(t)`**: multiplication of the coordinate of `ρ = β + iγ` by `e^{iγt}`, a linear isometry
equivalence (a unitary) of `ℓ²` of the zeros. -/
def dil (t : ℝ) : L2 ≃ₗᵢ[ℂ] L2 where
  toLinearEquiv := LinearEquiv.ofLinearMap (dilL t) (dilL (-t))
    (LinearMap.ext fun x => by
      show dilL t (dilL (-t) x) = x
      rw [← dilL_add, add_neg_cancel, dilL_zero])
    (LinearMap.ext fun x => by
      show dilL (-t) (dilL t x) = x
      rw [← dilL_add, neg_add_cancel, dilL_zero])
  norm_map' x := by
    show ‖dilL t x‖ = ‖x‖
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    refine tsum_congr fun q => ?_
    rw [dilL_apply, norm_mul, norm_phase, one_mul]

/-- `U(t)` multiplies the coordinate of `ρ` by `e^{iγt}`. -/
theorem dil_apply (t : ℝ) (x : L2) (q : ZIdx) : dil t x q = phase q t * x q := rfl

/-- **`U(s + t) = U(s)U(t)`**: the dilations are a one-parameter unitary group. -/
theorem dil_add (s t : ℝ) : dil (s + t) = dil s * dil t :=
  LinearIsometryEquiv.ext fun x => dilL_add s t x

/-- `t ↦ U(t)` as a homomorphism from `(ℝ, +)`. -/
def dilHom : Multiplicative ℝ →* (L2 ≃ₗᵢ[ℂ] L2) where
  toFun t := dil t.toAdd
  map_one' := LinearIsometryEquiv.ext fun x => dilL_zero x
  map_mul' s t := dil_add s.toAdd t.toAdd

/-- **`U(t)^k = U(kt)`** for every integer `k`. -/
theorem dil_zpow (t : ℝ) (k : ℤ) : dil t ^ k = dil (k * t) := by
  have h := map_zpow dilHom (Multiplicative.ofAdd t) k
  rw [← ofAdd_zsmul] at h
  simpa [dilHom, zsmul_eq_mul] using h.symm

open scoped Classical in
/-- **The spectrum of `U(t)` is pure point**: the basis vector of `ρ` is an eigenvector with eigenvalue `e^{iγt}`. -/
theorem dil_single (q : ZIdx) (t : ℝ) : dil t (lp.single 2 q 1) = phase q t • lp.single 2 q 1 := by
  ext i
  rw [dil_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply]
  rcases eq_or_ne i q with rfl | h
  · rfl
  · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero]

/-! ## No wandering vector -/

/-- `⟨U(t)^k x, x⟩ = Σ_ρ |x_ρ|²e^{−iγkt}`. -/
lemma inner_dil_zpow (t : ℝ) (k : ℤ) (x : L2) :
    ⟪(dil t ^ k) x, x⟫_ℂ = ∑' q, ((‖x q‖ ^ 2 : ℝ) : ℂ) * cexp ((-((zetaZeroFamily q).im * t) * k : ℝ) * I) := by
  rw [dil_zpow, lp.inner_eq_tsum]
  refine tsum_congr fun q => ?_
  rw [dil_apply, RCLike.inner_apply, map_mul, phase, ← Complex.exp_conj]
  have e : x q * conj (x q) = ((‖x q‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']; push_cast; rfl
  have e3 : conj ((((zetaZeroFamily q).im * (k * t) : ℝ) : ℂ) * I) =
      ((-((zetaZeroFamily q).im * t) * k : ℝ) : ℂ) * I := by
    rw [map_mul, conj_ofReal, conj_I]; push_cast; ring
  rw [e3]
  linear_combination (cexp (((-((zetaZeroFamily q).im * t) * k : ℝ) : ℂ) * I)) * e

/-- **`U(t)` has no wandering vector, over `ℤ`**: if `⟨U(t)^k x, x⟩ = 0` for every integer `k ≠ 0`, then `x = 0`. -/
theorem not_wandering_zpow (t : ℝ) (x : L2) (h : ∀ k : ℤ, k ≠ 0 → ⟪(dil t ^ k) x, x⟫_ℂ = 0) : x = 0 := by
  have hz := weights_eq_zero (fun q => ‖x q‖ ^ 2) (fun q => sq_nonneg _) (summable_sq_of_mem x)
    (fun q => -((zetaZeroFamily q).im * t)) (fun m hm => by rw [← inner_dil_zpow]; exact h m hm)
  ext q
  have := hz q
  simpa using this

/-- **`U(t)` has no wandering vector**: if `⟨U(t)^k x, x⟩ = 0` for every `k ≥ 1`, then `x = 0`. So `U(t)` is a shift
on no nonzero subspace, for every real `t`. -/
theorem not_wandering (t : ℝ) (x : L2) (h : ∀ k : ℕ, 0 < k → ⟪(dil t ^ k) x, x⟫_ℂ = 0) : x = 0 := by
  refine not_wandering_zpow t x fun k hk => ?_
  rcases lt_or_gt_of_ne hk with hk | hk
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = -k := ⟨(-k).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hn0 : 0 < n := by omega
    have h1 := h n hn0
    have e : ⟪(dil t ^ k) x, x⟫_ℂ = conj ⟪(dil t ^ (n : ℤ)) x, x⟫_ℂ := by
      rw [inner_conj_symm]
      have := ((dil t ^ (n : ℤ))).inner_map_map ((dil t ^ k) x) x
      have hx : (dil t ^ (n : ℤ)) ((dil t ^ k) x) = x := by
        show ((dil t ^ (n : ℤ)) * (dil t ^ k)) x = x
        rw [← zpow_add, hn, neg_add_cancel, zpow_zero]
        rfl
      rw [← this, hx]
    rw [e, zpow_natCast, h1, map_zero]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = k := ⟨k.toNat, Int.toNat_of_nonneg hk.le⟩
    rw [zpow_natCast]
    exact h n (by omega)

/-! ## The normalized dilation `U_p` on the orbit -/

/-- **`U_p = U(log p)`**: multiplication of the coordinate of `ρ` by `p^{iγ}`. -/
def Up (p : ℕ) : L2 ≃ₗᵢ[ℂ] L2 := dil (Real.log p)

/-- **`U_p` has no wandering vector**, for every `p`: no nonzero `x` has `⟨U_p^k x, x⟩ = 0` for every `k ≥ 1`. -/
theorem Up_not_wandering (p : ℕ) (x : L2) (h : ∀ k : ℕ, 0 < k → ⟪(Up p ^ k) x, x⟫_ℂ = 0) : x = 0 :=
  not_wandering _ x h

/-- **Under RH, `U_p = φ_p/√p`**: on the line `p^ρ = √p·p^{iγ}`. -/
theorem Up_eq_phi (hRH : RiemannHypothesis) {p : ℕ} (hp : 0 < p) (x : L2) :
    Up p x = ((Real.sqrt p)⁻¹ : ℂ) • phiL p x := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  ext q
  rw [Up, dil_apply, lp.coeFn_smul, Pi.smul_apply, phiL_apply, smul_eq_mul, ← mul_assoc]
  congr 1
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, (zetaZeroFamily q).im = γ := ⟨_, rfl⟩
  have hline : zetaZeroFamily q = 1 / 2 + (γ : ℂ) * I := by
    apply Complex.ext <;> simp [line_of_RH hRH q, hγ]
  have hsq : (Real.sqrt p : ℂ) = cexp ((Real.log p / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp0, ← Complex.ofReal_exp]
    congr 2
    ring
  have hs0 : (Real.sqrt p : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hp0).ne'
  rw [eq_inv_mul_iff_mul_eq₀ hs0, hsq, phase, pw, ← Complex.exp_add, hγ]
  congr 1
  rw [hline]
  push_cast
  ring

/-- The orbit vectors `w_r = (r^ρ/|ρ|)_ρ` of `BallHadamard.realizationH`. -/
abbrev wv : ℚ → L2 := wvOf cH summable_cH_sq

/-- **`U_p(w_r) = w_{pr}/√p`**, under RH. -/
theorem Up_orbit (hRH : RiemannHypothesis) {p : ℕ} (hp : 0 < p) {r : ℚ} (hr : 0 < r) :
    Up p (wv r) = ((Real.sqrt p)⁻¹ : ℂ) • wv (p * r) := by
  rw [Up_eq_phi hRH hp]
  congr 1
  exact (realizationH hRH).orbit p r hp hr

/-- **The orbit's Gram matrix**: under RH, `⟨w_m, w_n⟩ = G(m, n) = √(mn)·K_H(m/n)` (`BallWeil.gram`). -/
theorem inner_orbit (hRH : RiemannHypothesis) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ⟪wv m, wv n⟫_ℂ = (gram m n : ℂ) :=
  inner_w (realizationH hRH) hm hn

end BallUnitary
