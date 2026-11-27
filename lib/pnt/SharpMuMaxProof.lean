import SharpRangeCert
import SourceMuMaxTw

/-!
# The maximal slope of the integral forms: `SharpMuMax`

`ZetaBalance.sharpMuMax`: eventually in the design (at every admissible design), at every translate, the
construction's lattice of integral forms `M_ω` has `μ_max(M_ω) ≤ B` in every realising frame, with
`B + c_F^{exact} ≤ x^{4ε}Σ_t a_t/8`. Hence (R′) from small certificates alone (`sharpRange_of_certSmall`), and the
frame loss from (NI) and small certificates (`frameLoss_of_sharpNI_cert`). All slopes are in the archive's units.

* **The object** (`SharpObj.muMaxLe_of_tw`, the twin of `SharpObj.slopeFV_exact`): for an object whose sources are
  the whole cut (`X_c = ⊤`), with places of `SG` over the split primes `g₀ ≠ g₁`, antitone weights and a nonzero
  integer `m` in every place of every `ST_ω`, `μ_max(M_ω) ≤ 2n₀·negW(λ_ω)·log|m|` in every realising frame
  (`HermForms.slopeLe_source`: the twisted Petersson pairing, Theorems A and B).
* **The negative determinant twists** (`negW_sharpLam0_le`): `λ_{ρ,k−1} = u_{k−1} + k/2 − ½` (`wt0_eq`), which is
  `−b_t ≥ −2b′` at a top (`hcFam_u_top`, `Adm.bT_le`) and `k/2 − 1 ≥ 0` elsewhere (`hcFam_u_ntop`), so
  `negW(λ_0) ≤ |Φ|·2b′ ≤ 4x³·b′` (`card_Φ`, `card_le_cube`).
* **The budget** (`sharpMuMax`). With `m = T` (the auxiliary prime, in every place of `ST`), `n₀ = k ≤ 2x⁵`,
  `log T ≤ x` and `b′ = a/X′ ≤ A/x^{410}`, `A = Σ_t a_t`: `B = 2k·negW(λ_0)·log T ≤ 16x⁹·b′ ≤ 16A/x^{401} ≤ A`
  (`sharpB_le`). The proof of `cFx_le` gives `c_F^{exact} ≤ 0.036x^εA + 5A`, so `B + c_F^{exact} ≤ 0.036x^εA + 6A
  ≤ x^{4ε}A/8` as `x^ε ≥ 4096` (`add_cFx_le`).
-/

namespace ZetaBalance

open NumberField IsDedekindDomain HermForms

namespace SharpObj

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} {Dg : SharpDesign S κ x ε X} {C : SharpCoeff S}
  (b : SharpObj Dg C)

open Classical in
/-- (SP1) **`μ_max(M_ω)` for an object whose sources are the whole cut** (the twin of `slopeFV_exact`): with places
of `SG` over `g₀` and over `g₁` (trivial stabilisers), `X_c = ⊤`, antitone weights, an integer `m ≠ 0` in every place
of every `ST_ω`, and `B` at least every `2n₀·negW(λ_ω)·log|m|`, `μ_max(M_ω) ≤ B` in every realising frame. In the
frame's coordinates of the whole cut the lattice is the span of the integral forms and the metric is the Petersson
Gram matrix (`RealWith`), so `HermForms.slopeLe_source` applies. -/
theorem muMaxLe_of_tw (hg₀ : ∃ w : b.SG, (Dg.g₀ : 𝓞 S.E) ∈ w.1.asIdeal)
    (hg₁ : ∃ w : b.SG, (Dg.g₁ : 𝓞 S.E) ∈ w.1.asIdeal) (hXc : ∀ ω, b.Xc ω = ⊤)
    (hlam : ∀ ω ρ, Antitone (b.lam0 ω ρ)) {m : ℤ} (hm0 : m ≠ 0)
    (hm : ∀ ω, ∀ P ∈ b.ST ω, (m : 𝓞 S.E) ∈ P.asIdeal) {B : ℝ}
    (hB : ∀ ω, 2 * b.n0 * negW (b.lam0 ω) * Real.log |(m : ℝ)| ≤ B) : b.MuMaxLe B := by
  obtain ⟨w₀, h₀⟩ := hg₀
  obtain ⟨w₁, h₁⟩ := hg₁
  intro F c eC hF ω
  refine ⟨b.isLattice_map_M ω (hlam ω) (c ω), ?_⟩
  -- the frame's coordinates of the whole cut
  have hV : b.Xc ω ⊓ Vω (b.ST ω) C.τK (b.χ0 ω) (b.lam0 ω) = Vω (b.ST ω) C.τK (b.χ0 ω) (b.lam0 ω) := by
    rw [hXc, top_inf_eq]
  let c' := (LinearEquiv.ofEq _ _ hV).symm.trans ((b.e ω).symm.trans (c ω))
  have hc' (y : F.n ω → C.K) : (c'.symm y : Fn (b.ST ω) (ThetaChain.uniUT b.SG b.n0) (Φ S.A) C.K) =
      (b.e ω ((c ω).symm y) : Fn (b.ST ω) (ThetaChain.uniUT b.SG b.n0) (Φ S.A) C.K) := rfl
  refine (slopeLe_source C.τK (b.χ0 ω) (b.lam0 ω) (hlam ω) w₀ w₁ Dg.g₀_prime Dg.g₁_prime Dg.g₀_ne_g₁ h₀ h₁
    (HermClasses.uniAt_uniUT _) (HermClasses.uniAt_uniUT _) hm0 (hm ω) c' _ ?_ ?_).mono (hB ω)
  · -- the lattice: the integral forms of the cut, in the frame's coordinates
    show (b.M ω).map _ = _
    rw [M, Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      refine ⟨⟨_, (Submodule.mem_inf.1 (b.e ω φ).2).2⟩, hφ, ?_⟩
      have he : (LinearEquiv.ofEq _ _ hV).symm ⟨_, (Submodule.mem_inf.1 (b.e ω φ).2).2⟩ = b.e ω φ :=
        Subtype.ext rfl
      simp only [c', LinearEquiv.trans_apply, he, LinearEquiv.symm_apply_apply]
      rfl
    · rintro ⟨G, hG, rfl⟩
      refine ⟨(b.e ω).symm (LinearEquiv.ofEq _ _ hV |>.symm G), ?_, by simp [c']⟩
      simpa using hG
  · -- the metric: the Petersson Gram matrix
    intro v i j
    rw [hc', hc']
    exact hF.2.2.2.2.1 ω v i j

end SharpObj

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ}

/-- (SP2) **The negative determinant twists of the step-0 weights are small**: `negW λ_0 ≤ 4x³·b′`, `b′ = a/X′`.
The last weight is `λ_{ρ,k−1} = u_{k−1} + k/2 − ½` (`wt0_eq`): `−b_t ≥ −2b′` at a top (`hcFam_u_top`,
`Adm.bT_le`), `k/2 − 1 ≥ 0` elsewhere (`hcFam_u_ntop`); and `|Φ| = 2|A| ≤ 2x³` (`card_Φ`, `card_le_cube`). -/
theorem negW_sharpLam0_le {Dg : SharpDesign S κ x ε X} (hA : Dg.Adm) (u : S.A) :
    (negW (sharpLam0 Dg u) : ℝ) ≤ 4 * x ^ 3 * scB' x ε := by
  obtain ⟨pr, hF⟩ := hA.fam
  have hk5 : 5 ≤ Dg.R.k := by have := Dg.R.m_add_three_le; have := Dg.R.two_le_m; omega
  have hb'0 := (scB'_pos ε hA.big.pos).le
  -- one place: `max(0, −λ_{ρ,k−1}) ≤ 2b′`
  have hρ (ρ : Φ S.A) : (((-WeylFock.detShift (sharpLam0 Dg u ρ)).toNat : ℕ) : ℝ) ≤ 2 * scB' x ε := by
    have hdet : WeylFock.detShift (sharpLam0 Dg u ρ) = sharpLam0 Dg u ρ ⟨Dg.R.k - 1, by omega⟩ := by
      simp [WeylFock.detShift, show 0 < Dg.R.k by omega]
    have hl : ((sharpLam0 Dg u ρ ⟨Dg.R.k - 1, by omega⟩ : ℤ) : ℝ) =
        ((Dg.hc u ρ).u ⟨Dg.R.k - 1, by omega⟩ : ℝ) + (Dg.R.k : ℝ) / 2 - 1 / 2 := by
      have h := congrArg (fun q : ℚ => (q : ℝ)) (Setting.Ranks.wt0_eq (Dg.hc u) (by rw [zero_mul, add_zero]) ρ
        ⟨Dg.R.k - 1, by omega⟩)
      have e : ((Dg.R.k - 1 : ℕ) : ℝ) = (Dg.R.k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
      push_cast at h
      rw [e] at h
      rw [show sharpLam0 Dg u = Dg.R.wt0 (Dg.hc u) (by rw [zero_mul, add_zero]) from rfl, h]
      ring
    have hneg : -((sharpLam0 Dg u ρ ⟨Dg.R.k - 1, by omega⟩ : ℤ) : ℝ) ≤ 2 * scB' x ε := by
      rw [hl]
      by_cases hpk : placeKind Dg.TT Dg.T2 u ρ = .top
      · have ek : (Dg.hc u ρ).u ⟨Dg.R.k - 1, by omega⟩ = -pr.bT ρ.2 - ((Dg.R.k : ℚ) - 1) / 2 := by
          rw [hF.hc_eq u]; exact (hcFam_u_top hF.hyp hpk).2
        have ek' : ((Dg.hc u ρ).u ⟨Dg.R.k - 1, by omega⟩ : ℝ) = -(pr.bT ρ.2 : ℝ) - ((Dg.R.k : ℝ) - 1) / 2 := by
          rw [ek]; push_cast; ring
        obtain ⟨-, b2⟩ := hA.bT_le hF ρ.2 (placeKind_eq_top.1 hpk).2
        rw [ek']
        linarith
      · have ek : (Dg.hc u ρ).u ⟨Dg.R.k - 1, by omega⟩ = -1 / 2 := by
          rw [hF.hc_eq u]; exact (hcFam_u_ntop hF.hyp hpk).2
        have ek' : ((Dg.hc u ρ).u ⟨Dg.R.k - 1, by omega⟩ : ℝ) = -1 / 2 := by
          rw [ek]; push_cast; ring
        have hK : (5 : ℝ) ≤ Dg.R.k := by exact_mod_cast hk5
        rw [ek']
        linarith
    rw [hdet]
    have e : (((-(sharpLam0 Dg u ρ ⟨Dg.R.k - 1, by omega⟩)).toNat : ℕ) : ℝ) =
        max (-((sharpLam0 Dg u ρ ⟨Dg.R.k - 1, by omega⟩ : ℤ) : ℝ)) 0 := by
      rw [show (((-(sharpLam0 Dg u ρ ⟨Dg.R.k - 1, by omega⟩)).toNat : ℕ) : ℝ) =
        (((-(sharpLam0 Dg u ρ ⟨Dg.R.k - 1, by omega⟩)).toNat : ℤ) : ℝ) from rfl, Int.toNat_eq_max]
      push_cast
      rfl
    rw [e]
    exact max_le hneg (by linarith)
  -- the sum over the places
  have hcard : (Fintype.card (Φ S.A) : ℝ) ≤ 2 * x ^ 3 := by
    rw [card_Φ, Nat.cast_mul, Nat.cast_ofNat]
    linarith [hA.toDesignAdm.card_le_cube]
  calc (negW (sharpLam0 Dg u) : ℝ) = ∑ ρ, (((-WeylFock.detShift (sharpLam0 Dg u ρ)).toNat : ℕ) : ℝ) := by
        rw [negW, Nat.cast_sum]
    _ ≤ ∑ _ρ : Φ S.A, 2 * scB' x ε := Finset.sum_le_sum fun ρ _ => hρ ρ
    _ = Fintype.card (Φ S.A) * (2 * scB' x ε) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 2 * x ^ 3 * (2 * scB' x ε) := mul_le_mul_of_nonneg_right hcard (by linarith)
    _ = 4 * x ^ 3 * scB' x ε := by ring

/-- **The bound `B` is small**: `B = 2k·negW(λ_0)·log T ≤ 16x⁹·b′ ≤ 16A/x^{401} ≤ A`, `A = Σ_t a_t`, with `k ≤ 2x⁵`
(`designK_le`), `negW(λ_0) ≤ 4x³·b′` (`negW_sharpLam0_le`), `0 ≤ log T ≤ x` (`log_sharpT_le`) and
`b′ = a/X′ ≤ A/x^{410}` (`X'_ge`, `scA_le_sum`). -/
theorem sharpB_le {Dg : SharpDesign S κ x ε X} (hA : Dg.Adm) (u : S.A) :
    2 * Dg.R.k * negW (sharpLam0 Dg u) * Real.log (sharpT Dg u) ≤ ∑ s ∈ Dg.TT, Dg.a s := by
  set A := ∑ s ∈ Dg.TT, Dg.a s
  have hx0 := hA.big.pos
  have hx := hA.big.x_ge
  have hk : (Dg.R.k : ℝ) ≤ 2 * x ^ 5 := by rw [hA.k_eq]; exact hA.big.designK_le.2
  have hN := negW_sharpLam0_le hA u
  have hT := log_sharpT_le hA u
  have hT0 : 0 ≤ Real.log (sharpT Dg u) := Real.log_natCast_nonneg _
  have hb'0 := (scB'_pos ε hA.big.pos).le
  -- `b′ ≤ A/x^{410}`
  have hX := hA.big.X'_ge
  have hx410 : 0 < x ^ 410 := pow_pos hx0 _
  have hb' : scB' x ε ≤ A / x ^ 410 := by
    rw [scB']
    calc scA x ε / scX' x ε ≤ scA x ε / x ^ 410 := div_le_div_of_nonneg_left (scA_pos ε hx0).le hx410 hX
      _ ≤ A / x ^ 410 := div_le_div_of_nonneg_right hA.scA_le_sum hx410.le
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun t ht => (Dg.a_pos t ht).le
  -- `16x⁹ ≤ x^{410}`
  have h16 : 16 * x ^ 9 ≤ x ^ 410 := by
    have e : x ^ 410 = x ^ 9 * x ^ 401 := by ring
    have h1 : (16 : ℝ) ≤ x ^ 401 := le_trans (by linarith) (le_self_pow₀ (by linarith) (by norm_num))
    rw [e]
    nlinarith [pow_pos hx0 9]
  calc 2 * Dg.R.k * negW (sharpLam0 Dg u) * Real.log (sharpT Dg u)
      ≤ 2 * (2 * x ^ 5) * (4 * x ^ 3 * scB' x ε) * x := by
        refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) hN (Nat.cast_nonneg _)
          (by positivity)) hT hT0 (by positivity)
    _ = 16 * x ^ 9 * scB' x ε := by ring
    _ ≤ 16 * x ^ 9 * (A / x ^ 410) := mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = 16 * x ^ 9 / x ^ 410 * A := by ring
    _ ≤ 1 * A := mul_le_mul_of_nonneg_right ((div_le_one hx410).2 h16) hA0
    _ = A := one_mul A

/-- **The budget of (F) with room**: for `B ≤ A = Σ_t a_t`, `B + c_F^{exact} ≤ x^{4ε}A/8`. The proof of `cFx_le`:
`c_F^{exact} ≤ 36A·log x + 4A + A ≤ 0.036x^εA + 5A`, and `6A ≤ x^εA/500` as `x^ε ≥ 4096`. -/
theorem add_cFx_le {Dg : SharpDesign S κ x ε X} (hA : Dg.Adm) (u : S.A) {B : ℝ}
    (hB : B ≤ ∑ s ∈ Dg.TT, Dg.a s) :
    B + HermForms.cFx Dg.R.k (sharpLam0 Dg u) (sharpST Dg u) ≤ x ^ (4 * ε) * (∑ s ∈ Dg.TT, Dg.a s) / 8 := by
  unfold HermForms.cFx
  set A := ∑ s ∈ Dg.TT, Dg.a s
  set L := ∑ P ∈ sharpST Dg u, Real.log (Ideal.absNorm P.asIdeal : ℝ)
  have hx0 := hA.big.pos
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun t ht => (Dg.a_pos t ht).le
  -- the weights
  have hp : Dg.PinnedTo u (Dg.hc u) := fun _ => ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  have hk0 : Dg.R.k = Dg.R.k + 0 * (Dg.R.t + 1) := by rw [zero_mul, add_zero]
  have hν : ((∑ ρ, ∑ i, WeylFock.natW (sharpLam0 Dg u ρ) i : ℕ) : ℝ) ≤ 2 * A := hA.sum_natW_le hp hk0
  have hlam : max 0 (∑ ρ, ∑ i, (sharpLam0 Dg u ρ i : ℝ)) ≤ 2 * A := hA.sum_wt0_le hp hk0
  -- the ranks
  have hlk := hA.log_k_le
  have hlx := hA.log_le
  have hk1 : (1 : ℝ) ≤ Dg.R.k := by rw [hA.k_eq]; exact hA.big.designK_le.1
  have hlk0 : 0 ≤ Real.log Dg.R.k := Real.log_nonneg hk1
  have hxk : x ≤ Dg.R.k := by
    rw [hA.k_eq]
    refine le_trans ?_ (designK_mem hA.big).1
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ (9 / 2 + 10 * ε) := Real.rpow_le_rpow_of_exponent_le hA.big.one_lt.le (by linarith [hA.big.ε_pos])
  have hxe : 4096 ≤ x ^ ε := hA.big.le_rpow (by linarith [hA.big.ε_pos])
  have hx4 : x ^ ε ≤ x ^ (4 * ε) := Real.rpow_le_rpow_of_exponent_le hA.big.one_lt.le (by linarith [hA.big.ε_pos])
  -- the places of `ST`
  obtain ⟨hcard, hsum⟩ := sum_log_absNorm_le (ST := sharpST Dg u) (sharpT_prime Dg u).ne_zero fun P hP =>
    natCast_mem_of_conj_normPi_mem (mem_of_mem_placesOf hP)
  have hn0 : (0 : ℝ) < Module.finrank ℚ S.E := Nat.cast_pos.2 Module.finrank_pos
  have hnx : (Module.finrank ℚ S.E : ℝ) * x ≤ A := (le_div_iff₀ hx0).1 hA.card_E_le
  have hT := log_sharpT_le hA u
  have hLx : L ≤ Module.finrank ℚ S.E * x := hsum.trans (mul_le_mul_of_nonneg_left hT hn0.le)
  have hL0 : 0 ≤ L := le_trans (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg one_le_two)) hcard
  -- the three terms
  have t1 : ((∑ ρ, ∑ i, WeylFock.natW (sharpLam0 Dg u ρ) i : ℕ) : ℝ) * Real.log Dg.R.k ≤
      2 * A * (6 * Real.log x) := mul_le_mul hν hlk hlk0 (by positivity)
  have t1' : A * Real.log x ≤ A * (x ^ ε / 1000) := mul_le_mul_of_nonneg_left hlx hA0
  have t2 : 2 * max 0 (∑ ρ, ∑ i, (sharpLam0 Dg u ρ i : ℝ)) * L / (Dg.R.k * Module.finrank ℚ S.E) ≤ 4 * A := by
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul hlam (hLx.trans (mul_le_mul_of_nonneg_left hxk hn0.le)) hL0 (by positivity)
    linarith
  have t5 : A * 4096 ≤ A * x ^ ε := mul_le_mul_of_nonneg_left hxe hA0
  have t6 : A * x ^ ε ≤ A * x ^ (4 * ε) := mul_le_mul_of_nonneg_left hx4 hA0
  linarith

/-- (SP3) **`SharpMuMax`**, at every admissible design (`ε₁ = 1`, `x₀ = 0`): with `m = T` (`sharpT`, in every place
of `ST`, `natCast_mem_of_conj_normPi_mem`), `B = 2k·negW(λ_0)·log T` bounds `μ_max(M_ω)`
(`SharpObj.muMaxLe_of_tw`, with the places of `SG` over `g₀` and `g₁`, `exists_sharpSG`), and `B ≤ A`
(`sharpB_le`), so `B + c_F^{exact} ≤ x^{4ε}A/8` (`add_cFx_le`). -/
theorem sharpMuMax : SharpMuMax := by
  refine ⟨1, one_pos, fun ε _ _ => ⟨0, fun {S κ x X} Dg _ hA u _ => ?_⟩⟩
  obtain ⟨h₀, h₁⟩ := exists_sharpSG hA
  have hT0 : ((sharpT Dg u : ℤ)) ≠ 0 := by exact_mod_cast (sharpT_prime Dg u).ne_zero
  refine ⟨2 * Dg.R.k * negW (sharpLam0 Dg u) * Real.log (sharpT Dg u), add_cFx_le hA u (sharpB_le hA u), ?_⟩
  refine (sharpObj Dg u).muMaxLe_of_tw h₀ h₁ (fun _ => rfl) (fun _ => Setting.Ranks.wt0_antitone _ _) hT0
    (fun _ P hP => ?_) fun _ => le_of_eq ?_
  · rw [Int.cast_natCast]
    exact natCast_mem_of_conj_normPi_mem (mem_of_mem_placesOf hP)
  · rw [Int.cast_natCast, Nat.abs_cast]
    rfl

/-- (SP4) **(R′) from small certificates alone**: `sharpRange_of_cert` with `sharpMuMax`. -/
theorem sharpRange_of_certSmall (hC : SharpCertSmall) : SharpRange := sharpRange_of_cert sharpMuMax hC

/-- **The frame loss of the construction from (NI) and small certificates**: `frameLoss_of_sharpNI` with
`sharpRange_of_certSmall`. -/
theorem frameLoss_of_sharpNI_cert (hNI : SharpNI) (hC : SharpCertSmall) : EventuallyAdm (fun Dg => Dg.Adm)
    fun {S κ x ε X} (Dg : SharpDesign S κ x ε X) => ∀ u ∈ A₀ κ, ((sharpCons Dg).obj u).FrameLoss :=
  frameLoss_of_sharpNI hNI (sharpRange_of_certSmall hC)

end ZetaBalance
