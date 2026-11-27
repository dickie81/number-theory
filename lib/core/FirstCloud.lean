import FirstCloudDim

/-!
# The cloud step: from the flat weights to the actual top weights (L5, A-N15–N17)

Module 11 (`FirstCloud`) of the L5/L6 plan: the hypothesis `FirstAssembly.CloudStep` of the first local theorem, at
one orbit of an inert prime `p` in the setting `Unram`, from three classical inputs (`cloudStep`), and the first local
theorem with the cloud step discharged (`first_local''`).

**The inputs** (exact statements in the definitions).
* `CloudPair` (`FirstCloudPair`; Annex I's I5 with the contraction of N16): an equivariant, `∇_O`-integral contraction
  `V(λ) × V(μ*) → V(H⁺)` with top cloud vectors `s_b`, `s′_a`, `Con(F·s_b, s′_a) = δ_{ab}p^{κ_a}F·hw(fl₂)`,
  `κ_a ≤ E`, as many cloud vectors as the Weyl dimension of the middle entries.
* `HwSat` (`FirstCloudPair`; the domain half of Annex I's I6): `F·hw(ν₂) ∈ ∇_O ⇒ F ∈ ∇_O`.
* `WeylDim` (`FirstCloudDim`; Annex I's I8): `dim V(λ) = ∏_s dimW_k(λ_s)`.

**Main results.**
* *The cloud step* (`cloudStep`, N15): for `b′ > 0` and `k ≥ 2`, `FirstAssembly.CloudStep` with the cloud exponent
  `D_c = E`. Edge by edge (`goodSys_cloud`, N16–N17), good systems of sizes `n₁ ≥ (1 − κ₁)d(H)/g` and
  `n₂ ≥ (1 − κ₂)d(H⁺)/g` give one of size `m·r` at `λ` with `g·(n₁ − r + n₂) ≤ d(H⁺)`; with the dimensions
  (`cloud_dims`) `(1 − ε)d(λ) ≤ m·d(H) ≤ d(λ)` and `d(H⁺) ≤ e^ε·d(H) ≤ 2d(H)` (`ε = 12Nkc/b′ ≤ 1/9 < log 2`):
  `m·r ≥ m((1 − κ₁)d(H) − κ₂d(H⁺))/g ≥ (1 − κ₁ − 2κ₂ − ε)·d(λ)/g`.
* *The first local theorem* (`first_local''`): `OffTop.first_local'` with the hypothesis `CloudStep` replaced by the
  three inputs (`b′ > 0` and `k ≥ 3` are in `FirstHyp`).

**Readings of the planning statement.** `CloudStep` quantifies over the weights but not over `b′`, `a`: `cloudStep`
assumes `b′ > 0` (for `b′ ≤ 0` the fraction `12Nkc/b′` is not positive and the dimension count fails) and `k ≥ 2`,
both supplied by `FirstHyp`. The hypotheses `A_s + B_s + 4c + 1 ≤ 8a` and the exact value of `D_c` are not used: the
cloud exponents are bounded in `CloudPair` (Annex I: by `N·⌈(k − 1)²(log_p(8a + k) + 1)⌉ ≤ D_c`).
-/

namespace FirstCloud

open MvPolynomial WeylFock HermForms InertModel LocalLattice LocalRank FirstMeans FirstAssembly Finset

noncomputable section

section Step

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

/-- **The cloud step** (A-N15–N17): given the cloud pairing with exponents at most `D_c`, the saturation of highest
weight vectors and the Weyl dimension formula, `FirstAssembly.CloudStep` holds for `b′ > 0` and `k ≥ 2`. -/
theorem cloudStep (hU : Unram p n' W Qq O Kf ι σ j ϖ) (hk : 2 ≤ k) {TT : Finset (Fin n')} {c Dc : ℕ} {b' a : ℝ}
    (hb' : 0 < b') (hWD : WeylDim Kf n' k) (hCP : CloudPair O Kf p TT k c Dc) (hsat : HwSat O Kf n' k) :
    CloudStep W k p ι σ ϖ TT c Dc b' a := by
  intro lam0 A B t c₂ D₁ κ₁ κ₂ hsh hz hcond hε h4 h2 hκ₁0 hκ₁1 hκ₂0 hR1 hR2 L'' L he
  have hA : ∀ s, b' / 3 ≤ (A s : ℝ) := fun s => (hcond s).1
  have hB : ∀ s, b' / 3 ≤ (B s : ℝ) := fun s => (hcond s).2.1
  have h3 : (0 : ℝ) < b' / 3 := by positivity
  have hA0 : ∀ s, 0 ≤ A s := fun s => by
    have : (0 : ℝ) ≤ A s := by linarith [hA s]
    exact_mod_cast this
  have hB0 : ∀ s, 0 ≤ B s := fun s => by
    have : (0 : ℝ) ≤ B s := by linarith [hB s]
    exact_mod_cast this
  obtain ⟨n₁, hn₁, hG₁⟩ := hR1 L'' L he
  obtain ⟨n₂, hn₂, hG₂⟩ := hR2 L'' L he
  obtain ⟨m, hm, r, hr, hcount, hG⟩ := goodSys_cloud hU hk hCP hsat hA0 hB0 hsh hz h4 h2 he hG₁ hG₂
  refine ⟨m * r, ?_, hG⟩
  obtain ⟨hD1, hD2, hD3⟩ := cloud_dims (Kf := Kf) hk hWD hb' hA hB hsh hz
  set ε : ℝ := 12 * (TT.card : ℝ) * k * c / b' with hεdef
  set cl : ℝ := ((∏ x ∈ TT, ∏ i : Fin k, ∏ j ∈ Ioi i, midFac (lam0 x) i j : ℚ) : ℝ) with hcldef
  set dL : ℝ := (dimV Kf lam0 : ℝ)
  set dH : ℝ := (dimV Kf (flatWt (k := k) TT A B) : ℝ)
  set dP : ℝ := (dimV Kf (flatWt (k := k) TT (A + fun _ => 2 * (c : ℤ)) (B + fun _ => 2 * (c : ℤ))) : ℝ)
    with hdPdef
  set g : ℝ := (gE p n' k : ℝ) with hgdef
  have hg : 0 < g := by
    rw [hgdef]
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_gE hU (k := k) (by omega))
  have hmc : (m : ℝ) = cl := by rw [hcldef, ← hm]; norm_cast
  have hcl0 : 0 ≤ cl := hmc ▸ Nat.cast_nonneg m
  have hdL0 : 0 ≤ dL := Nat.cast_nonneg _
  have hdH0 : 0 ≤ dH := Nat.cast_nonneg _
  -- the count at the edge
  have hcR : g * ((n₁ : ℝ) - r + n₂) ≤ dP := by
    have h' : ((nEdges (n' := n') p 1 L * (n₁ - r + n₂) : ℕ) : ℝ) ≤ dP := by
      rw [hdPdef]
      exact_mod_cast hcount
    rw [nEdges_eq_gE hU he.1] at h'
    push_cast [Nat.cast_sub hr] at h'
    exact h'
  -- the fraction `ε`
  have hε0 : 0 ≤ ε := by positivity
  have he2 : Real.exp ε ≤ 2 := by
    calc Real.exp ε ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 (hε.trans (by linarith [Real.log_two_gt_d9]))
      _ = 2 := Real.exp_log two_pos
  have h1e : (1 - ε) * dL ≤ cl * dH := by
    have hx : Real.exp (-ε) * dL ≤ cl * dH := by
      have := mul_le_mul_of_nonneg_left hD2 (Real.exp_nonneg (-ε))
      rwa [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at this
    nlinarith [Real.add_one_le_exp (-ε)]
  have hP2 : dP ≤ 2 * dH := hD3.trans (mul_le_mul_of_nonneg_right he2 hdH0)
  -- the sizes
  have s1 : (1 - κ₁) * dH ≤ n₁ * g := by rwa [div_le_iff₀ hg] at hn₁
  have s2 : (1 - κ₂) * dP ≤ n₂ * g := by rwa [div_le_iff₀ hg] at hn₂
  have s3 : (1 - κ₁) * dH - κ₂ * dP ≤ g * r := by nlinarith
  have s4 : (1 - κ₁ - ε) * dL ≤ cl * ((1 - κ₁) * dH) := by
    have := mul_le_mul_of_nonneg_left h1e (show 0 ≤ 1 - κ₁ by linarith)
    nlinarith [mul_nonneg (mul_nonneg hκ₁0 hε0) hdL0]
  have s5 : cl * (κ₂ * dP) ≤ 2 * κ₂ * dL := by
    have := mul_le_mul_of_nonneg_left hP2 (mul_nonneg hcl0 hκ₂0)
    have := mul_le_mul_of_nonneg_left hD1 (show 0 ≤ 2 * κ₂ by linarith)
    nlinarith
  have s6 : cl * ((1 - κ₁) * dH - κ₂ * dP) ≤ cl * (g * r) := mul_le_mul_of_nonneg_left s3 hcl0
  rw [div_le_iff₀ hg]
  push_cast
  rw [hmc]
  nlinarith

end Step

/-! ## The first local theorem with the cloud step discharged -/

/-- **The first local theorem (L5)** with the off-top step (`OffTop.offTop`) and the cloud step (`cloudStep`)
discharged: `FirstAssembly.first_local` from the inputs `FlatDim`, `HarmSplit`, `InputRank`, `SegMean`,
`κ_P ≤ C_P·N·N₁/Y` and the classical inputs of the cloud step, `WeylDim`, `CloudPair` (with exponents at most
`D_c = N·⌈k²λ_a⌉`) and `HwSat`. -/
theorem first_local'' (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (Ct CI CA CP : ℝ) (hCt : 0 ≤ Ct) (hCI : 0 ≤ CI) (hCA : 0 ≤ CA)
    (hCP : 0 ≤ CP) :
    ∃ CH C : ℝ, 0 < C ∧ ∀ (p n' k : ℕ) (TT : Finset (Fin n')) (G' N₁ : ℕ) (Y Yb a b' bl bu : ℝ) (c D cStar : ℕ),
      Even n' → 5 ≤ p → FirstHyp C₀ CH p n' k TT G' N₁ Y Yb a b' bl bu c D cStar →
      ∀ (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
        [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
        (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (ϖ : O), Unram p n' W Qq O Kf ι σ j ϖ →
      FlatDim Kf TT k → HarmSplit O Kf p TT k (uH TT.card k (lamA p k a)) (8 * a) →
      ∀ (κP : ℝ) (κT : Fin n' → (TT → ℤ) → (TT → ℤ) → ℝ),
        InputRank W k p ι σ ϖ TT (WAp k Y a c (Jsh C₀ N₁ k a b')) (WBp bl bu c (Jsh C₀ N₁ k a b'))
          (t0F Ct C₀ N₁ p TT k G' a b' c cStar) (c4F TT c cStar) (D0 CI TT.card Y N₁ k (lamA p k a)) κP κT →
        SegMean TT (WAp k Y a c (Jsh C₀ N₁ k a b')) (WBp bl bu c (Jsh C₀ N₁ k a b')) κT CA N₁ Y →
        κP ≤ CP * TT.card * N₁ / Y →
        WeylDim Kf n' k → CloudPair O Kf p TT k c (Dcl TT.card k (lamA p k a)) → HwSat O Kf n' k →
        ∃ κ : (TT → ℤ) → (TT → ℤ) → ℝ, (∀ aa bb, 0 ≤ κ aa bb) ∧ boxMean TT k Y a bl bu κ ≤ C * TT.card * N₁ / Y ∧
          ∀ (aw bw : Fin n' → ℤ) (lam0 : Fin n' → Fin k → ℤ), IsShape TT aw bw c lam0 →
            (∀ s ∈ TT, aw s ∈ aWin k Y a ∧ bw s ∈ bWin bl bu) →
            ∀ t : ℕ, depthI C (C₀ * N₁ ^ 2 * Real.log a) p n' k TT G' N₁ a b' c cStar aw bw ≤ t →
              ∀ L : Submodule W (Fin k → Qq), L.IsLattice Qq →
                LLPAt p 1 ι σ ϖ lam0 t D (κ (fun s => aw s) (fun s => bw s)) cStar L := by
  obtain ⟨CH, C, hC, h⟩ := OffTop.first_local' C₀ hC₀ Ct CI CA CP hCt hCI hCA hCP
  refine ⟨CH, C, hC, ?_⟩
  intro p n' k TT G' N₁ Y Yb a b' bl bu c D cStar hn' hp hF W Qq O Kf _ _ _ _ _ _ _ _ _ _ _ ι σ j ϖ hU hFD hHS κP κT
    hI1 hseg hκP hWD hCPair hsat
  have hk : 2 ≤ k := by have := hF.k_ge; omega
  exact h p n' k TT G' N₁ Y Yb a b' bl bu c D cStar hn' hp hF W Qq O Kf ι σ j ϖ hU hFD hHS κP κT hI1 hseg hκP
    (cloudStep hU hk hF.b_win.1 hWD hCPair hsat)

end

end FirstCloud
