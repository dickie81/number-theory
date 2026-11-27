import WeylDimPf
import FirstCloud

/-!
# Saturation of highest weight vectors (`FirstCloud.HwSat`) and the first local theorem with the cloud inputs

The domain half of Annex I's I6, an input of the cloud step (`FirstCloud.cloudStep`): over a discrete valuation ring
`O` with fraction field `Kf` of characteristic `0`, `F ∈ ∇_{Kf}(ν)` and `F·hw(ν₂) ∈ ∇_O(ν + ν₂)` give `F ∈ ∇_O(ν)`
(`hwSat`); hence the first local theorem with `FlatDim`, `WeylDim` and `HwSat` discharged, from `CloudPair` and the
inputs `HarmSplit`, `InputRank`, `SegMean`, `κ_P ≤ C_P·N·N₁/Y` (`first_local_cloud`).

**Standard monomial theory** (classically `∇_O(ν) = ∇_{Kf}(ν) ∩ O[x]`, with Gauss's lemma for `hw(ν₂)`). The block
products of the standard row path polynomials (`WeylDimPf.stdProd`) are a basis of `∇_K` over every field `K` of
characteristic `0` (`WeylDimPf.nabla_eq_span`) and stay independent over every field, the residue field included
(`WeylDimPf.stdProd_linearIndependent`). Each of them is a bideterminant with increasing rows (`stdProd_eq_bidet`:
a standard row path polynomial is the letter bideterminant at the sorted columns of its filling,
`pathPoly_eq_lbidet`), and the bideterminants are defined over `ℤ` (`bidetZ`, `map_bidetZ`).

**The saturation** (`hwSat_blocks`) runs Gauss's lemma and the saturation of `∇_O` at once, modulo the uniformiser:
with `F = Σ_f c_f·S_f` and `e` least with `ϖ^e c_f ∈ O` (`exists_pow_mul_mem`), `e ≥ 1` would give
`D·H = ϖ^e·A` in `O[x]` for `D = Σ_f ϖ^e c_f·S_f`, `H` the `O`-form of `hw(ν₂)` and `A` that of `F·hw(ν₂)`; over the
residue field `D̄·h̄w = 0` with `h̄w ≠ 0` (`WeylFock.eval_one_hw`), so `D̄ = 0` and all `ϖ^e c_f ∈ ϖO`, against the
minimality of `e`. The antitonicity of `ν₂` is not needed.
-/

namespace HwSatPf

open MvPolynomial Finset TwistedDegree PathBasis WeylFock WeylDimPf

noncomputable section

/-! ## Standard row path polynomials are bideterminants -/

section Std

variable {m : ℕ} {ν : Fin (m + 1) → ℕ}

/-- **The increasing enumeration of a set of `h` rows** (`0` if the set has another size). -/
def srt (J : Finset (Fin (m + 1))) (h : ℕ) : Fin h → Fin (m + 1) :=
  if hJ : J.card = h then J.orderEmbOfFin hJ else fun _ => 0

/-- **The minor at the increasing rows of `J`** is the wedge at `J` (`WeylDimPf.det_eq_wst`). -/
theorem det_srt {J : Finset (Fin (m + 1))} {h : ℕ} (hJ : J.card = h) :
    (Matrix.of fun i j : Fin h => (X (j.val, srt J h i) : MvPolynomial (ℕ × Fin (m + 1)) ℤ)).det =
      wst (fun t a => X (t, a)) h J := by
  have e : srt J h = J.orderEmbOfFin hJ := by unfold srt; rw [dite_eq_left hJ]
  rw [e]
  refine (det_eq_wst (fun t a => (X (t, a) : MvPolynomial (ℕ × Fin (m + 1)) ℤ)) h _
    (J.orderEmbOfFin hJ).strictMono).trans ?_
  rw [image_orderEmbOfFin_univ]

/-- **The rows of a filling**: the factor `(s, c)` reads the column `colOf (s, c)` in increasing order. -/
def rowsOf (ν : Fin (m + 1) → ℕ) (I : ℤ → Finset (Fin (m + 1))) :
    (s : Fin (m + 1)) → Fin (mult ν s) → Fin (s + 1) → Fin (m + 1) :=
  fun s c => srt (I (colOf ν ⟨s, c⟩)) (s + 1)

/-- **A standard filling is empty outside the columns `1, …, ν_0`.** -/
theorem std_eq_empty (hν : Antitone ν) {I : ℤ → Finset (Fin (m + 1))}
    (hI : IsStdFilling (FlatDimPf.muR ν (m + 1)) I) {c : ℤ} (hc : c ≤ 0 ∨ (ν 0 : ℤ) < c) : I c = ∅ := by
  have h := hI.1 c
  rw [colH_rowR_out hν hc] at h
  unfold colSet at h
  by_cases h0 : c ≤ 0
  · simp only [show ¬ 1 ≤ c by omega, h0, ite_false, ite_true, card_compl, Fintype.card_fin] at h
    have : (I c).card ≤ m + 1 := (card_le_univ _).trans (by simp)
    exact card_eq_zero.1 (by omega)
  · simp only [show 1 ≤ c by omega, h0, ite_false, ite_true] at h
    exact card_eq_zero.1 h

/-- **A standard row path polynomial is a letter bideterminant** with increasing rows (the converse of
`WeylDimPf.lbidet_mem`). -/
theorem pathPoly_eq_lbidet (hν : Antitone ν) {I : ℤ → Finset (Fin (m + 1))}
    (hI : IsStdFilling (FlatDimPf.muR ν (m + 1)) I) :
    pathPoly ℤ (FlatDimPf.muR ν) (m + 1) I = lbidet ℤ ν (rowsOf ν I) := by
  have key : ∏ c ∈ Icc (1 : ℤ) (ν 0), wst (fun t a => (X (t, a) : MvPolynomial (ℕ × Fin (m + 1)) ℤ))
      (colH (FlatDimPf.muR ν (m + 1)) c) (I c) =
      ∏ c ∈ colRange (FlatDimPf.PR hν).mu (m + 1), colK ℤ (FlatDimPf.muR ν) c (m + 1) (I c) := by
    refine prod_subset_one_on_sdiff (Icc_sub_colRange hν) (fun c hc => ?_) (fun c hc => ?_)
    · obtain ⟨-, hc⟩ := mem_sdiff.1 hc
      rw [mem_Icc, not_and_or, not_le, not_le] at hc
      have hout : c ≤ 0 ∨ (ν 0 : ℤ) < c := by omega
      rw [colK_rowR_out ℤ hν hout, std_eq_empty hν hI hout]
      simp [st0]
    · rw [colK_muR ℤ hν (mem_Icc.1 hc).1]
  rw [pathPoly, show colRange (FlatDimPf.muR ν) (m + 1) = colRange (FlatDimPf.PR hν).mu (m + 1) from rfl, ← key,
    prod_cols hν, lbidet]
  refine prod_congr rfl fun s _ => prod_congr rfl fun c _ => ?_
  have hc := colH_colOf hν ⟨s, c⟩
  have hcard : (I (colOf ν ⟨s, c⟩)).card = s + 1 := by
    have h := hI.1 (colOf ν ⟨s, c⟩)
    rwa [hc, colSet, ite_eq_left (colOf_mem hν _).1] at h
  rw [hc, rowsOf, det_srt hcard]

end Std

/-! ## Bideterminants over `ℤ` -/

section BidetZ

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ] {n : ℕ}

/-- **The bideterminants over `ℤ`** (`WeylFock.bidet` is defined over fields). -/
def bidetZ (ν : Φ → Fin n → ℕ) (rows : (τ : Φ) → (s : Fin n) → Fin (mult (ν τ) s) → Fin (s + 1) → Fin n) :
    MvPolynomial (Φ × Fin n × Fin n) ℤ :=
  ∏ τ, ∏ s : Fin n, ∏ c, ((Matrix.of fun a b => (X (τ, a, b) : MvPolynomial (Φ × Fin n × Fin n) ℤ)).submatrix
    (rows τ s c) (Fin.castLE s.isLt)).det

omit [DecidableEq Φ] in
/-- **The bideterminants over a field are the images of those over `ℤ`.** -/
theorem map_bidetZ (K : Type*) [Field K] (ν : Φ → Fin n → ℕ)
    (rows : (τ : Φ) → (s : Fin n) → Fin (mult (ν τ) s) → Fin (s + 1) → Fin n) :
    MvPolynomial.map (Int.castRingHom K) (bidetZ ν rows) = bidet K ν rows := by
  simp only [bidetZ, bidet, minor, map_prod, RingHom.map_det]
  refine prod_congr rfl fun τ _ => prod_congr rfl fun s _ => prod_congr rfl fun c _ => ?_
  congr 1
  refine Matrix.ext fun i j => ?_
  simp [xMat]

end BidetZ

/-- **The block products of standard row path polynomials are bideterminants** (over every field). -/
theorem stdProd_eq_bidet {K : Type*} [Field K] {Φ : Type} [Fintype Φ] [DecidableEq Φ] {m : ℕ}
    {ν : Φ → Fin (m + 1) → ℕ} (hν : ∀ b, Antitone (ν b))
    (f : ∀ b, {I // IsStdFilling (FlatDimPf.muR (ν b) (m + 1)) I}) :
    stdProd (K := K) ν f = bidet K ν (fun b => rowsOf (ν b) (f b).1) := by
  rw [bidet_eq_prod_emb, stdProd]
  refine prod_congr rfl fun b _ => ?_
  rw [← pathPoly_eq_lbidet (hν b) (f b).2, pathPoly_map]

/-! ## Saturation -/

section Sat

open InertModel

variable {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [IsFractionRing O Kf]

/-- **Clearing denominators by a uniformiser**: a power of `ϖ` makes every element of `Kf` integral. -/
theorem exists_pow_mul_mem {ϖ : O} (hϖ : Irreducible ϖ) (c : Kf) :
    ∃ e : ℕ, algebraMap O Kf ϖ ^ e * c ∈ Oint O Kf := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hϖ0 : algebraMap O Kf ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O Kf)).2 hϖ.ne_zero
  have hu1 : algebraMap O Kf (↑u⁻¹ : O) * algebraMap O Kf (↑u : O) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hu0 : algebraMap O Kf (↑u : O) ≠ 0 := right_ne_zero_of_mul_eq_one hu1
  refine ⟨e, a * ↑u⁻¹, ?_⟩
  rw [hu, map_mul, map_mul, map_pow]
  field_simp
  linear_combination (algebraMap O Kf a) * hu1

/-- **Highest weight vectors are saturated**, block by block: for an antitone shape `ν`, any `ν₂` and `F ∈ ∇_{Kf}(ν)`,
`F·hw(ν₂) ∈ ∇_O(ν + ν₂)` implies `F ∈ ∇_O(ν)`. Write `F = Σ_f c_f·S_f` in the standard basis (`nabla_le_span`;
`S_f` a bideterminant, `stdProd_eq_bidet`, defined over `ℤ`), and let `e` be least with `ϖ^e c_f ∈ O` for all `f`.
If `e ≥ 1`, `D = Σ_f ϖ^e c_f·S_f` and the `O`-form `H` of `hw(ν₂)` satisfy `D·H = ϖ^e·A` in `O[x]` (`A` the
`O`-combination of bideterminants giving `F·hw(ν₂)`), so `D̄·h̄w = 0` over the residue field: `h̄w ≠ 0` (its value at
the identity is `1`), hence `D̄ = 0`, every `ϖ^e c_f ∈ ϖO` by the independence of the `S̄_f` over the residue field
(`stdProd_linearIndependent`), contradicting the minimality of `e`. -/
theorem hwSat_blocks [CharZero Kf] {Φ : Type} [Fintype Φ] [DecidableEq Φ] {m : ℕ}
    {ν ν₂ : Φ → Fin (m + 1) → ℕ} (hν : ∀ b, Antitone (ν b)) {F : Pol Φ (m + 1) Kf} (hF : F ∈ nabla Kf ν)
    (hFh : F * hw Kf ν₂ ∈ nablaInt (Oint O Kf) (ν + ν₂)) :
    F ∈ nablaInt (Oint O Kf) ν := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hι : Function.Injective (algebraMap O Kf) := IsFractionRing.injective O Kf
  have hϖ0 : algebraMap O Kf ϖ ≠ 0 := (map_ne_zero_iff _ hι).2 hϖ.ne_zero
  have := fun b => finite_std (hν b)
  let _ : ∀ b, Fintype {I // IsStdFilling (FlatDimPf.muR (ν b) (m + 1)) I} := fun b => Fintype.ofFinite _
  -- `F` in the standard basis
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Kf).1 (nabla_le_span hν hF)
  -- the integer forms
  have hZ : ∀ (K : Type) [Field K] (f : ∀ b, {I // IsStdFilling (FlatDimPf.muR (ν b) (m + 1)) I}),
      MvPolynomial.map (Int.castRingHom K) (bidetZ ν fun b => rowsOf (ν b) (f b).1) = stdProd (K := K) ν f :=
    fun K _ f => by rw [map_bidetZ, stdProd_eq_bidet hν]
  have hOK : ∀ (K : Type) [Field K] (φ : O →+* K) (P : MvPolynomial (Φ × Fin (m + 1) × Fin (m + 1)) ℤ),
      MvPolynomial.map φ (MvPolynomial.map (Int.castRingHom O) P) = MvPolynomial.map (Int.castRingHom K) P :=
    fun K _ φ P => by
      rw [MvPolynomial.map_map, RingHom.ext_int (φ.comp (Int.castRingHom O)) (Int.castRingHom K)]
  -- it suffices that the coordinates are integral
  suffices hcO : ∀ f, c f ∈ Oint O Kf by
    rw [← hc]
    refine Submodule.sum_mem _ fun f _ => ?_
    rw [stdProd_eq_bidet hν, show c f • bidet Kf ν (fun b => rowsOf (ν b) (f b).1) =
      (⟨c f, hcO f⟩ : Oint O Kf) • bidet Kf ν (fun b => rowsOf (ν b) (f b).1) from rfl]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  -- the least power of `ϖ` clearing the denominators
  have hex : ∃ e, ∀ f, algebraMap O Kf ϖ ^ e * c f ∈ Oint O Kf := by
    choose e he using fun f => exists_pow_mul_mem (Kf := Kf) hϖ (c f)
    refine ⟨∑ f, e f, fun f => ?_⟩
    rw [← Nat.sub_add_cancel (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ f) : e f ≤ ∑ f, e f), pow_add,
      mul_assoc]
    exact (Oint O Kf).mul_mem (pow_mem (show algebraMap O Kf ϖ ∈ Oint O Kf from ⟨ϖ, rfl⟩) _) (he f)
  by_contra hnot
  obtain ⟨f₁, hf₁⟩ := not_forall.1 hnot
  set e := Nat.find hex with hedef
  have he0 : e ≠ 0 := fun h0 => by
    have h := Nat.find_spec hex f₁
    rw [← hedef, h0, pow_zero, one_mul] at h
    exact hf₁ h
  obtain ⟨f₀, hf₀⟩ : ∃ f, algebraMap O Kf ϖ ^ (e - 1) * c f ∉ Oint O Kf :=
    not_forall.1 (Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero he0) one_pos))
  choose d hd using Nat.find_spec hex
  -- the relation over `O`
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (Oint O Kf)).1 hFh
  choose a' ha' using fun r => (a r).2
  set D : MvPolynomial (Φ × Fin (m + 1) × Fin (m + 1)) O :=
    ∑ f, d f • MvPolynomial.map (Int.castRingHom O) (bidetZ ν fun b => rowsOf (ν b) (f b).1) with hDdef
  set H : MvPolynomial (Φ × Fin (m + 1) × Fin (m + 1)) O :=
    MvPolynomial.map (Int.castRingHom O) (bidetZ ν₂ fun _ s _ => Fin.castLE s.isLt) with hHdef
  set A : MvPolynomial (Φ × Fin (m + 1) × Fin (m + 1)) O :=
    ∑ r, a' r • MvPolynomial.map (Int.castRingHom O) (bidetZ (ν + ν₂) r) with hAdef
  have hDι : MvPolynomial.map (algebraMap O Kf) D = algebraMap O Kf ϖ ^ e • F := by
    rw [← hc, hDdef, map_sum, smul_sum]
    refine sum_congr rfl fun f _ => ?_
    rw [CapacitySpan.map_smul', hOK, hZ, hd f, smul_smul]
  have hHι : MvPolynomial.map (algebraMap O Kf) H = hw Kf ν₂ := by
    rw [hHdef, hOK, map_bidetZ, WeylSandwich.hw_eq_bidet]
  have hAι : MvPolynomial.map (algebraMap O Kf) A = F * hw Kf ν₂ := by
    rw [← ha, hAdef, map_sum]
    refine sum_congr rfl fun r _ => ?_
    rw [CapacitySpan.map_smul', hOK, map_bidetZ, ha' r]
    rfl
  have hrel : D * H = ϖ ^ e • A := by
    apply MvPolynomial.map_injective _ hι
    rw [map_mul, hDι, hHι, CapacitySpan.map_smul', hAι, map_pow, smul_mul_assoc]
  -- reduce modulo `ϖ`
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hπϖ : IsLocalRing.residue O ϖ = 0 :=
    (IsLocalRing.residue_eq_zero_iff ϖ).2 (by rw [hmax]; exact Ideal.mem_span_singleton_self ϖ)
  have hHπ : MvPolynomial.map (IsLocalRing.residue O) H = hw (IsLocalRing.ResidueField O) ν₂ := by
    rw [hHdef, hOK, map_bidetZ, WeylSandwich.hw_eq_bidet]
  have hDπ : MvPolynomial.map (IsLocalRing.residue O) D = 0 := by
    have h := congrArg (MvPolynomial.map (IsLocalRing.residue O)) hrel
    rw [map_mul, CapacitySpan.map_smul', map_pow, hπϖ, zero_pow he0, zero_smul, hHπ] at h
    refine (mul_eq_zero.1 h).resolve_right fun h0 => ?_
    have := eval_one_hw (Φ := Φ) (L := IsLocalRing.ResidueField O) ν₂
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hdπ : ∀ f, IsLocalRing.residue O (d f) = 0 := by
    have h : ∑ f, IsLocalRing.residue O (d f) • stdProd (K := IsLocalRing.ResidueField O) ν f = 0 := by
      rw [← hDπ, hDdef, map_sum]
      refine sum_congr rfl fun f _ => ?_
      rw [CapacitySpan.map_smul', hOK, hZ]
    exact Fintype.linearIndependent_iff.1 (stdProd_linearIndependent hν) _ h
  obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.1 (by
    rw [← hmax]
    exact (IsLocalRing.residue_eq_zero_iff _).1 (hdπ f₀))
  apply hf₀
  refine ⟨o, mul_left_cancel₀ hϖ0 ?_⟩
  rw [← map_mul, mul_comm ϖ o, ho, hd f₀, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero he0)]

/-- **`HwSat`** (`FirstCloud.HwSat`, the domain half of Annex I's I6) over a discrete valuation ring `O` with
fraction field `Kf` of characteristic `0`: `hwSat_blocks` on the blocks of one orbit. -/
theorem hwSat (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    [IsFractionRing O Kf] [CharZero Kf] {n' k : ℕ} (hk : 1 ≤ k) : FirstCloud.HwSat O Kf n' k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  intro ν ν₂ hν _ F hF hFh
  exact hwSat_blocks hν hF hFh

end Sat

/-! ## The first local theorem with the cloud inputs `WeylDim`, `HwSat` (and `FlatDim`) discharged -/

section FirstLocal

open HermForms InertModel LocalLattice LocalRank FirstMeans FirstAssembly FirstCloud

/-- **The first local theorem (L5)** with `FlatDim` (`FlatDimPf.flatDim`), `WeylDim` (`WeylDimPf.weylDim`) and
`HwSat` (`hwSat`) discharged: `FirstCloud.first_local''` from the inputs `HarmSplit`, `InputRank`, `SegMean`,
`κ_P ≤ C_P·N·N₁/Y` and the cloud pairing `CloudPair` alone (`k ≥ 3` is in `FirstHyp`; `Kf` is the fraction field
of `O` in `Unram`). -/
theorem first_local_cloud (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (Ct CI CA CP : ℝ) (hCt : 0 ≤ Ct) (hCI : 0 ≤ CI) (hCA : 0 ≤ CA)
    (hCP : 0 ≤ CP) :
    ∃ CH C : ℝ, 0 < C ∧ ∀ (p n' k : ℕ) (TT : Finset (Fin n')) (G' N₁ : ℕ) (Y Yb a b' bl bu : ℝ) (c D cStar : ℕ),
      Even n' → 5 ≤ p → FirstHyp C₀ CH p n' k TT G' N₁ Y Yb a b' bl bu c D cStar →
      ∀ (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
        [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
        (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (ϖ : O), Unram p n' W Qq O Kf ι σ j ϖ →
      HarmSplit O Kf p TT k (uH TT.card k (lamA p k a)) (8 * a) →
      ∀ (κP : ℝ) (κT : Fin n' → (TT → ℤ) → (TT → ℤ) → ℝ),
        InputRank W k p ι σ ϖ TT (WAp k Y a c (Jsh C₀ N₁ k a b')) (WBp bl bu c (Jsh C₀ N₁ k a b'))
          (t0F Ct C₀ N₁ p TT k G' a b' c cStar) (c4F TT c cStar) (D0 CI TT.card Y N₁ k (lamA p k a)) κP κT →
        SegMean TT (WAp k Y a c (Jsh C₀ N₁ k a b')) (WBp bl bu c (Jsh C₀ N₁ k a b')) κT CA N₁ Y →
        κP ≤ CP * TT.card * N₁ / Y →
        CloudPair O Kf p TT k c (Dcl TT.card k (lamA p k a)) →
        ∃ κ : (TT → ℤ) → (TT → ℤ) → ℝ, (∀ aa bb, 0 ≤ κ aa bb) ∧ boxMean TT k Y a bl bu κ ≤ C * TT.card * N₁ / Y ∧
          ∀ (aw bw : Fin n' → ℤ) (lam0 : Fin n' → Fin k → ℤ), IsShape TT aw bw c lam0 →
            (∀ s ∈ TT, aw s ∈ aWin k Y a ∧ bw s ∈ bWin bl bu) →
            ∀ t : ℕ, depthI C (C₀ * N₁ ^ 2 * Real.log a) p n' k TT G' N₁ a b' c cStar aw bw ≤ t →
              ∀ L : Submodule W (Fin k → Qq), L.IsLattice Qq →
                LLPAt p 1 ι σ ϖ lam0 t D (κ (fun s => aw s) (fun s => bw s)) cStar L := by
  obtain ⟨CH, C, hC, h⟩ := first_local'' C₀ hC₀ Ct CI CA CP hCt hCI hCA hCP
  refine ⟨CH, C, hC, ?_⟩
  intro p n' k TT G' N₁ Y Yb a b' bl bu c D cStar hn' hp hF W Qq O Kf _ _ _ _ _ _ _ _ _ _ _ ι σ j ϖ hU hHS κP κT
    hI1 hseg hκP hCPair
  have hk : 2 ≤ k := by have := hF.k_ge; omega
  have := hU.frac_O
  exact h p n' k TT G' N₁ Y Yb a b' bl bu c D cStar hn' hp hF W Qq O Kf ι σ j ϖ hU
    (FlatDimPf.flatDim Kf hk TT) hHS κP κT hI1 hseg hκP (weylDim Kf (by omega)) hCPair (hwSat O Kf (by omega))

end FirstLocal

end

end HwSatPf
