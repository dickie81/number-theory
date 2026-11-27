import FirstCloudCount
import WeylSandwich

/-!
# The cloud maps at an edge (L5, A-N16)

The edge part of module 11 (`FirstCloud`) of the L5/L6 plan, at one orbit of an inert prime `p` in the setting
`Unram`. For a weight `λ` of the cloud shape (top extremes `(A_s + c, B_s + c)`, middle entries in `[−c, c]`, `0` off
the tops `TT`), the flat weights `H = fl(A, B)`, `H⁺ = fl(A + 2c, B + 2c)`, `fl₂ = fl(2c, 2c)` and the cloud weight
`μ = λ − H` (`cloudWt`: `(c, λ_{s,1}, …, λ_{s,k−2}, −c)` at the tops) with its dual `μ* = −μ ∘ rev` (`cloudDual`).

**The weights.** `λ = H + μ` (`lam_eq_flat_add_cloud`), `H⁺ = H + fl₂` (`flatWt_add`); `lamAt`, the block weights and
`A₁` are additive (`lamAt_add`, `wt1_add`, `topA_add`), and `A₁(μ) = A₁(μ*) = Nc`, `A₁(fl₂) = 2Nc`
(`topA_cloudWt`, `topA_cloudDual`, `topA_flat2`).

**The edge basis.** An edge `L″ ⊂ L` of type `1` has a basis matrix `B` of `L` with `L″` spanned by the columns of
`B·diag(p, 1, …, 1)` (`exists_basis_edge0`: the plane coordinate moved to `0`); its block bases `C_s = ισ^s(B)`
(`edgeC`) give the blocks of `L`, of the midpoint (`C_s·diag(ϖ, 1, …, 1)`) and of `L″` (`C_s·diag(p, 1, …, 1)`).

**Top vectors.** For `P ∈ ∇_O` whose row weight has the maximal entry `natW(λ_b)_0` in row `0` of every block, the
normalised vector `P̃ = p^{−A₁}·twist_{C⁻¹}P` (`topVec`) has `twist_{C·diag(c₀,1,…,1)}P̃ = p^{−A₁}c₀^{A₁}·P`
(`twist_topVec`), so `P̃ ∈ ∇(L″)`, `P̃ ∈ 𝓡(e)`, `p^{A₁}P̃ ∈ ∇(L)` (`topVec_mem_nab`, `topVec_mem_edgeLat`,
`pow_smul_topVec_mem_nab`); on the other edges into `L`, `ϖ^m·∇(L) ⊆ ∇(mid)` for `m ≥ −Σ_b detShift(λ_b)`
(`smul_mem_nabMid_of_nab`, from the adapted basis `OffTop.exists_adapted_basis_ge`).

**Products.** For `K = H + ν` with `H, ν` dominant: `𝓡_H(e)·𝓡_ν(e) ⊆ 𝓡_K(e)` (`mul_mem_edgeLat'`) and sources at `H`
times `∇_ν(L″)` are sources at `K`, at the same depth and conductor (`mul_mem_srcFam'`), by the easy half of the
Cartan product `FirstCloud.mul_mem_nablaB'` and the inclusion `∇(L″) ⊆ 𝓡(e′)` (model fact 1).
-/

namespace FirstCloud

open MvPolynomial WeylFock HermForms InertModel LocalLattice LocalRank FirstMeans FirstAssembly

open scoped Matrix Pointwise

noncomputable section

/-! ## The weights of the cloud step -/

section Weights

variable {n' k : ℕ}

/-- **The cloud weight** `μ = λ − fl(A, B)`: at a top `s`, `(c, λ_{s,1}, …, λ_{s,k−2}, −c)`; `0` off the tops. -/
def cloudWt (TT : Finset (Fin n')) (c : ℕ) (lam0 : Fin n' → Fin k → ℤ) : Fin n' → Fin k → ℤ := fun s i =>
  if s ∈ TT then (if i.val = 0 then (c : ℤ) else if i.val + 1 = k then -(c : ℤ) else lam0 s i) else 0

/-- **The dual cloud weight** `μ* = −μ ∘ rev`: at a top `s`, `(c, −λ_{s,k−2}, …, −λ_{s,1}, −c)`. -/
def cloudDual (TT : Finset (Fin n')) (c : ℕ) (lam0 : Fin n' → Fin k → ℤ) : Fin n' → Fin k → ℤ := fun s i =>
  -cloudWt TT c lam0 s i.rev

/-- **The middle Weyl factor** of a weight `w` at a pair `i < j`: `(w_i − w_j + j − i)/(j − i)` when both indices are
in the middle `[1, k − 2]`, `1` otherwise; the product over the pairs is the Weyl dimension of the middle entries. -/
def midFac (w : Fin k → ℤ) (i j : Fin k) : ℚ :=
  if 0 < i.val ∧ j.val + 1 < k then
    ((w i - w j + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : ℚ) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))
  else 1

/-- **`lamAt` is additive.** -/
theorem lamAt_add (f g : Fin n' → Fin k → ℤ) (s : Fin n') : lamAt (f + g) s = lamAt f s + lamAt g s := by
  unfold lamAt
  split_ifs
  · rfl
  · funext i
    simp only [Pi.add_apply, neg_add]

/-- **The block weights are additive.** -/
theorem wt1_add (f g : Fin n' → Fin k → ℤ) : wt1 (f + g) = wt1 f + wt1 g := by
  funext b
  exact lamAt_add f g b.2

/-- **`A₁` is additive.** -/
theorem topA_add (f g : Fin n' → Fin k → ℤ) : topA 1 (f + g) = topA 1 f + topA 1 g := by
  simp only [topA, topSum, lamAt_add, Pi.add_apply, Finset.sum_add_distrib]

/-- **A weight of the cloud shape is the flat weight plus the cloud weight**: `λ = fl(A, B) + μ`. -/
theorem lam_eq_flat_add_cloud {TT : Finset (Fin n')} {A B : TT → ℤ} {c : ℕ} {lam0 : Fin n' → Fin k → ℤ}
    (hsh : IsShape TT (ext TT (A + fun _ => (c : ℤ))) (ext TT (B + fun _ => (c : ℤ))) c lam0)
    (hz : ∀ s ∉ TT, lam0 s = 0) : lam0 = flatWt TT A B + cloudWt TT c lam0 := by
  funext s i
  simp only [Pi.add_apply, flatWt, cloudWt]
  by_cases hs : s ∈ TT
  · have h := (hsh.2 s i).1 hs
    simp only [hs, ↓reduceIte]
    split_ifs with h0 h1
    · rw [h.1 h0, ext_add, ext_of_mem _ hs, ext_of_mem _ hs]
    · rw [h.2.1 h1, ext_add, ext_of_mem _ hs, ext_of_mem _ hs]
      simp only [neg_add]
    · ring
  · simp [hs, hz s hs, ext_of_not_mem]

/-- **Flat weights add**: `fl(A + 2c, B + 2c) = fl(A, B) + fl(2c, 2c)`. -/
theorem flatWt_add (TT : Finset (Fin n')) (A B : TT → ℤ) (d : ℤ) :
    flatWt (k := k) TT (A + fun _ => d) (B + fun _ => d) = flatWt TT A B + flatWt TT (fun _ => d) fun _ => d := by
  funext s i
  simp only [Pi.add_apply, flatWt]
  split_ifs
  · exact ext_add _ _ _
  · rw [ext_add]
    ring
  · ring

/-- **The cloud weight is dominant** (`k ≥ 2`): `c ≥ λ_{s,1} ≥ … ≥ λ_{s,k−2} ≥ −c` at a top. -/
theorem antitone_cloudWt (hk : 2 ≤ k) {TT : Finset (Fin n')} {a b : Fin n' → ℤ} {c : ℕ}
    {lam0 : Fin n' → Fin k → ℤ} (hsh : IsShape TT a b c lam0) (s : Fin n') : Antitone (cloudWt TT c lam0 s) := by
  intro i i' (hii : i.val ≤ i'.val)
  simp only [cloudWt]
  by_cases hs : s ∈ TT
  · have hm : ∀ l : Fin k, 0 < l.val → l.val + 1 < k → |lam0 s l| ≤ c := fun l h1 h2 => ((hsh.2 s l).1 hs).2.2 h1 h2
    simp only [hs, ↓reduceIte]
    split_ifs <;> first | omega | (have := hsh.1 s (show i ≤ i' from hii); omega) |
      (have := abs_le.1 (hm i (by omega) (by omega)); omega) | (have := abs_le.1 (hm i' (by omega) (by omega)); omega)
  · simp [hs]

/-- **The dual cloud weight is dominant** (`k ≥ 2`). -/
theorem antitone_cloudDual (hk : 2 ≤ k) {TT : Finset (Fin n')} {a b : Fin n' → ℤ} {c : ℕ}
    {lam0 : Fin n' → Fin k → ℤ} (hsh : IsShape TT a b c lam0) (s : Fin n') : Antitone (cloudDual TT c lam0 s) :=
  fun _ _ hii => neg_le_neg (antitone_cloudWt hk hsh s (Fin.rev_le_rev.2 hii))

/-- **`A₁` of the cloud weight**: `Nc`, `N = |TT|`. -/
theorem topA_cloudWt (hk : 2 ≤ k) (TT : Finset (Fin n')) (c : ℕ) (lam0 : Fin n' → Fin k → ℤ) :
    topA 1 (cloudWt TT c lam0) = TT.card * c := by
  rw [topA, topSum_one (by omega), ← Finset.sum_subset (Finset.subset_univ TT) fun s _ hs => by
    rw [lamAt_zero (by omega)]; simp [cloudWt, hs]]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [lamAt_zero (by omega)]
  simp only [cloudWt, hs, ↓reduceIte]
  split_ifs <;> omega

/-- **`A₁` of the dual cloud weight**: `Nc`. -/
theorem topA_cloudDual (hk : 2 ≤ k) (TT : Finset (Fin n')) (c : ℕ) (lam0 : Fin n' → Fin k → ℤ) :
    topA 1 (cloudDual TT c lam0) = TT.card * c := by
  rw [topA, topSum_one (by omega), ← Finset.sum_subset (Finset.subset_univ TT) fun s _ hs => by
    rw [lamAt_zero (by omega)]; simp [cloudDual, cloudWt, hs]]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [lamAt_zero (by omega)]
  simp only [cloudDual, cloudWt, hs, ↓reduceIte, Fin.val_rev]
  split_ifs <;> omega

/-- **`A₁` of `fl(2c, 2c)`**: `2Nc`. -/
theorem topA_flat2 (hk : 2 ≤ k) (TT : Finset (Fin n')) (c : ℕ) :
    topA 1 (flatWt (k := k) TT (fun _ => 2 * (c : ℤ)) fun _ => 2 * (c : ℤ)) = 2 * (TT.card * c) := by
  rw [topA_flatWt hk, ← Finset.sum_subset (Finset.subset_univ TT) fun s _ hs => by simp [ext_of_not_mem _ hs]]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  simp [ext_of_mem _ hs]

end Weights


/-! ## The edge basis and the top vectors -/

section EdgeBasis

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

omit [CharZero Kf] in
/-- **An edge of type `1` with the plane coordinate `0`**: a basis matrix `B` of `L` with `L″` spanned by the columns
of `B·diag(p, 1, …, 1)` (`exists_basis_edge`, with the columns permuted by the transposition moving the plane
coordinate to `0`). -/
theorem exists_basis_edge0 (hU : Unram p n' W Qq O Kf ι σ j ϖ) (hk : 0 < k) {L'' L : Submodule W (Fin k → Qq)}
    (he : IsEdge (n' := n') p 1 L'' L) :
    ∃ B : Matrix (Fin k) (Fin k) Qq, IsUnit B.det ∧ L = Submodule.span W (Set.range fun l i => B i l) ∧
      L'' = Submodule.span W (Set.range fun l i =>
        (B * Matrix.diagonal fun i => if i ∈ ({⟨0, hk⟩} : Finset (Fin k)) then (p : Qq) else 1) i l) := by
  obtain ⟨B, S, hS, hB, hLB, hL''B⟩ := exists_basis_edge hU he
  obtain ⟨j₀, rfl⟩ := Finset.card_eq_one.1 hS
  set τ := Equiv.swap (⟨0, hk⟩ : Fin k) j₀
  have hs : IsUnit ((Equiv.Perm.sign τ : ℤ) : Qq) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]
  refine ⟨B.submatrix id τ, by rw [Matrix.det_permute']; exact hs.mul hB, ?_, ?_⟩
  · rw [hLB, show (fun l i => B.submatrix id τ i l) = (fun m i => B i m) ∘ τ from rfl,
      (Equiv.surjective τ).range_comp]
  · have e : (fun l i => (B.submatrix id τ * Matrix.diagonal fun i =>
        if i ∈ ({⟨0, hk⟩} : Finset (Fin k)) then (p : Qq) else 1) i l) =
        (fun m i => (B * Matrix.diagonal fun i => if i ∈ ({j₀} : Finset (Fin k)) then (p : Qq) else 1) i m) ∘ τ := by
      funext l i
      simp only [Function.comp_apply, Matrix.mul_diagonal, Matrix.submatrix_apply, id, Finset.mem_singleton]
      congr 1
      have : τ l = j₀ ↔ l = ⟨0, hk⟩ := by
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
      exact if_congr this.symm rfl rfl
    rw [hL''B, e, (Equiv.surjective τ).range_comp]

/-- **The block bases of an edge**: `C_s = ισ^s(B)` for a basis matrix `B` of the upper lattice. -/
abbrev edgeC (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (B : Matrix (Fin k) (Fin k) Qq) :
    Unit × Fin n' → Matrix (Fin k) (Fin k) Kf :=
  fun b => (ι.comp (σ ^ b.2.val).toRingHom).mapMatrix B

omit [CharZero Kf] in
/-- **The diagonal of the plane coordinate `0`** is `diag(c₀, 1, …, 1)`. -/
theorem diag_singleton_eq_dg0 (hk : 0 < k) (c₀ : Kf) :
    (Matrix.diagonal fun i : Fin k => if i ∈ ({⟨0, hk⟩} : Finset (Fin k)) then c₀ else 1) = dg0 c₀ := by
  unfold dg0
  congr 1
  funext i
  simp [Finset.mem_singleton, Fin.ext_iff]

omit [CharZero Kf] in
/-- **The three block bases of an edge**: `C_s` of `L`, `C_s·diag(ϖ, 1, …, 1)` of the midpoint and
`C_s·diag(p, 1, …, 1)` of `L″`. -/
theorem edgeC_bases (hU : Unram p n' W Qq O Kf ι σ j ϖ) (hk : 0 < k) {L'' L : Submodule W (Fin k → Qq)}
    {B : Matrix (Fin k) (Fin k) Qq} (hB : IsUnit B.det) (hL : L = Submodule.span W (Set.range fun l i => B i l))
    (hL'' : L'' = Submodule.span W (Set.range fun l i =>
      (B * Matrix.diagonal fun i => if i ∈ ({⟨0, hk⟩} : Finset (Fin k)) then (p : Qq) else 1) i l)) :
    (∀ b : Unit × Fin n', IsBasisOf (blk (O := O) ι σ b.2 L) (edgeC ι σ B b)) ∧
      (∀ b : Unit × Fin n', IsBasisOf (midBlk ι σ ϖ b.2 L'' L) (edgeC ι σ B b * dg0 (algebraMap O Kf ϖ))) ∧
      ∀ b : Unit × Fin n', IsBasisOf (blk (O := O) ι σ b.2 L'') (edgeC ι σ B b * dg0 (p : Kf)) := by
  refine ⟨fun b => isBasisOf_blk hU _ hB hL, fun b => ?_, fun b => ?_⟩
  · rw [← diag_singleton_eq_dg0 hk]
    exact isBasisOf_midBlk hU _ hB hL hL''
  · rw [← diag_singleton_eq_dg0 hk]
    exact isBasisOf_blk_edge hU _ hB hL''

/-- **The normalised top vector** `P̃ = p^{−A₁(w)}·twist_{C⁻¹}P` of `P` in the coordinates `C` of an edge. -/
def topVec (p : ℕ) (C : Unit × Fin n' → Matrix (Fin k) (Fin k) Kf) (w : Fin n' → Fin k → ℤ)
    (P : Pol (Unit × Fin n') k Kf) : Pol (Unit × Fin n') k Kf :=
  (p : Kf) ^ (-topA 1 w) • twist (wt1 w) (fun b => (C b)⁻¹) P

omit [CharZero Kf] in
/-- **The row-`0` exponent of a top vector** is `A₁`: `Σ_b (detShift(w_b) + natW(w_b)_0) = A₁(w)`. -/
theorem sum_detShift_add_natW (hk : 0 < k) {w : Fin n' → Fin k → ℤ} (hw : ∀ s, Antitone (w s)) :
    ∑ b : Unit × Fin n', (detShift (wt1 w b) + ((nu1 w b ⟨0, hk⟩ : ℕ) : ℤ)) = topA 1 w := by
  have key : ∀ b : Unit × Fin n', detShift (wt1 w b) + ((nu1 w b ⟨0, hk⟩ : ℕ) : ℤ) = wt1 w b ⟨0, hk⟩ := by
    intro b
    have h : detShift (wt1 w b) ≤ wt1 w b ⟨0, hk⟩ := detShift_le (antitone_blockWt (fun _ => hw) b) ⟨0, hk⟩
    simp only [nu1, natW]
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  simp only [key]
  rw [topA, topSum_one hk, Fintype.sum_prod_type, Fintype.sum_unique]
  rfl

omit [CharZero Kf] in
/-- **Twisting a top vector to the edge**: for `P` whose row weight `ρ` has `ρ_{b,0} = natW(w_b)_0`,
`twist_{C·diag(c₀,1,…,1)} P̃ = p^{−A₁}c₀^{A₁}·P`. -/
theorem twist_topVec (hk : 0 < k) {C : Unit × Fin n' → Matrix (Fin k) (Fin k) Kf} (hC : ∀ b, IsUnit (C b).det)
    {w : Fin n' → Fin k → ℤ} (hw : ∀ s, Antitone (w s)) {P : Pol (Unit × Fin n') k Kf}
    {ρ : Unit × Fin n' → Fin k → ℕ} (hP : IsWeightedHomogeneous (rowW (Unit × Fin n') k) P ρ)
    (hρ : ∀ b (i : Fin k), i.val = 0 → ρ b i = nu1 w b i) {c₀ : Kf} (hc₀ : c₀ ≠ 0) :
    twist (wt1 w) (fun b => C b * dg0 c₀) (topVec p C w P) = ((p : Kf) ^ (-topA 1 w) * c₀ ^ topA 1 w) • P := by
  rw [topVec, twist_smul, twist_twist, show (fun b => (C b)⁻¹ * (C b * dg0 c₀)) = fun _ => dg0 c₀ from
    funext fun b => by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hC b), Matrix.one_mul],
    twist_dg0 hk _ hP hc₀, smul_smul]
  congr 3
  rw [← sum_detShift_add_natW hk hw]
  exact Finset.sum_congr rfl fun b _ => by rw [hρ b ⟨0, hk⟩ rfl]

end EdgeBasis


/-! ## Lattices of the top vectors and products at an edge -/

section Products

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ}

/-- **The lattices of a top vector**: for `P ∈ ∇_O(w)` with row weight maximal in row `0`, the normalised `P̃` lies in
`∇_{Kf}`, in `∇(L″)` and in `𝓡(e)`, and `p^{A₁}P̃ ∈ ∇(L)`. -/
theorem topVec_mem (hU : Unram p n' W Qq O Kf ι σ j ϖ) (hk : 0 < k) {L'' L : Submodule W (Fin k → Qq)}
    {B : Matrix (Fin k) (Fin k) Qq} (hB : IsUnit B.det) (hL : L = Submodule.span W (Set.range fun l i => B i l))
    (hL'' : L'' = Submodule.span W (Set.range fun l i =>
      (B * Matrix.diagonal fun i => if i ∈ ({⟨0, hk⟩} : Finset (Fin k)) then (p : Qq) else 1) i l))
    {w : Fin n' → Fin k → ℤ} (hw : ∀ s, Antitone (w s)) {P : Pol (Unit × Fin n') k Kf}
    (hPint : P ∈ nablaInt (Oint O Kf) (nu1 w)) {ρ : Unit × Fin n' → Fin k → ℕ}
    (hP : IsWeightedHomogeneous (rowW (Unit × Fin n') k) P ρ) (hρ : ∀ b (i : Fin k), i.val = 0 → ρ b i = nu1 w b i) :
    topVec p (edgeC ι σ B) w P ∈ nabla Kf (nu1 w) ∧ topVec p (edgeC ι σ B) w P ∈ nab O ι σ w L'' ∧
      topVec p (edgeC ι σ B) w P ∈ edgeLat ι σ ϖ 1 w L'' L ∧
      (p : Kf) ^ topA 1 w • topVec p (edgeC ι σ B) w P ∈ nab O ι σ w L := by
  obtain ⟨hC, hCm, hC''⟩ := edgeC_bases (n' := n') (O := O) hU hk hB hL hL''
  have hdet : ∀ b, IsUnit (edgeC (n' := n') ι σ B b).det := fun b => (hC b).1
  have hwb : ∀ b, Antitone (wt1 w b) := antitone_blockWt fun _ => hw
  have hPV : P ∈ nabla Kf (nu1 w) := WeylSandwich.nablaInt_subset_nabla _ (fun b => natW_antitone (hwb b)) hPint
  have hV : topVec p (edgeC ι σ B) w P ∈ nabla Kf (nu1 w) := Submodule.smul_mem _ _ (twist_mem_nabla _ _ hPV)
  have hp : (p : Kf) ≠ 0 := hU.castK_ne_zero
  have hϖ := varpiK_ne_zero hU
  refine ⟨hV, ?_, ?_, ?_⟩
  · show _ ∈ nablaB (wt1 w) fun b => blk ι σ b.2 L''
    rw [mem_nablaB_iff hC'', twist_topVec hk hdet hw hP hρ hp, ← zpow_add₀ hp, neg_add_cancel, zpow_zero,
      one_smul]
    exact ⟨hV, hPint⟩
  · show _ ∈ nablaB (wt1 w) fun b => midBlk ι σ ϖ b.2 L'' L
    rw [mem_nablaB_iff hCm, twist_smul, twist_topVec hk hdet hw hP hρ hϖ, smul_smul, OffTop.castK_zpow hU,
      ← zpow_add₀ hϖ, ← zpow_add₀ hϖ, show topA 1 w + (2 * -topA 1 w + topA 1 w) = 0 by ring, zpow_zero, one_smul]
    exact ⟨Submodule.smul_mem _ _ hV, hPint⟩
  · have e : twist (wt1 w) (edgeC ι σ B) ((p : Kf) ^ topA 1 w • topVec p (edgeC ι σ B) w P) = P := by
      rw [topVec, twist_smul, twist_smul, twist_twist_inv _ hdet, smul_smul, ← zpow_add₀ hp, add_neg_cancel,
        zpow_zero, one_smul]
    show _ ∈ nablaB (wt1 w) fun b => blk ι σ b.2 L
    rw [mem_nablaB_iff hC, e]
    exact ⟨Submodule.smul_mem _ _ hV, hPint⟩

/-- **`∇(L)` scaled into the midpoint of another edge into `L`**: `ϖ^m·∇(L) ⊆ ∇(mid(L₁ ⊂ L))` for
`m ≥ −Σ_b detShift(w_b)` (adapted basis `OffTop.exists_adapted_basis_ge`: `∇(L) = span(p^{π_i}x_i)`,
`∇(mid) = span(ϖ^{π_i}x_i)`, `π_i ≥ Σ_b detShift(w_b)`). -/
theorem smul_mem_nabMid_of_nab (hU : Unram p n' W Qq O Kf ι σ j ϖ) {w : Fin n' → Fin k → ℤ}
    (hw : ∀ s, Antitone (w s)) {L₁ L : Submodule W (Fin k → Qq)} (he : IsEdge (n' := n') p 1 L₁ L) {m : ℤ}
    (hm : -∑ b, detShift (wt1 w b) ≤ m) {F : Pol (Unit × Fin n') k Kf} (hF : F ∈ nab O ι σ w L) :
    algebraMap O Kf ϖ ^ m • F ∈ nabMid ι σ ϖ w L₁ L := by
  obtain ⟨x, π, -, hxL, hxm, hπ⟩ := OffTop.exists_adapted_basis_ge hU hw he
  have hϖ := varpiK_ne_zero hU
  rw [hxm, SetLike.mem_coe]
  rw [hxL, SetLike.mem_coe] at hF
  refine smul_mem_span_range (fun i => ?_) hF
  have hi : 0 ≤ m + π i := by
    have := hπ i
    push_cast at this
    linarith
  rw [OffTop.castK_zpow hU, smul_smul, ← zpow_add₀ hϖ, show m + 2 * π i = (m + π i) + π i by ring,
    zpow_add₀ hϖ, ← smul_smul, algebraMap_zpow_eq _ hi, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

omit [CharZero Kf] in
/-- **Products of edge lattices**: `𝓡_H(e)·𝓡_ν(e) ⊆ 𝓡_{H+ν}(e)` for dominant `H`, `ν` (`A₁` is additive and
`mul_mem_nablaB'` at the midpoint). -/
theorem mul_mem_edgeLat' (hU : Unram p n' W Qq O Kf ι σ j ϖ) {H ν : Fin n' → Fin k → ℤ} (hH : ∀ s, Antitone (H s))
    (hν : ∀ s, Antitone (ν s)) {L'' L : Submodule W (Fin k → Qq)} {F G : Pol (Unit × Fin n') k Kf}
    (hF : F ∈ edgeLat ι σ ϖ 1 H L'' L) (hG : G ∈ edgeLat ι σ ϖ 1 ν L'' L) :
    F * G ∈ edgeLat ι σ ϖ 1 (H + ν) L'' L := by
  have hϖ := varpiK_ne_zero hU
  show _ ∈ nablaB (wt1 (H + ν)) fun b => midBlk ι σ ϖ b.2 L'' L
  rw [topA_add, zpow_add₀ hϖ, ← smul_mul_smul_comm, wt1_add]
  exact mul_mem_nablaB' (antitone_blockWt fun _ => hH) (antitone_blockWt fun _ => hν) hF hG

/-- **Sources times `∇(L″)`**: a source at `H` times an element of `∇_ν(L″)` is a source at `H + ν`, at the same depth
and conductor (`mul_mem_nablaB'`, `mul_mem_edgeLat'`, and `∇_ν(L″) ⊆ 𝓡_ν(e′)` for every edge `e′` out of `L″`). -/
theorem mul_mem_srcFam' (hU : Unram p n' W Qq O Kf ι σ j ϖ) {H ν : Fin n' → Fin k → ℤ} (hH : ∀ s, Antitone (H s))
    (hν : ∀ s, Antitone (ν s)) {t c : ℕ} {L'' L : Submodule W (Fin k → Qq)} {F Q : Pol (Unit × Fin n') k Kf}
    (hF : F ∈ SrcFam p 1 ι σ ϖ H t c L'' L) (hQ : Q ∈ nab O ι σ ν L'') :
    F * Q ∈ SrcFam p 1 ι σ ϖ (H + ν) t c L'' L := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hF
  have hQe : ∀ L', IsEdge (n' := n') p 1 L'' L' → Q ∈ edgeLat ι σ ϖ 1 ν L'' L' := fun L' he' =>
    nab_subset_edgeLat hU hν he' hQ
  refine ⟨⟨?_, Set.mem_iInter₂.2 fun L' he' => mul_mem_edgeLat' hU hH hν (Set.mem_iInter₂.1 h2 L' he')
    (hQe L' he')⟩, Set.mem_iInter₂.2 fun L' he' => Set.mem_iInter.2 fun hne => ?_⟩
  · obtain ⟨F₀, hF₀, rfl⟩ := Set.mem_smul_set.1 h1
    refine Set.mem_smul_set.2 ⟨F₀ * Q, ?_, (smul_mul_assoc _ _ _).symm⟩
    show F₀ * Q ∈ nablaB (wt1 (H + ν)) fun b => blk ι σ b.2 L''
    rw [wt1_add]
    exact mul_mem_nablaB' (antitone_blockWt fun _ => hH) (antitone_blockWt fun _ => hν)
      (show F₀ ∈ nablaB (wt1 H) fun b => blk ι σ b.2 L'' from hF₀) hQ
  · obtain ⟨F₁, hF₁, rfl⟩ := Set.mem_smul_set.1 (Set.mem_iInter.1 (Set.mem_iInter₂.1 h3 L' he') hne)
    exact Set.mem_smul_set.2 ⟨F₁ * Q, mul_mem_edgeLat' hU hH hν hF₁ (hQe L' he'), (smul_mul_assoc _ _ _).symm⟩

end Products

end

end FirstCloud
