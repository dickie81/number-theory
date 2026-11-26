import InertModel

/-!
# The sandwich `Δ_O ⊆ ∇_O` and `p^e·∇_O ⊆ Δ_O`

L3 of the local theory of the gain. For an antitone shape `ν` (block-wise, `Φ` the blocks; one block is
`Φ = Unit`), a field `K` of characteristic `0` and a subring `A ⊆ K`, the two `A`-lattices in `∇_K(ν)` are the span
`∇_A(ν)` of the bideterminants (`WeylFock.nablaInt`) and its Fock dual `Δ_A(ν)` for the normalised bilinear Fock form
`⟨F, G⟩/κ`, `κ = ⟨hw_ν, hw_ν⟩` (`WeylFock.Delta`). In this normalisation the inclusions run `Δ ⊆ ∇`: for one block of
`GL_2` and `ν = (a, 0)`, `∇_ℤ` is spanned by the monomials `x₀₀^i x₁₀^{a−i}`, `κ = a!`, and `Δ_ℤ` by the
`C(a, i)·x₀₀^i x₁₀^{a−i}`.

**Main results.**
* *First half* (`Delta_subset_nablaInt`): `Δ_A(ν) ⊆ ∇_A(ν)` for every subring `A`, with no hypothesis on `A`.
* *Second half* (`pow_smul_mem_Delta`): `p^e·∇_A(ν) ⊆ Δ_A(ν)` with `e = sandExp p ν`, when every natural number
  prime to `p` is invertible in `A`.
* *The sandwich* (`sandwich`): both, for `A = O ⊆ Kf` with `O` a local ring in which the prime `p` is not a unit
  (then the integers prime to `p` are units, `isUnit_natCast_of_not_dvd`).
* *Tuples and local forms* (`DeltaT_subset_NablaT`, `pow_smul_mem_DeltaT`, `forms_DeltaT_subset`,
  `pow_smul_mem_forms`): `Δ_L ⊆ ∇_L` and `p^e·∇_L ⊆ Δ_L` for the local Weyl lattices of a tuple in the setting `Unram`
  of `InertModel`, hence `M ⊆ M∇` and `p^e·M∇ ⊆ M` for the local forms of a level, `e = tupExp p lam0`.
* *The exponent* (`sandExp`, `sandExp_le`): `e = v_p(κ) − Σ_{τ,b} (v_p(ν_{τ,b}!) − (k − 1)·⌊log_p ν_{τ,b}⌋)`
  (truncated subtractions). Given the classical value `κ = ∏_b ν_b!·∏_{i<j} (ν_i + j − i)/(ν_i − ν_j + j − i)` of the
  Fock norm of `hw_ν` in every block (an explicit hypothesis of `sandExp_le`, not proved here), it is at most
  `Σ_τ (Σ_{i<j} ⌊log_p(ν_{τ,i} + j − i)⌋ + (k − 1)·Σ_b ⌊log_p ν_{τ,b}⌋)`.

**Route of the first half** (a reproducing formula with sorted rows). By `WeylSpan.fock_hw` and the adjointness
`fock_lsub`, `κ·F(g) = ⟨hw_ν(gᵀ·), F⟩` for `F ∈ ∇_K(ν)`. Cauchy–Binet with sorted rows (`lsub_hw_sorted`) writes
`hw_ν(gᵀx) = Σ_{rows} bidet_rows(g)·bidet_rows(x)` over the rows that are strictly increasing in every minor: the
library's Cauchy–Binet `lsub_minor` sums over all row maps, and grouping a row map with its sorted version
(`sum_eq_sum_sorted`, from `Tuple.sort`) turns its monomials into minors (Leibniz). So
`κ·F = Σ_{rows sorted} ⟨bidet_rows, F⟩·bidet_rows` (`kappa_mul_eq_sum`), and for `F ∈ Δ_A` the coefficients
`⟨F, bidet_rows⟩/κ` lie in `A`.

**Route of the second half** (Kummer for multinomials, column by column). For `F ∈ ∇_A` and a bideterminant `β`,
`⟨p^eF, β⟩/κ = Σ_d F_d·β_d·(p^e·d!/κ)` with `F_d, β_d ∈ A` (`coeff_mem_of_nablaInt`, `coeff_bidet_mem`). Every exponent
`d` of `F` has column weight `ν`, and the entries of column `(τ, b)` sum to `ν_{τ,b}`, so
`v_p(d!) ≥ Σ_{τ,b} (v_p(ν_{τ,b}!) − (k − 1)·⌊log_p ν_{τ,b}⌋)` (`padicValNat_factorial_sum_le`, from Legendre's formula
and `⌊Σ x/q⌋ ≤ Σ ⌊x/q⌋ + (k − 1)`); `κ` is a positive integer (`kapN`), and `p^e·d!/κ ∈ A` once
`v_p(κ) ≤ e + v_p(d!)` (`pow_mul_div_mem`).
-/

namespace WeylSandwich

open MvPolynomial WeylFock HermForms InertModel

noncomputable section

/-! ## Sorting tuples -/

section Sorting

/-- **An injective tuple has exactly one sorting permutation**: exactly one `π` makes `f ∘ π` strictly
increasing (`Tuple.sort`, unique by `Tuple.unique_monotone`). -/
theorem card_sorting {m n : ℕ} {f : Fin m → Fin n} (hf : Function.Injective f) :
    (Finset.univ.filter fun π : Equiv.Perm (Fin m) => StrictMono (f ∘ π)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨Tuple.sort f, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, fun π hπ => ?_⟩⟩
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _,
      (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)⟩
  · rw [Finset.mem_filter] at hπ
    have h := Tuple.unique_monotone hπ.2.monotone (Tuple.monotone_sort f)
    exact Equiv.ext fun i => hf (congrFun h i)

/-- **Summing over tuples by sorting**: if `φ` vanishes on the non-injective tuples, then
`Σ_f φ(f) = Σ_{I strictly increasing} Σ_π φ(I ∘ π)`. -/
theorem sum_eq_sum_sorted {m n : ℕ} {M : Type*} [AddCommMonoid M] (φ : (Fin m → Fin n) → M)
    (hφ : ∀ f, ¬ Function.Injective f → φ f = 0) :
    ∑ f, φ f = ∑ I, if StrictMono I then ∑ π : Equiv.Perm (Fin m), φ (I ∘ π) else 0 := by
  have h1 : ∀ f, φ f = ∑ π : Equiv.Perm (Fin m), if StrictMono (f ∘ π) then φ f else 0 := fun f => by
    by_cases hf : Function.Injective f
    · rw [← Finset.sum_filter, Finset.sum_const, card_sorting hf, one_smul]
    · simp [hφ f hf]
  rw [Finset.sum_congr rfl fun f _ => h1 f, Finset.sum_comm]
  have h2 : ∀ π : Equiv.Perm (Fin m), (∑ f, if StrictMono (f ∘ π) then φ f else 0) =
      ∑ I, if StrictMono I then φ (I ∘ ⇑π⁻¹) else 0 := fun π => by
    refine (Fintype.sum_bijective (fun I => I ∘ ⇑π⁻¹) ?_ _ _ fun I => ?_).symm
    · refine ⟨fun I J h => ?_, fun f => ⟨f ∘ ⇑π, ?_⟩⟩
      · funext i
        simpa using congrFun h (π i)
      · funext i
        simp
    · have e : (I ∘ ⇑π⁻¹) ∘ ⇑π = I := by funext i; simp
      rw [e]
  rw [Finset.sum_congr rfl fun π _ => h2 π, Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  split_ifs with hI
  · exact Fintype.sum_equiv (Equiv.inv _) _ _ fun π => rfl
  · simp

end Sorting

/-! ## Cauchy–Binet with sorted rows, and the reproducing formula -/

section Reproduce

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {K : Type} [Field K]

omit [Fintype Φ] [DecidableEq Φ] in
/-- **Permuting the rows of a minor**: `D_{I∘π} = sign(π)·D_I`. -/
theorem minor_comp_perm (τ : Φ) (s : Fin n) (I : Fin (s + 1) → Fin n) (π : Equiv.Perm (Fin (s + 1))) :
    (minor τ s (I ∘ π) : Pol Φ n K) = ((Equiv.Perm.sign π : ℤ) : Pol Φ n K) * minor τ s I := by
  unfold minor
  rw [← Matrix.det_permute]
  rfl

omit [Fintype Φ] [DecidableEq Φ] in
/-- **Repeated rows**: a minor with a repeated row vanishes. -/
theorem minor_eq_zero {τ : Φ} {s : Fin n} {I : Fin (s + 1) → Fin n} (hI : ¬ Function.Injective I) :
    (minor τ s I : Pol Φ n K) = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, I i = I j ∧ i ≠ j := by
    by_contra h
    push Not at h
    exact hI fun i j hij => h i j hij
  unfold minor
  exact Matrix.det_zero_of_row_eq hne (funext fun b => by simp [hij])

omit [Fintype Φ] [DecidableEq Φ] in
/-- **The Leibniz expansion of a minor**: `D_I = Σ_π sign(π)·∏_i x_{τ, I(π i), i}`. -/
theorem minor_eq_sum (τ : Φ) (s : Fin n) (I : Fin (s + 1) → Fin n) :
    (minor τ s I : Pol Φ n K) =
      ∑ π : Equiv.Perm (Fin (s + 1)), ((Equiv.Perm.sign π : ℤ) : Pol Φ n K) *
        ∏ i, X (τ, I (π i), Fin.castLE s.isLt i) := by
  rw [minor, Matrix.det_apply]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  simp [xMat]

omit [Fintype Φ] [DecidableEq Φ] in
/-- **Cauchy–Binet with sorted rows** for a leading minor of `gᵀx`, `g_τ = (x_{τ,a,b})`: a sum over the strictly
increasing row maps `I` of the minor of `g` on the rows `I` times the minor of `x` on the rows `I`. -/
theorem lsub_minor_sorted (x : Φ × Fin n × Fin n → K) (τ : Φ) (s : Fin n) :
    lsub (fun σ => (Matrix.of fun a b => x (σ, a, b)).transpose) (minor τ s (Fin.castLE s.isLt)) =
      ∑ I : Fin (s + 1) → Fin n, C ((if StrictMono I then 1 else 0) * eval x (minor τ s I)) * minor τ s I := by
  rw [lsub_minor, sum_eq_sum_sorted]
  · refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs with hI
    · have h := minor_eq_sum (K := K) τ s I
      rw [one_mul]
      conv_rhs => arg 2; rw [h]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun π _ => ?_
      rw [minor_comp_perm, map_mul, map_intCast, map_mul, map_intCast]
      simp only [Function.comp_apply]
      ring
    · rw [zero_mul, map_zero, zero_mul]
  · intro f hf
    rw [minor_eq_zero hf, map_zero, map_zero, zero_mul]

/-- **The indicator of sorted rows**: `1` if every minor of the bideterminant has strictly increasing rows. -/
def sortedInd (ν : Φ → Fin n → ℕ) (rows : BRows Φ n ν) : K :=
  ∏ τ, ∏ s : Fin n, ∏ c, if StrictMono (rows τ s c) then 1 else 0

/-- **Cauchy–Binet with sorted rows for `hw_ν`**: `hw_ν(gᵀx) = Σ_{rows sorted} bidet_rows(g)·bidet_rows(x)`,
`g_τ = (x_{τ,a,b})`. -/
theorem lsub_hw_sorted (x : Φ × Fin n × Fin n → K) (ν : Φ → Fin n → ℕ) :
    lsub (fun σ => (Matrix.of fun a b => x (σ, a, b)).transpose) (hw K ν) =
      ∑ rows : BRows Φ n ν, C (sortedInd ν rows * eval x (bidet K ν rows)) * bidet K ν rows := by
  rw [hw, map_prod]
  simp only [map_prod, lsub_minor_sorted, ← Fin.prod_const, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun rows _ => ?_
  simp only [bidet, sortedInd, map_prod, map_mul, Finset.prod_mul_distrib]

omit [DecidableEq Φ] in
/-- **The sorted indicator is `0` or `1`**, so it lies in every subring. -/
theorem sortedInd_mem (A : Subring K) (ν : Φ → Fin n → ℕ) (rows : BRows Φ n ν) : sortedInd ν rows ∈ A :=
  A.prod_mem fun τ _ => A.prod_mem fun s _ => A.prod_mem fun c _ => by
    split_ifs
    · exact A.one_mem
    · exact A.zero_mem

/-- **The reproducing formula with sorted rows**: for `F ∈ ∇_K(ν)`,
`κ·F = Σ_{rows sorted} ⟨bidet_rows, F⟩·bidet_rows`, `κ = ⟨hw_ν, hw_ν⟩`. At a point `x`,
`κ·F(x) = ⟨hw_ν, F(g·)⟩ = ⟨hw_ν(gᵀ·), F⟩` (`fock_hw`, `fock_lsub`), expanded by `lsub_hw_sorted`. -/
theorem kappa_mul_eq_sum [CharZero K] {ν : Φ → Fin n → ℕ} (hν : ∀ σ, Antitone (ν σ)) {F : Pol Φ n K}
    (hF : F ∈ nabla K ν) :
    C (fockWith (RingHom.id K) (hw K ν) (hw K ν)) * F =
      ∑ rows : BRows Φ n ν, C (sortedInd ν rows * fockWith (RingHom.id K) (bidet K ν rows) F) *
        bidet K ν rows := by
  refine MvPolynomial.funext fun x => ?_
  have h := fock_hw hν (lsub_mem_nabla (fun σ => Matrix.of fun a b => x (σ, a, b)) hF)
  rw [eval_lsub, ← fock_lsub, lsub_hw_sorted, fock_sum_left] at h
  simp only [fock_C_mul_left] at h
  have hx : (fun p : Φ × Fin n × Fin n => Matrix.of (fun a b => x (p.1, a, b)) p.2.1 p.2.2) = x :=
    funext fun _ => rfl
  rw [hx] at h
  simp only [map_mul, eval_C, map_sum]
  rw [mul_comm, ← h]
  exact Finset.sum_congr rfl fun rows _ => by ring

/-- **`Δ_A ⊆ ∇_A`** (the first half of the sandwich): for every subring `A` of a field of characteristic `0`, the
Fock dual `Δ_A(ν)` of `∇_A(ν)` lies in `∇_A(ν)`. By the reproducing formula `kappa_mul_eq_sum`,
`F = Σ_{rows sorted} (⟨F, bidet_rows⟩/κ)·bidet_rows`, and for `F ∈ Δ_A` the coefficients lie in `A`. -/
theorem Delta_subset_nablaInt [CharZero K] (A : Subring K) {ν : Φ → Fin n → ℕ} (hν : ∀ σ, Antitone (ν σ)) :
    Delta A ν ⊆ (nablaInt A ν : Set (Pol Φ n K)) := by
  rintro F ⟨hF, hA⟩
  set κ := fockWith (RingHom.id K) (hw K ν) (hw K ν) with hκdef
  have hκ : κ ≠ 0 := fock_hw_hw_ne_zero ν
  have key := kappa_mul_eq_sum hν hF
  rw [← hκdef] at key
  have hF' : F = ∑ rows : BRows Φ n ν,
      (sortedInd ν rows * (fockWith (RingHom.id K) F (bidet K ν rows) / κ)) • bidet K ν rows := by
    calc F = C κ⁻¹ * (C κ * F) := by rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hκ, C_1, one_mul]
      _ = _ := by
        rw [key, Finset.mul_sum]
        refine Finset.sum_congr rfl fun rows _ => ?_
        rw [smul_eq_C_mul, ← mul_assoc, ← C_mul, fock_comm]
        congr 2
        field_simp
  rw [hF', SetLike.mem_coe]
  refine Submodule.sum_mem _ fun rows _ => ?_
  have hmem := A.mul_mem (sortedInd_mem A ν rows) (hA rows)
  exact Submodule.smul_mem _ (⟨_, hmem⟩ : A) (Submodule.subset_span ⟨rows, rfl⟩)

end Reproduce

/-! ## Valuations of factorials: Kummer's bound for multinomials -/

section Kummer

/-- **The floor of a sum** exceeds the sum of the floors by less than the number of terms:
`⌊Σ_a x_a/q⌋ ≤ Σ_a ⌊x_a/q⌋ + (|s| − 1)`. -/
theorem sum_div_le {ι : Type*} (s : Finset ι) (x : ι → ℕ) (q : ℕ) :
    (∑ a ∈ s, x a) / q ≤ ∑ a ∈ s, x a / q + (s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have h1 := Nat.add_div_le_div_add_div_add_one (x a) (∑ b ∈ s, x b) q
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      simp
    · have := hs.card_pos
      omega

/-- **Kummer's bound for multinomials**: `v_p(m!) ≤ Σ_a v_p(α_a!) + (|s| − 1)·⌊log_p m⌋` for `m = Σ_a α_a`, by
Legendre's formula `v_p(m!) = Σ_{1 ≤ i ≤ log_p m} ⌊m/p^i⌋` and `sum_div_le` at each `i`. -/
theorem padicValNat_factorial_sum_le {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι) (α : ι → ℕ) :
    padicValNat p (∑ a ∈ s, α a).factorial ≤
      ∑ a ∈ s, padicValNat p (α a).factorial + (s.card - 1) * Nat.log p (∑ a ∈ s, α a) := by
  set m := ∑ a ∈ s, α a
  have hb : Nat.log p m < Nat.log p m + 1 := lt_add_one _
  rw [padicValNat_factorial hb]
  have hα : ∀ a ∈ s, padicValNat p (α a).factorial = ∑ i ∈ Finset.Ico 1 (Nat.log p m + 1), α a / p ^ i := fun a ha =>
    padicValNat_factorial (lt_of_le_of_lt (Nat.log_mono_right
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) ha)) hb)
  rw [Finset.sum_congr rfl hα, Finset.sum_comm]
  calc ∑ i ∈ Finset.Ico 1 (Nat.log p m + 1), m / p ^ i
      ≤ ∑ i ∈ Finset.Ico 1 (Nat.log p m + 1), (∑ a ∈ s, α a / p ^ i + (s.card - 1)) :=
        Finset.sum_le_sum fun i _ => sum_div_le s α _
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, smul_eq_mul, Nat.add_sub_cancel, mul_comm]

/-- **The `p`-part of a quotient**: if every natural number prime to `p` is invertible in the subring `A`, and
`v_p(b) ≤ e + v_p(a)`, then `p^e·a/b ∈ A`. -/
theorem pow_mul_div_mem {K : Type*} [Field K] [CharZero K] (A : Subring K) {p : ℕ} (hp : p.Prime)
    (hA : ∀ m : ℕ, ¬ p ∣ m → (m : K)⁻¹ ∈ A) {a b e : ℕ} (hb : b ≠ 0)
    (hab : padicValNat p b ≤ e + padicValNat p a) : (p : K) ^ e * a / b ∈ A := by
  obtain ⟨a', ea⟩ : ∃ a', a = p ^ padicValNat p a * a' :=
    ⟨ordCompl[p] a, by rw [← Nat.factorization_def a hp]; exact (Nat.ordProj_mul_ordCompl_eq_self a p).symm⟩
  obtain ⟨b', hb', eb⟩ : ∃ b', ¬ p ∣ b' ∧ b = p ^ padicValNat p b * b' :=
    ⟨ordCompl[p] b, Nat.not_dvd_ordCompl hp hb,
      by rw [← Nat.factorization_def b hp]; exact (Nat.ordProj_mul_ordCompl_eq_self b p).symm⟩
  have key : ∀ va vb : ℕ, vb ≤ e + va → (b' : K) ≠ 0 →
      (p : K) ^ e * ((p ^ va * a' : ℕ) : K) / ((p ^ vb * b' : ℕ) : K) = (p : K) ^ (e + va - vb) * a' * (b' : K)⁻¹ :=
    fun va vb h hb0 => by
      have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
      have hpow : (p : K) ^ e * (p : K) ^ va = (p : K) ^ (e + va - vb) * (p : K) ^ vb := by
        rw [← pow_add, ← pow_add, Nat.sub_add_cancel h]
      push_cast
      field_simp
      linear_combination (a' : K) * hpow
  have hb0 : (b' : K) ≠ 0 := Nat.cast_ne_zero.2 fun h => hb (by rw [eb, h, mul_zero])
  have e1 := key _ _ hab hb0
  rw [← ea, ← eb] at e1
  rw [e1]
  exact A.mul_mem (A.mul_mem (A.pow_mem (natCast_mem _ _) _) (natCast_mem _ _)) (hA _ hb')

end Kummer

/-! ## The second half: `p^e·∇_A ⊆ Δ_A` -/

section Second

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {K : Type} [Field K]

/-- **`κ` as a natural number**: `κ = ⟨hw_ν, hw_ν⟩ ∈ ℚ` is a positive integer (`kapN_cast`). -/
def kapN (ν : Φ → Fin n → ℕ) : ℕ := (fockWith (RingHom.id ℚ) (hw ℚ ν) (hw ℚ ν)).num.toNat

omit [DecidableEq Φ] in
/-- **`hw_ν` is a bideterminant**, with the leading rows in every minor. -/
theorem hw_eq_bidet (L : Type) [Field L] (ν : Φ → Fin n → ℕ) :
    hw L ν = bidet L ν fun _ s _ => Fin.castLE s.isLt := by
  simp [hw, bidet, Finset.prod_const]

omit [DecidableEq Φ] in
/-- **`κ` is a natural number**: `hw_ν` has integer coefficients (`coeff_bidet_mem`), and `κ ≥ 0`. -/
theorem kapN_cast (ν : Φ → Fin n → ℕ) :
    ((kapN ν : ℕ) : ℚ) = fockWith (RingHom.id ℚ) (hw ℚ ν) (hw ℚ ν) := by
  set q := fockWith (RingHom.id ℚ) (hw ℚ ν) (hw ℚ ν) with hq
  have hc : ∀ d, (hw ℚ ν).coeff d ∈ (Int.castRingHom ℚ).range := fun d => by
    rw [hw_eq_bidet]
    exact coeff_bidet_mem _ ν _ d
  have hint : q ∈ (Int.castRingHom ℚ).range := by
    rw [hq, fock_eq_sum_left (subset_refl _)]
    exact Subring.sum_mem _ fun d _ => Subring.mul_mem _ (Subring.mul_mem _ (hc d) (hc d))
      (Subring.prod_mem _ fun _ _ => natCast_mem _ _)
  have hpos : 0 ≤ q := by
    rw [hq, fock_eq_sum_left (subset_refl _)]
    exact Finset.sum_nonneg fun d _ => mul_nonneg (mul_self_nonneg _)
      (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
  obtain ⟨z, hz⟩ := hint
  simp only [Int.coe_castRingHom] at hz
  have hz0 : 0 ≤ z := by exact_mod_cast hz ▸ hpos
  show ((q.num.toNat : ℕ) : ℚ) = q
  rw [← hz, Rat.num_intCast]
  exact_mod_cast Int.toNat_of_nonneg hz0

omit [DecidableEq Φ] in
/-- **`κ ≠ 0`.** -/
theorem kapN_ne_zero (ν : Φ → Fin n → ℕ) : kapN ν ≠ 0 := fun h => by
  have := kapN_cast (Φ := Φ) ν
  rw [h, Nat.cast_zero] at this
  exact fock_hw_hw_ne_zero (L := ℚ) ν this.symm

omit [DecidableEq Φ] in
/-- **`κ` over any field of characteristic `0`** is the natural number `kapN ν`. -/
theorem fock_hw_eq_kapN [CharZero K] (ν : Φ → Fin n → ℕ) :
    fockWith (RingHom.id K) (hw K ν) (hw K ν) = (kapN ν : K) := by
  rw [← WeylFock.map_hw (L := K), ← map_fockWith_id, ← kapN_cast, map_natCast]

/-- **The loss of a column of degree `m`**: `v_p(m!) − (k − 1)·⌊log_p m⌋`, a lower bound for `v_p(∏_a α_a!)` over
the `k`-part compositions `α` of `m` (`padicValNat_factorial_sum_le`). -/
def colBound (p k m : ℕ) : ℕ := padicValNat p m.factorial - (k - 1) * Nat.log p m

/-- **The valuation of a product of nonzero naturals** is the sum of the valuations. -/
theorem padicValNat_prod {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) : padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, padicValNat.mul (hf a (Finset.mem_insert_self a s))
      (Finset.prod_ne_zero_iff.2 fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- **The factorial of an exponent of column weight `ν`** has `v_p(d!) ≥ Σ_{τ,b} colBound(ν_{τ,b})`, column by
column (`padicValNat_factorial_sum_le`). -/
theorem sum_colBound_le {p : ℕ} [Fact p.Prime] {ν : Φ → Fin n → ℕ} {d : Φ × Fin n × Fin n →₀ ℕ}
    (hd : Finsupp.weight (colW Φ n) d = ν) :
    ∑ τ, ∑ b, colBound p n (ν τ b) ≤ padicValNat p (∏ q, (d q).factorial) := by
  rw [padicValNat_prod _ _ fun q _ => Nat.factorial_ne_zero _, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_le_sum fun b _ => ?_
  have hm : ν τ b = ∑ a, d (τ, a, b) := by rw [← hd, weight_colW_apply]
  have := padicValNat_factorial_sum_le (p := p) Finset.univ fun a => d (τ, a, b)
  rw [Finset.card_univ, Fintype.card_fin, ← hm] at this
  exact Nat.sub_le_iff_le_add.2 this

/-- **The sandwich exponent** `e(ν) = v_p(κ) − Σ_{τ,b} colBound(ν_{τ,b})`, truncated at `0`; it is at most
`v_p(κ/∏ν_{τ,b}!) + (k − 1)·Σ_{τ,b} ⌊log_p ν_{τ,b}⌋` when that is nonnegative. -/
def sandExp (p : ℕ) (ν : Φ → Fin n → ℕ) : ℕ := padicValNat p (kapN ν) - ∑ τ, ∑ b, colBound p n (ν τ b)

/-- **`∇_A ⊆ ∇_K`**: bideterminants lie in `∇_K(ν)`. -/
theorem nablaInt_subset_nabla [CharZero K] (A : Subring K) {ν : Φ → Fin n → ℕ} (hν : ∀ σ, Antitone (ν σ))
    {F : Pol Φ n K} (hF : F ∈ nablaInt A ν) : F ∈ nabla K ν := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨rows, rfl⟩ := hx
    exact bidet_mem_nabla hν rows
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ (a : K) hx

omit [DecidableEq Φ] in
/-- **`∇_A` has coefficients in `A`**: bideterminants have integer coefficients. -/
theorem coeff_mem_of_nablaInt (A : Subring K) {ν : Φ → Fin n → ℕ} {F : Pol Φ n K} (hF : F ∈ nablaInt A ν)
    (d : Φ × Fin n × Fin n →₀ ℕ) : F.coeff d ∈ A := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨rows, rfl⟩ := hx
    exact coeff_bidet_mem A ν rows d
  | zero => simp
  | add x y _ _ hx hy => simpa using A.add_mem hx hy
  | smul a x _ hx => rw [Subring.smul_def, coeff_smul, smul_eq_mul]; exact A.mul_mem a.2 hx

/-- **`p^e·∇_A ⊆ Δ_A`** (the second half of the sandwich), with `e = sandExp p ν`, for a subring `A` in which every
natural number prime to `p` is invertible: `⟨p^e F, β⟩/κ = Σ_d F_d·β_d·(p^e d!/κ)` with `F_d, β_d ∈ A`, and
`v_p(κ) ≤ e + v_p(d!)` for every exponent `d` of column weight `ν` (`sum_colBound_le`). -/
theorem pow_smul_mem_Delta [CharZero K] (A : Subring K) {p : ℕ} (hp : p.Prime)
    (hA : ∀ m : ℕ, ¬ p ∣ m → (m : K)⁻¹ ∈ A) {ν : Φ → Fin n → ℕ} (hν : ∀ σ, Antitone (ν σ)) {F : Pol Φ n K}
    (hF : F ∈ nablaInt A ν) : (p : K) ^ sandExp p ν • F ∈ Delta A ν := by
  have := Fact.mk hp
  have hFn := nablaInt_subset_nabla A hν hF
  refine ⟨Submodule.smul_mem _ _ hFn, fun rows => ?_⟩
  rw [fock_hw_eq_kapN, fock_eq_sum_left (S := F.support) support_smul, Finset.sum_div]
  refine A.sum_mem fun d hd => ?_
  have hcol : Finsupp.weight (colW Φ n) d = ν := (mem_nabla_iff.1 hFn).1 (mem_support_iff.1 hd)
  have hfact : (fact d : K) = ((∏ q, (d q).factorial : ℕ) : K) := by simp [fact]
  have e : (((p : K) ^ sandExp p ν • F).coeff d * (bidet K ν rows).coeff d * fact d) / (kapN ν : K) =
      F.coeff d * (bidet K ν rows).coeff d *
        ((p : K) ^ sandExp p ν * ((∏ q, (d q).factorial : ℕ) : K) / (kapN ν : K)) := by
    rw [coeff_smul, smul_eq_mul, hfact]
    ring
  rw [e]
  refine A.mul_mem (A.mul_mem (coeff_mem_of_nablaInt A hF d) (coeff_bidet_mem A ν rows d))
    (pow_mul_div_mem A hp hA (kapN_ne_zero ν) ?_)
  have := sum_colBound_le (p := p) hcol
  unfold sandExp
  omega

omit [DecidableEq Φ] in
/-- **The size of the exponent, given the Fock norm of `hw_ν`.** If, block by block,
`κ·∏_{i<j}(ν_i − ν_j + j − i) = ∏_b ν_b!·∏_{i<j}(ν_i + j − i)` (the classical value of `⟨hw_ν, hw_ν⟩`, not
proved here), then `sandExp p ν ≤ Σ_τ (Σ_{i<j} ⌊log_p(ν_{τ,i} + j − i)⌋ + (k − 1)·Σ_b ⌊log_p ν_{τ,b}⌋)`, as
`v_p(κ) ≤ v_p(∏ν!) + v_p(∏(ν_i + j − i))` and `v_p(m) ≤ ⌊log_p m⌋`. -/
theorem sandExp_le {p : ℕ} (hp : p.Prime) {ν : Φ → Fin n → ℕ}
    (hκ : kapN ν * ∏ τ, ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (ν τ i - ν τ j + (j.val - i.val)) =
      (∏ τ, ∏ b, (ν τ b).factorial) * ∏ τ, ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (ν τ i + (j.val - i.val))) :
    sandExp p ν ≤ ∑ τ, (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, Nat.log p (ν τ i + (j.val - i.val)) +
      (n - 1) * ∑ b, Nat.log p (ν τ b)) := by
  have := Fact.mk hp
  have hD : ∏ τ, ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (ν τ i - ν τ j + (j.val - i.val)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2
      fun j hj => by have := Finset.mem_Ioi.1 hj; omega
  have hM : ∏ τ, ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (ν τ i + (j.val - i.val)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2
      fun j hj => by have := Finset.mem_Ioi.1 hj; omega
  have hN : ∏ τ, ∏ b, (ν τ b).factorial ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun b _ => Nat.factorial_ne_zero _
  have h1 := congrArg (padicValNat p) hκ
  rw [padicValNat.mul (kapN_ne_zero ν) hD, padicValNat.mul hN hM] at h1
  have hvM : padicValNat p (∏ τ, ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (ν τ i + (j.val - i.val))) ≤
      ∑ τ, ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, Nat.log p (ν τ i + (j.val - i.val)) := by
    rw [padicValNat_prod _ _ fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2
      fun j hj => by have := Finset.mem_Ioi.1 hj; omega]
    refine Finset.sum_le_sum fun τ _ => ?_
    rw [padicValNat_prod _ _ fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => by
      have := Finset.mem_Ioi.1 hj; omega]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [padicValNat_prod _ _ fun j hj => by have := Finset.mem_Ioi.1 hj; omega]
    exact Finset.sum_le_sum fun j _ => padicValNat_le_nat_log _
  have hvN : padicValNat p (∏ τ, ∏ b, (ν τ b).factorial) ≤
      ∑ τ, ∑ b, colBound p n (ν τ b) + (n - 1) * ∑ τ, ∑ b, Nat.log p (ν τ b) := by
    rw [padicValNat_prod _ _ fun τ _ => Finset.prod_ne_zero_iff.2 fun b _ => Nat.factorial_ne_zero _,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun τ _ => ?_
    rw [padicValNat_prod _ _ fun b _ => Nat.factorial_ne_zero _, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun b _ => le_tsub_add
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold sandExp
  omega

end Second

/-! ## Over a local ring: the sandwich -/

section Local

/-- **Prime-to-`p` integers are units of a local ring in which `p` is not**: Bézout `a·m + b·p = 1`, and in a local
ring one of two summands of a unit is a unit. -/
theorem isUnit_natCast_of_not_dvd {O : Type*} [CommRing O] [IsLocalRing O] {p : ℕ} (hp : p.Prime)
    (hpO : ¬ IsUnit (p : O)) {m : ℕ} (hm : ¬ p ∣ m) : IsUnit (m : O) := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  have h1 : (a : O) * p + (b : O) * m = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → O) hab
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (h1 ▸ isUnit_one) with h | h
  · exact absurd (isUnit_of_mul_isUnit_right h) hpO
  · exact isUnit_of_mul_isUnit_right h

/-- **Prime-to-`p` integers are invertible in `O ⊆ Kf`**, `O` local with `p` not a unit. -/
theorem inv_natCast_mem_Oint {O Kf : Type} [CommRing O] [IsLocalRing O] [Field Kf] [Algebra O Kf] {p : ℕ}
    (hp : p.Prime) (hpO : ¬ IsUnit (p : O)) {m : ℕ} (hm : ¬ p ∣ m) : (m : Kf)⁻¹ ∈ Oint O Kf := by
  obtain ⟨u, hu⟩ := isUnit_natCast_of_not_dvd hp hpO hm
  refine ⟨(u⁻¹ : Oˣ), eq_inv_of_mul_eq_one_left ?_⟩
  rw [← map_natCast (algebraMap O Kf), ← hu, ← map_mul, Units.inv_mul, map_one]

/-- **The sandwich** (L3), block-wise, over a local ring `O ⊆ Kf` (`Kf` of characteristic `0`) in which the prime
`p` is not a unit: `Δ_O(ν) ⊆ ∇_O(ν)` and `p^e·∇_O(ν) ⊆ Δ_O(ν)` with `e = sandExp p ν`. The one-block case is
`β = Unit`. -/
theorem sandwich {O Kf : Type} [CommRing O] [IsLocalRing O] [Field Kf] [CharZero Kf] [Algebra O Kf] {p : ℕ}
    (hp : p.Prime) (hpO : ¬ IsUnit (p : O)) {β : Type} [Fintype β] [DecidableEq β] {k : ℕ}
    {ν : β → Fin k → ℕ} (hν : ∀ b, Antitone (ν b)) :
    (∀ F ∈ Delta (Oint O Kf) ν, F ∈ (nablaInt (Oint O Kf) ν : Set (Pol β k Kf))) ∧
      ∀ F ∈ (nablaInt (Oint O Kf) ν : Set (Pol β k Kf)), ((p : Kf) ^ sandExp p ν) • F ∈ Delta (Oint O Kf) ν :=
  ⟨fun _ hF => Delta_subset_nablaInt _ hν hF,
    fun _ hF => pow_smul_mem_Delta _ hp (fun _ hm => inv_natCast_mem_Oint hp hpO hm) hν hF⟩

end Local

/-! ## The local Weyl lattices of tuples and the local forms -/

section Forms

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf] {ι : Qq →+* Kf}
  {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ} {V : Type} [Fintype V] [DecidableEq V]

omit [CharZero Kf] [Fintype V] [DecidableEq V] in
/-- **`p` is not a unit of `O`**: `p = ϖ²` with `ϖ` a uniformiser. -/
theorem not_isUnit_natCast_p (hU : Unram p n' W Qq O Kf ι σ j ϖ) : ¬ IsUnit (p : O) := by
  rw [← hU.sq, isUnit_pow_iff two_ne_zero]
  exact hU.unif_O.not_isUnit

/-- **The exponent of a tuple**: `sandExp` of the block weights `natW (blockWt lam0 b)`. -/
abbrev tupExp (p : ℕ) (lam0 : V → Fin n' → Fin k → ℤ) : ℕ := sandExp p fun b => natW (blockWt lam0 b)

omit [Fintype V] [DecidableEq V] in
/-- **Dominant weights give antitone block shapes.** -/
theorem antitone_natW_blockWt {lam0 : V → Fin n' → Fin k → ℤ} (hlam : ∀ v s, Antitone (lam0 v s))
    (b : V × Fin n') : Antitone (natW (blockWt lam0 b)) :=
  natW_antitone (antitone_blockWt hlam b)

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`Δ_L ⊆ ∇_L`** for every tuple `L` and dominant weights (`Delta_subset_nablaInt` in the coordinates of basis
matrices of the blocks). -/
theorem DeltaT_subset_NablaT {lam0 : V → Fin n' → Fin k → ℤ} (hlam : ∀ v s, Antitone (lam0 v s))
    (L : V → Submodule W (Fin k → Qq)) : DeltaT O ι σ lam0 L ⊆ NablaT O ι σ lam0 L := by
  rintro F ⟨hF, C, hC, hD⟩
  exact ⟨hF, C, hC, Delta_subset_nablaInt _ (antitone_natW_blockWt hlam) hD⟩

/-- **`p^e·∇_L ⊆ Δ_L`** for every tuple `L` and dominant weights, `e = tupExp p lam0` (`pow_smul_mem_Delta` in the
coordinates of basis matrices of the blocks). -/
theorem pow_smul_mem_DeltaT (hU : Unram p n' W Qq O Kf ι σ j ϖ) {lam0 : V → Fin n' → Fin k → ℤ}
    (hlam : ∀ v s, Antitone (lam0 v s)) {L : V → Submodule W (Fin k → Qq)} {F : Pol (V × Fin n') k Kf}
    (hF : F ∈ NablaT O ι σ lam0 L) : (p : Kf) ^ tupExp p lam0 • F ∈ DeltaT O ι σ lam0 L := by
  obtain ⟨hF, C, hC, hN⟩ := hF
  refine ⟨Submodule.smul_mem _ _ hF, C, hC, ?_⟩
  rw [twist_smul]
  exact pow_smul_mem_Delta _ hU.prime (fun _ hm => inv_natCast_mem_Oint hU.prime (not_isUnit_natCast_p hU) hm)
    (antitone_natW_blockWt hlam) hN

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **The sandwich for the local forms** of a level (L1): `M ⊆ M∇`, for `M` and `M∇` the forms with coefficients in
`Δ_L` and `∇_L` (`DeltaT_subset_NablaT`). -/
theorem forms_DeltaT_subset (C : Level V k Qq O) {lam0 : V → Fin n' → Fin k → ℤ}
    (hlam : ∀ v s, Antitone (lam0 v s)) :
    C.forms ι σ lam0 (DeltaT (W := W) O ι σ lam0) ⊆ C.forms ι σ lam0 (NablaT (W := W) O ι σ lam0) :=
  fun _ hF => ⟨fun L hL => DeltaT_subset_NablaT hlam L (hF.1 L hL), hF.2.1, hF.2.2⟩

/-- **The sandwich for the local forms** of a level (L1): `p^e·M∇ ⊆ M`, `e = tupExp p lam0`
(`pow_smul_mem_DeltaT`; the action on coefficients is linear). -/
theorem pow_smul_mem_forms (hU : Unram p n' W Qq O Kf ι σ j ϖ) (C : Level V k Qq O)
    {lam0 : V → Fin n' → Fin k → ℤ} (hlam : ∀ v s, Antitone (lam0 v s))
    {F : (V → Submodule W (Fin k → Qq)) → Pol (V × Fin n') k Kf} (hF : F ∈ C.forms ι σ lam0 (NablaT O ι σ lam0)) :
    (p : Kf) ^ tupExp p lam0 • F ∈ C.forms ι σ lam0 (DeltaT O ι σ lam0) := by
  refine ⟨fun L hL => pow_smul_mem_DeltaT hU hlam (hF.1 L hL), fun L hL => ?_, fun γ L => ?_⟩
  · rw [Pi.smul_apply, hF.2.1 L hL, smul_zero]
  · rw [Pi.smul_apply, Pi.smul_apply, hF.2.2 γ L, map_smul, smul_comm]

end Forms

end

end WeylSandwich
