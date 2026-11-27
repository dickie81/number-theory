import LocalRank

/-!
# Gaussian binomials, the edge count and Hecke adjointness

D2-4 of the served valuation of the theta chain (layer 2, lattices).

**Gaussian binomials** (`qBinom`), by the q-Pascal recursion `[n+1, k+1] = [n, k] + q^{k+1}·[n, k+1]`. They satisfy
**q-Vandermonde** in the form whose `q`-power does not depend on `n` (`qBinom_add`):
`[m+n, k] = Σ_j q^{(m−j)(k−j)}·[m, j]·[n, k−j]` (induction on `m`), and **count subspaces**
(`card_subspace_eq_qBinom`): an `n`-dimensional space over a field with `q` elements has `[n, m]_q` subspaces of
dimension `m` (from `LocalRank.card_subspace_mul` and `[n, m]·∏_{i<m}(q^{m−i} − 1) = ∏_{i<m}(q^{n−i} − 1)`). Hence
the subspaces of dimension `m` inside a subspace `E` number `[dim E, m]` (`card_subspace_le`), and those of codimension
`i` containing `E` number `[n − dim E, i]` (`card_subspace_ge`, through `V/E` and `card_subspace_compl`).

**The edge count** (`edge_count`, `N′ = N + t + 1`): for `x·L ⊆ L′` (`MapsInto`), let `φ̄ : p⁻¹L/L → L′/pL′`,
`y ↦ x(py)`, of rank `ρ`. The type-`i` edges `L₁ ⊂ L′` with `x·L ⊆ L₁` are the planes of codimension `i` in `L′/pL′`
containing the image of `φ̄` (`LocalRank.edgeEquivPlane`): `[N′ − ρ, i]_q` of them. The type-`r` edges `A ⊃ L` with
`x·A ⊆ L′` are the planes of dimension `r` in `p⁻¹L/L` inside `ker φ̄` (`LocalRank.outEdgeEquivPlane`; `xy ∈ L′` iff
`φ̄(y) = 0`): `[N − ρ, r]_q`. q-Vandermonde with `m = t + 1`, `n = N − ρ` relates the two.

**Hecke adjointness** (`hecke_adjoint`): with class representatives `R` of the lattice tuples under a level
(`ClassReps`), the mass-weighted sum `Σ_{L ∈ R} |Stab L|⁻¹·Σ_{edges up} φ` equals the sum over edges down, for a
`Γ`-invariant `φ`. Both are `Σ_{L ∈ R} Σ_{L′} Σ_{γ : γL′ ∈ R} φ(L, L′)/(|Stab L|·|Stab γL′|)` (the inner sum has
`|Stab|` terms), and `(L, L′, γ) ↦ (γL′, γL, γ⁻¹)` exchanges the two sides.
-/

open Finset

open scoped Matrix

namespace KernelCount

/-! ## Gaussian binomials -/

section QBinom

/-- **The Gaussian binomial** `[n, k]_q` (q-Pascal recursion). -/
def qBinom (q : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1)

/-- **`[n, 0] = 1`.** -/
@[simp] theorem qBinom_zero_right (q n : ℕ) : qBinom q n 0 = 1 := by
  cases n <;> rfl

/-- **`[0, k + 1] = 0`.** -/
@[simp] theorem qBinom_zero_succ (q k : ℕ) : qBinom q 0 (k + 1) = 0 := rfl

/-- **q-Pascal.** -/
theorem qBinom_succ_succ (q n k : ℕ) :
    qBinom q (n + 1) (k + 1) = qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1) := rfl

/-- **`[n, k] = 0` for `n < k`.** -/
theorem qBinom_eq_zero_of_lt (q : ℕ) : ∀ {n k : ℕ}, n < k → qBinom q n k = 0
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [qBinom_succ_succ, qBinom_eq_zero_of_lt q (by omega : n < k), qBinom_eq_zero_of_lt q (by omega : n < k + 1)]
    simp

/-- **q-Vandermonde** in the form whose `q`-power does not depend on `n`:
`[m + n, k] = Σ_{j ≤ k} q^{(m−j)(k−j)}·[m, j]·[n, k − j]`. -/
theorem qBinom_add (q m n k : ℕ) :
    qBinom q (m + n) k = ∑ j ∈ range (k + 1), q ^ ((m - j) * (k - j)) * qBinom q m j * qBinom q n (k - j) := by
  induction m generalizing k with
  | zero =>
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
      simp
    · intro h
      simp at h
  | succ m ih =>
    cases k with
    | zero => simp
    | succ k =>
      have key : ∀ j ∈ range (k + 1),
          q ^ ((m + 1 - (j + 1)) * (k + 1 - (j + 1))) * qBinom q (m + 1) (j + 1) * qBinom q n (k + 1 - (j + 1)) =
            q ^ ((m - j) * (k - j)) * qBinom q m j * qBinom q n (k - j) +
              q ^ (k + 1) * (q ^ ((m - (j + 1)) * (k + 1 - (j + 1))) * qBinom q m (j + 1) *
                qBinom q n (k + 1 - (j + 1))) := by
        intro j hj
        have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        rw [qBinom_succ_succ, Nat.add_sub_add_right, Nat.add_sub_add_right]
        by_cases hjm : j + 1 ≤ m
        · obtain ⟨a, ha⟩ : ∃ a, m - j = a + 1 ∧ m - (j + 1) = a := ⟨m - (j + 1), by omega, rfl⟩
          obtain ⟨c, hc⟩ : ∃ c, k = j + c := ⟨k - j, by omega⟩
          subst hc
          rw [ha.1, ha.2, Nat.add_sub_cancel_left]
          ring
        · rw [qBinom_eq_zero_of_lt q (by omega : m < j + 1)]
          ring
      rw [show m + 1 + n = (m + n) + 1 by omega, qBinom_succ_succ, ih k, ih (k + 1),
        Finset.sum_range_succ' (fun j => q ^ ((m + 1 - j) * (k + 1 - j)) * qBinom q (m + 1) j *
          qBinom q n (k + 1 - j)) (k + 1),
        Finset.sum_range_succ' (fun j => q ^ ((m - j) * (k + 1 - j)) * qBinom q m j * qBinom q n (k + 1 - j)) (k + 1),
        Finset.sum_congr rfl key, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
      simp only [Nat.sub_zero, qBinom_zero_right]
      ring

/-- `∏_{i<m}(q^{n−i} − 1)`. -/
private def gProd (q n m : ℕ) : ℤ := ∏ i ∈ range m, ((q : ℤ) ^ (n - i) - 1)

/-- **`[n, m]·∏_{i<m}(q^{m−i} − 1) = ∏_{i<m}(q^{n−i} − 1)`** (induction with q-Pascal). -/
private theorem qBinom_mul_gProd (q : ℕ) : ∀ n m : ℕ, (qBinom q n m : ℤ) * gProd q m m = gProd q n m
  | _, 0 => by simp [gProd]
  | 0, m + 1 => by
    rw [qBinom_zero_succ, Nat.cast_zero, zero_mul, gProd, Finset.prod_eq_zero (Finset.mem_range.2 m.succ_pos)]
    simp
  | n + 1, m + 1 => by
    have hs : ∀ a, gProd q (a + 1) (m + 1) = ((q : ℤ) ^ (a + 1) - 1) * gProd q a m := fun a => by
      rw [gProd, gProd, Finset.prod_range_succ', mul_comm]
      simp [Nat.add_sub_add_right]
    have h1 := qBinom_mul_gProd q n m
    have h2 := qBinom_mul_gProd q n (m + 1)
    have h3 : gProd q n (m + 1) = gProd q n m * ((q : ℤ) ^ (n - m) - 1) := Finset.prod_range_succ _ _
    rw [hs m, h3] at h2
    rw [qBinom_succ_succ, hs, hs, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    by_cases hmn : m ≤ n
    · have e : (q : ℤ) ^ (n + 1) = (q : ℤ) ^ (m + 1) * (q : ℤ) ^ (n - m) := by
        rw [← pow_add]
        congr 1
        omega
      linear_combination ((q : ℤ) ^ (m + 1) - 1) * h1 + (q : ℤ) ^ (m + 1) * h2 -
        gProd q n m * e
    · have h0 : gProd q n m = 0 := Finset.prod_eq_zero (Finset.mem_range.2 (by omega : n < m)) (by simp)
      rw [h0] at h1 h2
      rw [h0]
      linear_combination ((q : ℤ) ^ (m + 1) - 1) * h1 + (q : ℤ) ^ (m + 1) * h2

end QBinom

/-! ## Counting subspaces -/

section Grass

variable {K V : Type} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Finite V]

/-- **Subspaces of dimension `m` number `[n, m]_q`** (`n = dim V`, `q = #K`). -/
theorem card_subspace_eq_qBinom (m : ℕ) :
    Nat.card {U : Submodule K V // Module.finrank K U = m} =
      qBinom (Fintype.card K) (Module.finrank K V) m := by
  have : FiniteDimensional K V := Module.Finite.of_finite
  by_cases hm : m ≤ Module.finrank K V
  swap
  · rw [qBinom_eq_zero_of_lt _ (by omega)]
    have : IsEmpty {U : Submodule K V // Module.finrank K U = m} :=
      ⟨fun U => hm (U.2 ▸ Submodule.finrank_le U.1)⟩
    exact Nat.card_of_isEmpty
  have h := LocalRank.card_subspace_mul (K := K) (V := V) hm
  set q := Fintype.card K
  set n := Module.finrank K V
  have hq : 1 < q := Fintype.one_lt_card
  have hcast : ∀ a b : ℕ, b ≤ a → ((q ^ a - q ^ b : ℕ) : ℤ) = (q : ℤ) ^ (a - b) * (q : ℤ) ^ b - (q : ℤ) ^ b :=
    fun a b hab => by
      rw [Nat.cast_sub (Nat.pow_le_pow_right (by omega) hab), Nat.cast_pow, Nat.cast_pow, ← pow_add,
        Nat.sub_add_cancel hab]
  have hz := congrArg (fun x : ℕ => (x : ℤ)) h
  simp only [Nat.cast_mul, Nat.cast_prod] at hz
  rw [Finset.prod_congr rfl fun (i : Fin m) _ => hcast m i.val (le_of_lt i.isLt),
    Finset.prod_congr rfl fun (i : Fin m) _ => hcast n i.val (by have := i.isLt; omega)] at hz
  have hfac : ∀ a, ∏ i : Fin m, ((q : ℤ) ^ (a - i.val) * (q : ℤ) ^ i.val - (q : ℤ) ^ i.val) =
      (∏ i : Fin m, (q : ℤ) ^ i.val) * ∏ i : Fin m, ((q : ℤ) ^ (a - i.val) - 1) := fun a => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by ring
  rw [hfac, hfac] at hz
  have hP : (∏ i : Fin m, (q : ℤ) ^ i.val) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => by positivity
  have hG : ∀ a, ∏ i : Fin m, ((q : ℤ) ^ (a - i.val) - 1) = gProd q a m := fun a =>
    (Finset.prod_range fun i => (q : ℤ) ^ (a - i) - 1).symm
  rw [hG, hG] at hz
  have hGm : gProd q m m ≠ 0 := Finset.prod_ne_zero_iff.2 fun i hi => by
    have : 1 < (q : ℤ) ^ (m - i) := one_lt_pow₀ (by exact_mod_cast hq) (by simp at hi; omega)
    omega
  have h4 := qBinom_mul_gProd q n m
  have h5 : (Nat.card {U : Submodule K V // Module.finrank K U = m} : ℤ) * gProd q m m =
      (qBinom q n m : ℤ) * gProd q m m :=
    mul_left_cancel₀ hP (by linear_combination hz - (∏ i : Fin m, (q : ℤ) ^ i.val) * h4)
  exact_mod_cast mul_right_cancel₀ hGm h5

/-- **Subspaces of dimension `m` inside `E` number `[dim E, m]_q`** (subspaces of `E`, `Submodule.map E.subtype`). -/
theorem card_subspace_le (E : Submodule K V) (m : ℕ) :
    Nat.card {U : Submodule K V // Module.finrank K U = m ∧ U ≤ E} =
      qBinom (Fintype.card K) (Module.finrank K E) m := by
  rw [← card_subspace_eq_qBinom (V := E) m]
  refine Nat.card_congr
    { toFun := fun U => ⟨U.1.comap E.subtype, ?_⟩
      invFun := fun U => ⟨U.1.map E.subtype, by rw [Submodule.finrank_map_subtype_eq]; exact U.2,
        Submodule.map_subtype_le _ _⟩
      left_inv := fun U => Subtype.ext (by
        change (U.1.comap E.subtype).map E.subtype = U.1
        rw [Submodule.map_comap_subtype, inf_eq_right.2 U.2.2])
      right_inv := fun U => Subtype.ext (Submodule.comap_map_eq_of_injective E.injective_subtype U.1) }
  rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, inf_eq_right.2 U.2.2]
  exact U.2.1

/-- **Subspaces of codimension `i` containing `E` number `[n − dim E, i]_q`** (`n = dim V`): they are the
preimages of the subspaces of `V/E` of dimension `n − dim E − i`, as many as of dimension `i`
(`LocalRank.card_subspace_compl`). -/
theorem card_subspace_ge (E : Submodule K V) {i : ℕ} (hi : i ≤ Module.finrank K V) :
    Nat.card {U : Submodule K V // Module.finrank K U = Module.finrank K V - i ∧ E ≤ U} =
      qBinom (Fintype.card K) (Module.finrank K V - Module.finrank K E) i := by
  have : FiniteDimensional K V := Module.Finite.of_finite
  have : Finite (V ⧸ E) := Finite.of_surjective E.mkQ (Submodule.mkQ_surjective E)
  have hQ := Submodule.finrank_quotient_add_finrank E
  have hcomap : ∀ U : Submodule K (V ⧸ E),
      Module.finrank K (U.comap E.mkQ) = Module.finrank K U + Module.finrank K E := fun U => by
    have hle : E ≤ U.comap E.mkQ := fun x hx => by
      simp [Submodule.mem_comap, (Submodule.Quotient.mk_eq_zero E).2 hx]
    set f : ↥(U.comap E.mkQ) →ₗ[K] V ⧸ E := E.mkQ ∘ₗ (U.comap E.mkQ).subtype
    have hr : LinearMap.range f = U := by
      rw [LinearMap.range_comp, Submodule.range_subtype,
        Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective E)]
    have hk : LinearMap.ker f = E.comap (U.comap E.mkQ).subtype := by
      ext y
      simp [f, Submodule.Quotient.mk_eq_zero]
    have := LinearMap.finrank_range_add_finrank_ker f
    rw [hr, hk, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at this
    exact this.symm
  set n := Module.finrank K V
  set e := Module.finrank K E
  have he : e ≤ n := Submodule.finrank_le E
  have hequiv : {U : Submodule K V // Module.finrank K U = n - i ∧ E ≤ U} ≃
      {U : Submodule K (V ⧸ E) // Module.finrank K U + e = n - i} :=
    { toFun := fun U => ⟨U.1.map E.mkQ, by
        have h := hcomap (U.1.map E.mkQ)
        rw [Submodule.comap_map_mkQ, sup_eq_right.2 U.2.2, U.2.1] at h
        exact h.symm⟩
      invFun := fun U => ⟨U.1.comap E.mkQ, by rw [hcomap]; exact U.2, fun x hx => by
        simp [Submodule.mem_comap, (Submodule.Quotient.mk_eq_zero E).2 hx]⟩
      left_inv := fun U => Subtype.ext (by
        change (U.1.map E.mkQ).comap E.mkQ = U.1
        rw [Submodule.comap_map_mkQ, sup_eq_right.2 U.2.2])
      right_inv := fun U => Subtype.ext
        (Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective E) U.1) }
  rw [Nat.card_congr hequiv]
  by_cases hie : i ≤ n - e
  · rw [show n - e = Module.finrank K (V ⧸ E) by omega, ← card_subspace_eq_qBinom (V := V ⧸ E) i,
      LocalRank.card_subspace_compl (K := K) (V := V ⧸ E) (by omega)]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun U => by omega)
  · rw [qBinom_eq_zero_of_lt _ (by omega)]
    have : IsEmpty {U : Submodule K (V ⧸ E) // Module.finrank K U + e = n - i} := ⟨fun U => by
      have := U.2
      omega⟩
    exact Nat.card_of_isEmpty

end Grass

/-! ## The edge count -/

section Edges

open InertModel LocalRank

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] {n' : ℕ}

/-- `x·L ⊆ L′` for a matrix `x : Qq^N → Qq^{N′}`. -/
def MapsInto {N N' : ℕ} (x : Matrix (Fin N') (Fin N) Qq) (L : Submodule W (Fin N → Qq))
    (L' : Submodule W (Fin N' → Qq)) : Prop :=
  L.map ((Matrix.mulVecLin x).restrictScalars W) ≤ L'

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **`x·L ⊆ L′` pointwise.** -/
theorem mapsInto_iff {N N' : ℕ} {x : Matrix (Fin N') (Fin N) Qq} {L : Submodule W (Fin N → Qq)}
    {L' : Submodule W (Fin N' → Qq)} : MapsInto x L L' ↔ ∀ z ∈ L, x *ᵥ z ∈ L' :=
  ⟨fun h z hz => h ⟨z, hz, rfl⟩, fun h _ ⟨z, hz, e⟩ => e ▸ h z hz⟩

variable {p : ℕ}

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **`p` kills `M/pM`.** -/
theorem smul_resSp {k : ℕ} (M : Submodule W (Fin k → Qq)) (z : resSp p M) : (p : W) • z = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact mem_pId_smul_top.2 ⟨y, rfl⟩

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **`p·(p⁻¹y) = y`.** -/
theorem natCast_smul_inv {k : ℕ} (hp : (p : Qq) ≠ 0) (z : Fin k → Qq) : (p : W) • ((p : Qq)⁻¹ • z) = z := by
  rw [natCast_smul_eq, smul_smul, mul_inv_cancel₀ hp, one_smul]

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **`p` cancels** on `Qq^k`. -/
theorem natCast_smul_cancel {k : ℕ} (hp : (p : Qq) ≠ 0) {a b : Fin k → Qq} (h : (p : W) • a = (p : W) • b) :
    a = b := by
  calc a = (p : Qq)⁻¹ • ((p : W) • a) := by rw [natCast_smul_eq, smul_smul, inv_mul_cancel₀ hp, one_smul]
    _ = (p : Qq)⁻¹ • ((p : W) • b) := by rw [h]
    _ = b := by rw [natCast_smul_eq, smul_smul, inv_mul_cancel₀ hp, one_smul]

/-- **The map `p⁻¹L → L′/pL′`**, `y ↦ x(py)` (into `L′` as `py ∈ L`). -/
def phiW {N N' : ℕ} (x : Matrix (Fin N') (Fin N) Qq) {L : Submodule W (Fin N → Qq)}
    {L' : Submodule W (Fin N' → Qq)} (hx : MapsInto x L L') (hp : (p : Qq) ≠ 0) :
    ↥(pInv p L) →ₗ[W] resSp p L' :=
  (pId W p • (⊤ : Submodule W ↥L')).mkQ ∘ₗ LinearMap.codRestrict L'
    (((Matrix.mulVecLin x).restrictScalars W) ∘ₗ ((p : W) • (pInv p L).subtype))
    (fun y => hx ⟨_, (mem_pInv hp).1 y.2, rfl⟩)

/-- **The map `φ̄ : p⁻¹L/L → L′/pL′`**, `y ↦ x(py)`, over `W/p`. -/
def phiBar {N N' : ℕ} (x : Matrix (Fin N') (Fin N) Qq) {L : Submodule W (Fin N → Qq)}
    {L' : Submodule W (Fin N' → Qq)} (hx : MapsInto x L L') (hp : (p : Qq) ≠ 0) :
    resSp p (pInv p L) →ₗ[W ⧸ pId W p] resSp p L' :=
  LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    ((pId W p • (⊤ : Submodule W ↥(pInv p L))).liftQ (phiW x hx hp) (by
      refine Submodule.smul_le.2 fun r hr y _ => ?_
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      rw [LinearMap.mem_ker, map_smul, mul_smul, smul_resSp, smul_zero]))

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **`φ̄` on a class.** -/
theorem phiBar_mk {N N' : ℕ} (x : Matrix (Fin N') (Fin N) Qq) {L : Submodule W (Fin N → Qq)}
    {L' : Submodule W (Fin N' → Qq)} (hx : MapsInto x L L') (hp : (p : Qq) ≠ 0) (y : ↥(pInv p L)) :
    phiBar x hx hp (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ⟨x *ᵥ ((p : W) • (y : Fin N → Qq)), hx ⟨_, (mem_pInv hp).1 y.2, rfl⟩⟩ :=
  rfl

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **`x·L` lies in the lattice of a plane `U ⊆ L′/pL′` iff the image of `φ̄` does.** -/
theorem mapsInto_ofPlane_iff {N N' : ℕ} (x : Matrix (Fin N') (Fin N) Qq) {L : Submodule W (Fin N → Qq)}
    {L' : Submodule W (Fin N' → Qq)} (hx : MapsInto x L L') (hp : (p : Qq) ≠ 0)
    (U : Submodule (W ⧸ pId W p) (resSp p L')) :
    MapsInto x L (ofPlane p L' U) ↔ LinearMap.range (phiBar x hx hp) ≤ U := by
  constructor
  · rintro h _ ⟨u, rfl⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨w, hw, hwe⟩ := mapsInto_iff.1 h _ ((mem_pInv hp).1 y.2)
    rw [phiBar_mk, show (⟨x *ᵥ ((p : W) • (y : Fin N → Qq)), _⟩ : ↥L') = w from Subtype.ext hwe.symm]
    exact hw
  · intro h
    refine mapsInto_iff.2 fun z hz => ?_
    have hy : (p : Qq)⁻¹ • z ∈ pInv p L := ⟨z, hz, rfl⟩
    have hm := h ⟨Submodule.Quotient.mk ⟨_, hy⟩, rfl⟩
    rw [phiBar_mk] at hm
    refine ⟨⟨x *ᵥ ((p : W) • ((p : Qq)⁻¹ • z)), hx ⟨_, (mem_pInv hp).1 hy, rfl⟩⟩, hm, ?_⟩
    simp only [Submodule.subtype_apply]
    rw [natCast_smul_inv hp]

omit [IsDomain W] [IsDiscreteValuationRing W] in
/-- **The lattice of a plane `U ⊆ p⁻¹L/L` maps into `L′` iff `U ⊆ ker φ̄`** (`xy ∈ L′` iff `x(py) ∈ pL′`). -/
theorem ofPlane_mapsInto_iff {N N' : ℕ} (x : Matrix (Fin N') (Fin N) Qq) {L : Submodule W (Fin N → Qq)}
    {L' : Submodule W (Fin N' → Qq)} (hx : MapsInto x L L') (hp : (p : Qq) ≠ 0)
    (U : Submodule (W ⧸ pId W p) (resSp p (pInv p L))) :
    MapsInto x (ofPlane p (pInv p L) U) L' ↔ U ≤ LinearMap.ker (phiBar x hx hp) := by
  have hxs : ∀ y : Fin N → Qq, x *ᵥ ((p : W) • y) = (p : W) • (x *ᵥ y) := fun y =>
    ((Matrix.mulVecLin x).restrictScalars W).map_smul (p : W) y
  constructor
  · intro h u hu
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have hxy : x *ᵥ (y : Fin N → Qq) ∈ L' := mapsInto_iff.1 h _ ⟨y, hu, rfl⟩
    rw [LinearMap.mem_ker, phiBar_mk,
      show (⟨x *ᵥ ((p : W) • (y : Fin N → Qq)), _⟩ : ↥L') = (p : W) • ⟨x *ᵥ (y : Fin N → Qq), hxy⟩ from
        Subtype.ext (hxs _), Submodule.Quotient.mk_smul, smul_resSp]
  · intro h
    refine mapsInto_iff.2 fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := hz
    have h0 := h hy
    rw [LinearMap.mem_ker, Submodule.mkQ_apply, phiBar_mk, Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨v, hv⟩ := mem_pId_smul_top.1 h0
    have hv' : (p : W) • (v : Fin N' → Qq) = (p : W) • (x *ᵥ (y : Fin N → Qq)) := by
      rw [← hxs]
      exact congrArg Subtype.val hv
    rw [Submodule.subtype_apply, ← natCast_smul_cancel hp hv']
    exact v.2

variable {ι : Qq →+* Kf} {σf : Qq ≃+* Qq} {j : W →+* O} {ϖ : O}

/-- **The edges `L₁ ⊂ L′` of type `i` containing `x·L` number `[N′ − ρ, i]_q`** (`ρ` the rank of `φ̄`): the planes
of codimension `i` in `L′/pL′` containing the image of `φ̄`. -/
theorem ncard_edges_up (hU : Unram p n' W Qq O Kf ι σf j ϖ) {N N' : ℕ} (x : Matrix (Fin N') (Fin N) Qq)
    {L : Submodule W (Fin N → Qq)} {L' : Submodule W (Fin N' → Qq)} (hL' : L'.IsLattice Qq)
    (hx : MapsInto x L L') (i : ℕ) :
    {L₁ | IsEdge (n' := n') p i L₁ L' ∧ MapsInto x L L₁}.ncard =
      qBinom (p ^ n') (N' - Module.finrank (W ⧸ pId W p) (LinearMap.range (phiBar x hx hU.cast_ne_zero))) i := by
  have := isMaximal_pId hU
  let _ := Ideal.Quotient.field (pId W p)
  have := finite_resSp hU hL'
  have := finite_res hU
  let _ : Fintype (W ⧸ pId W p) := Fintype.ofFinite _
  have hq : Fintype.card (W ⧸ pId W p) = p ^ n' := by rw [Fintype.card_eq_nat_card, hU.res_card]
  set φ := phiBar x hx hU.cast_ne_zero
  by_cases hi : i ≤ N'
  · have h := card_subspace_ge (K := W ⧸ pId W p) (V := resSp p L') (LinearMap.range φ) (i := i)
      (by rw [finrank_resSp hU hL']; exact hi)
    rw [finrank_resSp hU hL', hq] at h
    rw [← Nat.card_coe_set_eq, ← h]
    exact Nat.card_congr
      { toFun := fun L₁ => ⟨plane p L' L₁.1, (edgeEquivPlane hU hL' hi ⟨L₁.1, L₁.2.1⟩).2,
          (mapsInto_ofPlane_iff x hx hU.cast_ne_zero _).1
            (by rw [ofPlane_plane L₁.2.1.2.2.1 L₁.2.1.2.2.2.1]; exact L₁.2.2)⟩
        invFun := fun U => ⟨ofPlane p L' U.1, ((edgeEquivPlane hU hL' hi).symm ⟨U.1, U.2.1⟩).2,
          (mapsInto_ofPlane_iff x hx hU.cast_ne_zero _).2 U.2.2⟩
        left_inv := fun L₁ => Subtype.ext (ofPlane_plane L₁.2.1.2.2.1 L₁.2.1.2.2.2.1)
        right_inv := fun U => Subtype.ext (plane_ofPlane L' U.1) }
  · have he : {L₁ | IsEdge (n' := n') p i L₁ L' ∧ MapsInto x L L₁} = ∅ :=
      Set.eq_empty_of_forall_notMem fun L₁ h => hi (le_of_isEdge hU h.1)
    rw [qBinom_eq_zero_of_lt _ (by omega), he, Set.ncard_empty]

/-- **The edges `A ⊃ L` of type `r` with `x·A ⊆ L′` number `[N − ρ, r]_q`**: the planes of dimension `r` in
`p⁻¹L/L` inside `ker φ̄`, of dimension `N − ρ`. -/
theorem ncard_edges_down (hU : Unram p n' W Qq O Kf ι σf j ϖ) {N N' : ℕ} (x : Matrix (Fin N') (Fin N) Qq)
    {L : Submodule W (Fin N → Qq)} {L' : Submodule W (Fin N' → Qq)} (hL : L.IsLattice Qq)
    (hx : MapsInto x L L') (r : ℕ) :
    {A | IsEdge (n' := n') p r L A ∧ MapsInto x A L'}.ncard =
      qBinom (p ^ n') (N - Module.finrank (W ⧸ pId W p) (LinearMap.range (phiBar x hx hU.cast_ne_zero))) r := by
  have := isMaximal_pId hU
  let _ := Ideal.Quotient.field (pId W p)
  have hM := isLattice_pInv hU.cast_ne_zero hL
  have := finite_resSp hU hM
  have := finite_res hU
  let _ : Fintype (W ⧸ pId W p) := Fintype.ofFinite _
  have : FiniteDimensional (W ⧸ pId W p) (resSp p (pInv p L)) := Module.Finite.of_finite
  have hq : Fintype.card (W ⧸ pId W p) = p ^ n' := by rw [Fintype.card_eq_nat_card, hU.res_card]
  set φ := phiBar x hx hU.cast_ne_zero
  have hrk := LinearMap.finrank_range_add_finrank_ker φ
  rw [finrank_resSp hU hM] at hrk
  have h := card_subspace_le (K := W ⧸ pId W p) (V := resSp p (pInv p L)) (LinearMap.ker φ) r
  rw [hq, show Module.finrank (W ⧸ pId W p) (LinearMap.ker φ) = N - Module.finrank (W ⧸ pId W p)
    (LinearMap.range φ) by omega] at h
  have hA : ∀ A, IsEdge (n' := n') p r L A → ofPlane p (pInv p L) (plane p (pInv p L) A) = A := fun A he =>
    ofPlane_plane (fun y hy => (mem_pInv hU.cast_ne_zero).2 (he.2.2.2.1 y hy))
      fun y hy => he.2.2.1 ((mem_pInv hU.cast_ne_zero).1 hy)
  rw [← Nat.card_coe_set_eq, ← h]
  exact Nat.card_congr
    { toFun := fun A => ⟨plane p (pInv p L) A.1, (outEdgeEquivPlane hU hL r ⟨A.1, A.2.1⟩).2,
        (ofPlane_mapsInto_iff x hx hU.cast_ne_zero _).1 (by rw [hA A.1 A.2.1]; exact A.2.2)⟩
      invFun := fun U => ⟨ofPlane p (pInv p L) U.1, ((outEdgeEquivPlane hU hL r).symm ⟨U.1, U.2.1⟩).2,
        (ofPlane_mapsInto_iff x hx hU.cast_ne_zero _).2 U.2.2⟩
      left_inv := fun A => Subtype.ext (hA A.1 A.2.1)
      right_inv := fun U => Subtype.ext (plane_ofPlane _ U.1) }

/-- **The rank of `φ̄` is at most `N`.** -/
theorem finrank_range_phiBar_le (hU : Unram p n' W Qq O Kf ι σf j ϖ) {N N' : ℕ} (x : Matrix (Fin N') (Fin N) Qq)
    {L : Submodule W (Fin N → Qq)} {L' : Submodule W (Fin N' → Qq)} (hL : L.IsLattice Qq)
    (hx : MapsInto x L L') :
    Module.finrank (W ⧸ pId W p) (LinearMap.range (phiBar x hx hU.cast_ne_zero)) ≤ N := by
  have := isMaximal_pId hU
  let _ := Ideal.Quotient.field (pId W p)
  have hM := isLattice_pInv hU.cast_ne_zero hL
  have := finite_resSp hU hM
  have : FiniteDimensional (W ⧸ pId W p) (resSp p (pInv p L)) := Module.Finite.of_finite
  have hrk := LinearMap.finrank_range_add_finrank_ker (phiBar x hx hU.cast_ne_zero)
  rw [finrank_resSp hU hM] at hrk
  omega

/-- **The edge count** (`N′ = N + t + 1`): for `x·L ⊆ L′`, the type-`i` edges `L₁ ⊂ L′` containing `x·L` are
`Σ_l q^{(t+1−l)(i−l)}·[t+1, l]_q` times the type-`(i−l)` edges `A ⊃ L` with `x·A ⊆ L′` (both sides are Gaussian
binomials in the rank `ρ` of `x mod p`: `[N′−ρ, i]_q`, `[N−ρ, i−l]_q`; `qBinom_add` with `m = t + 1`). -/
theorem edge_count (hU : Unram p n' W Qq O Kf ι σf j ϖ) {N t : ℕ} (x : Matrix (Fin (N + t + 1)) (Fin N) Qq)
    (L : Submodule W (Fin N → Qq)) (L' : Submodule W (Fin (N + t + 1) → Qq)) (hL : L.IsLattice Qq)
    (hL' : L'.IsLattice Qq) (hx : MapsInto x L L') (i : ℕ) :
    ({L₁ | IsEdge (n' := n') p i L₁ L' ∧ MapsInto x L L₁}.ncard : ℤ) =
      ∑ l ∈ range (i + 1), ((p ^ n') ^ ((t + 1 - l) * (i - l)) * qBinom (p ^ n') (t + 1) l : ℕ) *
        ({A | IsEdge (n' := n') p (i - l) L A ∧ MapsInto x A L'}.ncard : ℤ) := by
  have hρ := finrank_range_phiBar_le hU x hL hx
  rw [ncard_edges_up hU x hL' hx i]
  simp only [ncard_edges_down hU x hL hx]
  rw [show N + t + 1 - Module.finrank (W ⧸ pId W p) (LinearMap.range (phiBar x hx hU.cast_ne_zero)) =
    (t + 1) + (N - Module.finrank (W ⧸ pId W p) (LinearMap.range (phiBar x hx hU.cast_ne_zero))) by omega,
    qBinom_add]
  push_cast
  rfl

end Edges

/-! ## Class representatives and Hecke adjointness -/

section Adjoint

open InertModel LocalRank

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] {n' : ℕ}

/-- **Class representatives** of a level on lattice tuples: every lattice tuple is `γ·L₀` for exactly one `L₀ ∈ R`,
with finite stabilisers. -/
structure ClassReps {k : ℕ} {V : Type} (C : Level V k Qq O) where
  /-- The representatives. -/
  R : Finset (V → Submodule W (Fin k → Qq))
  /-- They are lattice tuples. -/
  lat : ∀ L ∈ R, ∀ v, (L v).IsLattice Qq
  /-- Every lattice tuple is a translate of exactly one of them. -/
  ex : ∀ L : V → Submodule W (Fin k → Qq), (∀ v, (L v).IsLattice Qq) →
    ∃! L₀, L₀ ∈ R ∧ ∃ γ : C.Γ, L = C.smul γ L₀
  /-- Their stabilisers are finite. -/
  stab_fin : ∀ L ∈ R, 0 < Nat.card {γ : C.Γ // C.smul γ L = L}

/-- `|Stab L|`. -/
noncomputable def stab {k : ℕ} {V : Type} (C : Level V k Qq O) (L : V → Submodule W (Fin k → Qq)) : ℕ :=
  Nat.card {γ : C.Γ // C.smul γ L = L}

variable {k : ℕ} {V : Type} {C : Level V k Qq O}

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`γ⁻¹·(γ·L) = L`.** -/
theorem smul_inv_smul (γ : C.Γ) (L : V → Submodule W (Fin k → Qq)) : C.smul γ⁻¹ (C.smul γ L) = L := by
  rw [← Level.smul_mul, inv_mul_cancel, Level.smul_one]

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`γ·(γ⁻¹·L) = L`.** -/
theorem smul_smul_inv (γ : C.Γ) (L : V → Submodule W (Fin k → Qq)) : C.smul γ (C.smul γ⁻¹ L) = L := by
  rw [← Level.smul_mul, mul_inv_cancel, Level.smul_one]

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Translates of lattice tuples are lattice tuples.** -/
theorem isLattice_smul (γ : C.Γ) {L : V → Submodule W (Fin k → Qq)} (hL : ∀ v, (L v).IsLattice Qq) (v : V) :
    ((C.smul γ L) v).IsLattice Qq :=
  isLattice_map _ (hL v)

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **A tuple with a translate in `R` is a lattice tuple.** -/
theorem ClassReps.isLattice_of_mem (RR : ClassReps (W := W) C) {γ : C.Γ} {B : V → Submodule W (Fin k → Qq)}
    (h : C.smul γ B ∈ RR.R) (v : V) : (B v).IsLattice Qq := by
  have := isLattice_smul γ⁻¹ (RR.lat _ h) v
  rwa [smul_inv_smul] at this

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **The translate in `R` is unique.** -/
theorem ClassReps.eq_of_mem (RR : ClassReps (W := W) C) {γ γ' : C.Γ} {B : V → Submodule W (Fin k → Qq)}
    (h : C.smul γ B ∈ RR.R) (h' : C.smul γ' B ∈ RR.R) : C.smul γ B = C.smul γ' B :=
  (RR.ex B (RR.isLattice_of_mem h)).unique ⟨h, γ⁻¹, (smul_inv_smul γ B).symm⟩
    ⟨h', γ'⁻¹, (smul_inv_smul γ' B).symm⟩

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **The elements moving `B` into `R` are a coset of a stabiliser**: as many as `|Stab(γ₀B)|`. -/
theorem ClassReps.card_toR (RR : ClassReps (W := W) C) {γ₀ : C.Γ} {B : V → Submodule W (Fin k → Qq)}
    (h₀ : C.smul γ₀ B ∈ RR.R) : Nat.card {γ : C.Γ // C.smul γ B ∈ RR.R} = stab C (C.smul γ₀ B) := by
  refine Nat.card_congr
    { toFun := fun γ => ⟨γ.1 * γ₀⁻¹, by
        rw [Level.smul_mul, smul_inv_smul]
        exact RR.eq_of_mem γ.2 h₀⟩
      invFun := fun δ => ⟨δ.1 * γ₀, by rw [Level.smul_mul, δ.2]; exact h₀⟩
      left_inv := fun γ => Subtype.ext (by simp)
      right_inv := fun δ => Subtype.ext (by simp) }

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Finitely many elements move a tuple into `R`.** -/
theorem ClassReps.finite_toR (RR : ClassReps (W := W) C) (B : V → Submodule W (Fin k → Qq)) :
    {γ : C.Γ | C.smul γ B ∈ RR.R}.Finite := by
  by_cases h : ∃ γ₀, C.smul γ₀ B ∈ RR.R
  · obtain ⟨γ₀, h₀⟩ := h
    have h1 := RR.card_toR h₀
    have h2 := RR.stab_fin _ h₀
    rw [← stab, ← h1] at h2
    exact Set.finite_coe_iff.1 (Nat.finite_of_card_ne_zero h2.ne')
  · simp only [not_exists] at h
    exact Set.finite_empty.subset fun γ hγ => h γ hγ

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **The masses of the elements moving a lattice tuple into `R` add up to `1`**: they all move it to the same
`L₀`, and there are `|Stab L₀|` of them. -/
theorem ClassReps.sum_inv_stab (RR : ClassReps (W := W) C) {B : V → Submodule W (Fin k → Qq)}
    (hB : ∀ v, (B v).IsLattice Qq) :
    ∑ γ ∈ (RR.finite_toR B).toFinset, ((stab C (C.smul γ B) : ℚ))⁻¹ = 1 := by
  obtain ⟨L₀, ⟨hL₀, γ₁, rfl⟩, -⟩ := RR.ex B hB
  have h₀ : C.smul γ₁⁻¹ (C.smul γ₁ L₀) ∈ RR.R := by rw [smul_inv_smul]; exact hL₀
  have hc : ∀ γ ∈ (RR.finite_toR (C.smul γ₁ L₀)).toFinset,
      C.smul γ (C.smul γ₁ L₀) = C.smul γ₁⁻¹ (C.smul γ₁ L₀) := fun γ hγ =>
    RR.eq_of_mem ((RR.finite_toR _).mem_toFinset.1 hγ) h₀
  rw [Finset.sum_congr rfl fun γ hγ => by rw [hc γ hγ], Finset.sum_const, nsmul_eq_mul,
    ← Set.ncard_eq_toFinset_card _ (RR.finite_toR _), ← Nat.card_coe_set_eq]
  have h1 := RR.card_toR h₀
  have h2 := RR.stab_fin _ h₀
  change Nat.card {γ : C.Γ // C.smul γ (C.smul γ₁ L₀) ∈ RR.R} = _ at h1
  rw [show Nat.card ↥{γ : C.Γ | C.smul γ (C.smul γ₁ L₀) ∈ RR.R} =
    Nat.card {γ : C.Γ // C.smul γ (C.smul γ₁ L₀) ∈ RR.R} from rfl, h1]
  exact mul_inv_cancel₀ (by exact_mod_cast h2.ne')

variable {ι : Qq →+* Kf} {σf : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p : ℕ}

/-- **Finitely many edges out of a lattice** (planes of `p⁻¹L₀/L₀`, `LocalRank.outEdgeEquivPlane`). -/
theorem finite_edges_up (hU : Unram p n' W Qq O Kf ι σf j ϖ) (r : ℕ) (L₀ : Submodule W (Fin k → Qq)) :
    {L₁ | IsEdge (n' := n') p r L₀ L₁}.Finite := by
  by_cases hL : L₀.IsLattice Qq
  · have := isMaximal_pId hU
    let _ := Ideal.Quotient.field (pId W p)
    have := finite_resSp hU (isLattice_pInv hU.cast_ne_zero hL)
    have : Finite (Submodule (W ⧸ pId W p) (resSp p (pInv p L₀))) :=
      Finite.of_injective (fun U => (U : Set (resSp p (pInv p L₀)))) SetLike.coe_injective
    exact Set.finite_coe_iff.1 (Finite.of_equiv _ (outEdgeEquivPlane hU hL r).symm)
  · exact Set.finite_empty.subset fun L₁ h => hL h.2.1

variable [DecidableEq V]

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Moving an edge pair back**: `γ·(L with L_v ↦ L₁)` with its `v`-entry reset to `(γ·L)_v` is `γ·L`. -/
theorem update_smul_update (γ : C.Γ) (L : V → Submodule W (Fin k → Qq)) (v : V) (L₁ : Submodule W (Fin k → Qq)) :
    Function.update (C.smul γ (Function.update L v L₁)) v (C.smul γ L v) = C.smul γ L := by
  rw [← update_smul, Function.update_idem, Function.update_eq_self]

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **The `v`-entry of a moved updated tuple.** -/
theorem smul_update_self (γ : C.Γ) (L : V → Submodule W (Fin k → Qq)) (v : V) (L₁ : Submodule W (Fin k → Qq)) :
    C.smul γ (Function.update L v L₁) v =
      L₁.map ((Matrix.mulVecLin ((C.act v γ : GL (Fin k) Qq) : Matrix (Fin k) (Fin k) Qq)).restrictScalars W) := by
  rw [← update_smul, Function.update_self]

/-- **Hecke adjointness** (the mass double count over the `Γ`-orbits of edges): for a `Γ`-invariant `φ`, the
mass-weighted sum over edges up from the representatives equals the sum over edges down. Each side is
`Σ_{L ∈ R} Σ_{L′} Σ_{γ : γL′ ∈ R} φ/(|Stab L|·|Stab γL′|)` (`ClassReps.sum_inv_stab`), and
`(L, L₁, γ) ↦ (γ·L[v ↦ L₁], (γL)_v, γ⁻¹)` exchanges them. -/
theorem hecke_adjoint (hU : Unram p n' W Qq O Kf ι σf j ϖ) [Fintype V] (RR : ClassReps (W := W) C) (v : V)
    (i : ℕ) {M : Type} [AddCommGroup M] [Module ℚ M]
    (φ : (V → Submodule W (Fin k → Qq)) → (V → Submodule W (Fin k → Qq)) → M)
    (hφ : ∀ γ L L₁, φ (C.smul γ L) (C.smul γ L₁) = φ L L₁) :
    ∑ L ∈ RR.R, ((stab C L : ℚ)⁻¹) • ∑ᶠ (L₁ : Submodule W (Fin k → Qq)) (_ : IsEdge (n' := n') p i (L v) L₁),
        φ L (Function.update L v L₁) =
      ∑ L ∈ RR.R, ((stab C L : ℚ)⁻¹) • ∑ᶠ (L₀ : Submodule W (Fin k → Qq)) (_ : IsEdge (n' := n') p i L₀ (L v)),
        φ (Function.update L v L₀) L := by
  classical
  set up : (V → Submodule W (Fin k → Qq)) → Finset (Submodule W (Fin k → Qq)) :=
    fun L => (finite_edges_up hU i (L v)).toFinset
  set dn : (V → Submodule W (Fin k → Qq)) → Finset (Submodule W (Fin k → Qq)) :=
    fun L => (finite_edges hU i (L v)).toFinset
  set G : (V → Submodule W (Fin k → Qq)) → Finset C.Γ := fun B => (RR.finite_toR B).toFinset
  have hlat : ∀ L ∈ RR.R, ∀ L₁ : Submodule W (Fin k → Qq), L₁.IsLattice Qq →
      ∀ w, (Function.update L v L₁ w).IsLattice Qq := fun L hL L₁ h₁ w => by
    by_cases hw : w = v
    · subst hw
      rw [Function.update_self]
      exact h₁
    · rw [Function.update_of_ne hw]
      exact RR.lat L hL w
  -- spread the mass `|Stab L|⁻¹` over the elements moving the other tuple into `R`
  have hspread : ∀ L B : V → Submodule W (Fin k → Qq), (∀ w, (B w).IsLattice Qq) → ∀ m : M,
      ((stab C L : ℚ)⁻¹) • m = ∑ γ ∈ G B, ((stab C L : ℚ)⁻¹ * (stab C (C.smul γ B) : ℚ)⁻¹) • m :=
    fun L B hB m => by
      have h1 : ∑ γ ∈ G B, ((stab C (C.smul γ B) : ℚ))⁻¹ = 1 := RR.sum_inv_stab hB
      calc ((stab C L : ℚ)⁻¹) • m = ((stab C L : ℚ)⁻¹) • ((∑ γ ∈ G B, ((stab C (C.smul γ B) : ℚ))⁻¹) • m) := by
            rw [h1, one_smul]
        _ = _ := by
            rw [Finset.sum_smul, Finset.smul_sum]
            simp only [mul_smul]
  have hL : ∑ L ∈ RR.R, ((stab C L : ℚ)⁻¹) • ∑ᶠ (L₁ : Submodule W (Fin k → Qq))
      (_ : IsEdge (n' := n') p i (L v) L₁), φ L (Function.update L v L₁) =
      ∑ x ∈ (RR.R.sigma up).sigma fun x => G (Function.update x.1 v x.2),
        ((stab C x.1.1 : ℚ)⁻¹ * (stab C (C.smul x.2 (Function.update x.1.1 v x.1.2)) : ℚ)⁻¹) •
          φ x.1.1 (Function.update x.1.1 v x.1.2) := by
    rw [Finset.sum_sigma, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun L hL => ?_
    have hfs : ∑ᶠ (L₁ : Submodule W (Fin k → Qq)) (_ : IsEdge (n' := n') p i (L v) L₁),
        φ L (Function.update L v L₁) = ∑ L₁ ∈ up L, φ L (Function.update L v L₁) :=
      finsum_mem_eq_finite_toFinset_sum _ _
    rw [hfs, Finset.smul_sum]
    refine Finset.sum_congr rfl fun L₁ h₁ => hspread L _ (hlat L hL L₁ ?_) _
    exact ((finite_edges_up hU i (L v)).mem_toFinset.1 h₁).1
  have hR : ∑ L ∈ RR.R, ((stab C L : ℚ)⁻¹) • ∑ᶠ (L₀ : Submodule W (Fin k → Qq))
      (_ : IsEdge (n' := n') p i L₀ (L v)), φ (Function.update L v L₀) L =
      ∑ x ∈ (RR.R.sigma dn).sigma fun x => G (Function.update x.1 v x.2),
        ((stab C x.1.1 : ℚ)⁻¹ * (stab C (C.smul x.2 (Function.update x.1.1 v x.1.2)) : ℚ)⁻¹) •
          φ (Function.update x.1.1 v x.1.2) x.1.1 := by
    rw [Finset.sum_sigma, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun L hL => ?_
    have hfs : ∑ᶠ (L₀ : Submodule W (Fin k → Qq)) (_ : IsEdge (n' := n') p i L₀ (L v)),
        φ (Function.update L v L₀) L = ∑ L₀ ∈ dn L, φ (Function.update L v L₀) L :=
      finsum_mem_eq_finite_toFinset_sum _ _
    rw [hfs, Finset.smul_sum]
    refine Finset.sum_congr rfl fun L₀ h₀ => hspread L _ (hlat L hL L₀ ?_) _
    exact ((finite_edges hU i (L v)).mem_toFinset.1 h₀).2.1
  rw [hL, hR]
  -- the exchange `(L, L₁, γ) ↦ (γ·L[v ↦ L₁], (γL)_v, γ⁻¹)`
  set e : (Σ _ : (Σ _ : V → Submodule W (Fin k → Qq), Submodule W (Fin k → Qq)), C.Γ) →
      (Σ _ : (Σ _ : V → Submodule W (Fin k → Qq), Submodule W (Fin k → Qq)), C.Γ) :=
    fun x => ⟨⟨C.smul x.2 (Function.update x.1.1 v x.1.2), C.smul x.2 x.1.1 v⟩, x.2⁻¹⟩
  have hee : ∀ x, e (e x) = x := fun x => by
    obtain ⟨⟨L, L₁⟩, γ⟩ := x
    simp only [e, update_smul_update, smul_inv_smul, inv_inv, Function.update_self]
  have hmem : ∀ (s t : (V → Submodule W (Fin k → Qq)) → Finset (Submodule W (Fin k → Qq)))
      (hst : ∀ L ∈ RR.R, ∀ L₁ ∈ s L, ∀ γ : C.Γ, C.smul γ L v ∈ t (C.smul γ (Function.update L v L₁))),
      ∀ x ∈ (RR.R.sigma s).sigma (fun x => G (Function.update x.1 v x.2)),
        e x ∈ (RR.R.sigma t).sigma (fun x => G (Function.update x.1 v x.2)) := by
    rintro s t hst ⟨⟨L, L₁⟩, γ⟩ hx
    simp only [Finset.mem_sigma, G, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hx
    simp only [e, Finset.mem_sigma, G, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, update_smul_update,
      smul_inv_smul]
    exact ⟨⟨hx.2, hst L hx.1.1 L₁ hx.1.2 γ⟩, hx.1.1⟩
  refine Finset.sum_nbij' e e (hmem up dn fun L _ L₁ h₁ γ => ?_) (hmem dn up fun L _ L₀ h₀ γ => ?_)
    (fun x _ => hee x) (fun x _ => hee x) fun x _ => ?_
  · simp only [up, dn, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at h₁ ⊢
    rw [smul_update_self]
    exact isEdge_map _ h₁
  · simp only [up, dn, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at h₀ ⊢
    rw [smul_update_self]
    exact isEdge_map _ h₀
  · obtain ⟨⟨L, L₁⟩, γ⟩ := x
    simp only [e, update_smul_update, smul_inv_smul, hφ]
    rw [mul_comm]

end Adjoint

end KernelCount
