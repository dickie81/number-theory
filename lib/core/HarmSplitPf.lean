import TwoLetter

/-!
# The harmonic splitting with denominators (L5, A-N7)

A proof of the hypothesis `FirstAssembly.HarmSplit` of the first local theorem: at a setting `Unram`, for `k ≥ 3`,
every set of tops `TT` and every `a`, with Annex I's exponent `u = N·⌈(k + 1)λ_a⌉` and `a_max = 8a` (`harmSplit`); hence
the first local theorem from the inputs `FlatDim`, `InputRank`, `SegMean`, `κ_P ≤ C_P·N·N₁/Y` and `CloudStep` alone
(`first_local''`).

**The maps.** With the two-letter models of `TwoLetter` (`ψ` for `H(A, B)`, `β` for the flat weights) and the
harmonic projectors `π_j` of `HarmDecomp` at the positions of the tops (`piL`, steps `J_s = min(A_s, B_s)`):
* `pr_j = β∘π_j∘ψ⁻¹`, `ψ⁻¹` a linear left inverse of `ψ` on the letter degree of `H(A, B)` (`exists_leftInv`);
* `io_j = ψ∘(∏_s h_s^{j_s}·)∘π₀∘s_j`, `s_j` a linear section of `β` on the letter degree of `fl(A − j, B − j)`
  (`exists_section`), `π₀` the harmonic projection at the steps `J − j`.

**The identity** `Σ_j io_j∘pr_j = id` on `∇(H(A, B))`: `ψ` is onto (`exists_psi`); `π₀∘s_j∘β = π₀` on the flat letter
degree, since a difference killed by `β` has a harmonic projection killed by `β`, hence zero (`pz_eq`, from
`TwoLetter.eq_zero_of_beta`); `π₀` fixes the harmonic `π_jP`; and `Σ_j (∏ h_s^{j_s})·π_jP = P`
(`HarmDecomp.Pairs.sum_piL`), the index sets matched by `sum_jBox`.

**Integrality.** For block lattices `Λ_s` with bases `C_s`, the twists of both models are `tcst·(model)∘Alet`
(`twist_psi`, `twist_beta`), the projectors commute with `Alet` up to `∏_s det(C_s)^{j_s}` (`piL_linS`,
`linS_hProd`), and the twist constants of the pieces absorb exactly that factor (`tcst_sub`). So integrality at `Λ`
is integrality of `π_j` on integral letter polynomials, which loses `p^{Σ_s (k + 1)⌊log_p(k + A_s + B_s)⌋}`
(`HarmDecomp.piL_mem_intP`), at most `p^u` (`budget`, from `A_s + B_s + 1 ≤ 8a`).

**Readings of the planning statements.** Annex I's `u = N·⌈(m + 2)λ_a⌉` is the repo's `uH = N·⌈(k + 1)λ_a⌉`
(`m = k − 1`); the proof needs `k ≥ 3` (the test matrices of `TwoLetter`), which `FirstHyp` supplies (`k ≥ 2N₁ + 3`).
The two-letter identification I4 is `TwoLetter`; the harmonic decomposition with denominators is `HarmDecomp`.
-/

namespace HarmSplitPf

open MvPolynomial WeylFock InertModel LocalLattice LetterFock HarmDecomp TwoLetter FirstMeans FirstAssembly Finset

open scoped Matrix

noncomputable section

section LinAlg

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- **A linear left inverse on a subspace** of a map injective there. -/
theorem exists_leftInv (f : V →ₗ[K] W) (S : Submodule K V) (h : Set.InjOn f S) :
    ∃ g : W →ₗ[K] V, ∀ x ∈ S, g (f x) = x := by
  have hinj : LinearMap.ker (f ∘ₗ S.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    exact Subtype.ext (h x.2 y.2 hxy)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  refine ⟨S.subtype ∘ₗ g, fun x hx => ?_⟩
  have := congrArg (fun φ => φ ⟨x, hx⟩) hg
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at this
  simp [this]

/-- **A linear section of a map** over its image of a subspace: `g(f x) ∈ S` and `f(g(f x)) = f x` on `S`. -/
theorem exists_section (f : V →ₗ[K] W) (S : Submodule K V) :
    ∃ g : W →ₗ[K] V, ∀ x ∈ S, g (f x) ∈ S ∧ f (g (f x)) = f x := by
  set fS := f ∘ₗ S.subtype
  obtain ⟨g₁, hg₁⟩ := LinearMap.exists_rightInverse_of_surjective fS.rangeRestrict
    (LinearMap.range_rangeRestrict fS)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range fS)
  refine ⟨S.subtype ∘ₗ g₁ ∘ₗ Submodule.projectionOnto _ C hC, fun x hx => ⟨?_, ?_⟩⟩
  · simp
  · have hmem : f x ∈ LinearMap.range fS := ⟨⟨x, hx⟩, rfl⟩
    have h1 : Submodule.projectionOnto _ C hC (f x) = ⟨f x, hmem⟩ :=
      Submodule.projectionOnto_apply_left hC ⟨f x, hmem⟩
    have h2 := congrArg (fun φ => (φ ⟨f x, hmem⟩ : W)) hg₁
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.codRestrict_apply] at h2
    simp only [LinearMap.comp_apply, h1, Submodule.subtype_apply]
    exact h2

end LinAlg

/-! ## The data of a pair of top degrees -/

section Data

variable {n' : ℕ} {TT : Finset (Fin n')}

/-- **A point on the tops as natural degrees** at every position (`0` off the tops). -/
def nat (TT : Finset (Fin n')) (A : TT → ℤ) : Fin n' → ℕ := fun s => (ext TT A s).toNat

/-- **The chain lengths** `J_s = min(A_s, B_s)`. -/
def Jm (A B : TT → ℤ) : Fin n' → ℕ := fun s => min (nat TT A s) (nat TT B s)

/-- **The bottom of the chains**: the letter degrees minus `J`. -/
def D0b (A B : TT → ℤ) : Fin (n' * 2) → ℕ := fun t => dL (nat TT A) (nat TT B) t - Jm A B (pos t)

/-- **The chain constants** `u_s = k + |A_s − B_s|`. -/
def uS (k : ℕ) (A B : TT → ℤ) : Fin n' → ℕ := fun s => k + D0b A B (vL s) + D0b A B (cL s)

/-- **`nat` at a top.** -/
theorem nat_of_mem {A : TT → ℤ} (hA : ∀ s, 0 ≤ A s) (s : TT) : (nat TT A s : ℤ) = A s := by
  simp [nat, Int.toNat_of_nonneg (hA s)]

/-- **`nat` off the tops.** -/
theorem nat_of_not_mem (A : TT → ℤ) {s : Fin n'} (hs : s ∉ TT) : nat TT A s = 0 := by
  simp [nat, ext_of_not_mem A hs]

/-- **The letter degrees are on the chains**: `dL = cdeg D₀ J`. -/
theorem dL_eq_cdeg (A B : TT → ℤ) : dL (nat TT A) (nat TT B) = cdeg vL cL (D0b A B) (Jm A B) := by
  funext t
  have hJ : ∀ s, Jm A B s ≤ degV (nat TT A) (nat TT B) s ∧ Jm A B s ≤ degC (nat TT A) (nat TT B) s :=
    fun s => by simp only [Jm, degV, degC]; split_ifs <;> omega
  rcases letter_cases t with h | h <;> rw [h]
  · rw [(pairs.cdeg_apply _ _ _).1, D0b, pos_vL, dL_vL]; have := (hJ (pos t)).1; omega
  · rw [(pairs.cdeg_apply _ _ _).2, D0b, pos_cL, dL_cL]; have := (hJ (pos t)).2; omega

/-- **The bottoms are bottoms**: one letter of each position has degree `0`. -/
theorem D0_zero (A B : TT → ℤ) (s : Fin n') : D0b A B (vL s) = 0 ∨ D0b A B (cL s) = 0 := by
  simp only [D0b, dL_vL, dL_cL, pos_vL, pos_cL, degV, degC, Jm]
  split_ifs <;> omega

/-- **The positions of the tops**, as a list. -/
def lT (TT : Finset (Fin n')) : List (Fin n') := TT.toList

/-- **The list of the tops has no repetitions.** -/
theorem lT_nodup : (lT TT).Nodup := Finset.nodup_toList TT

/-- **Membership in the list of the tops.** -/
@[simp] theorem mem_lT {s : Fin n'} : s ∈ lT TT ↔ s ∈ TT := Finset.mem_toList

/-- **The index of `j`** at every position. -/
theorem jBox_spec {A B j : TT → ℤ} (hj : j ∈ jBox A B) (s : TT) : 0 ≤ j s ∧ j s ≤ A s ∧ j s ≤ B s := by
  have := Fintype.mem_piFinset.1 hj s
  rw [Finset.mem_Icc, le_min_iff] at this
  exact ⟨this.1, this.2.1, this.2.2⟩

/-- **The degrees after removing `j`**: `nat(A − j) = nat A − nat j`. -/
theorem nat_sub {A j : TT → ℤ} (hj : ∀ s, 0 ≤ j s ∧ j s ≤ A s) (s : Fin n') :
    nat TT (A - j) s = nat TT A s - nat TT j s := by
  by_cases hs : s ∈ TT
  · have h := hj ⟨s, hs⟩
    simp only [nat, ext_of_mem _ hs, Pi.sub_apply]
    omega
  · simp [nat_of_not_mem _ hs]

/-- **`j ≤ J`.** -/
theorem nat_le_Jm {A B j : TT → ℤ} (hj : j ∈ jBox A B) (s : Fin n') : nat TT j s ≤ Jm A B s := by
  by_cases hs : s ∈ TT
  · have h := jBox_spec hj ⟨s, hs⟩
    simp only [Jm, nat, ext_of_mem _ hs]
    omega
  · simp [nat_of_not_mem _ hs]

/-- **The bottoms after removing `j`** are the same. -/
theorem D0_sub {A B j : TT → ℤ} (hj : j ∈ jBox A B) : D0b (A - j) (B - j) = D0b A B := by
  have hA := nat_sub (A := A) fun s => ⟨(jBox_spec hj s).1, (jBox_spec hj s).2.1⟩
  have hB := nat_sub (A := B) fun s => ⟨(jBox_spec hj s).1, (jBox_spec hj s).2.2⟩
  funext t
  have hle := nat_le_Jm hj (pos t)
  simp only [D0b, dL, degV, degC, Jm, hA, hB] at hle ⊢
  split_ifs <;> omega

/-- **The degrees of the flat piece `j`** are on the chains at steps `J − j`. -/
theorem dL_sub {A B j : TT → ℤ} (hj : j ∈ jBox A B) :
    dL (nat TT (A - j)) (nat TT (B - j)) = cdeg vL cL (D0b A B) fun s => Jm A B s - nat TT j s := by
  rw [dL_eq_cdeg, D0_sub hj]
  congr 1
  funext s
  have hA := nat_sub (A := A) (fun s => ⟨(jBox_spec hj s).1, (jBox_spec hj s).2.1⟩) s
  have hB := nat_sub (A := B) (fun s => ⟨(jBox_spec hj s).1, (jBox_spec hj s).2.2⟩) s
  simp only [Jm, hA, hB]
  have := nat_le_Jm hj s
  simp only [Jm] at this
  omega

/-- **Off the tops the chains are empty.** -/
theorem Jm_of_not_mem (A B : TT → ℤ) {s : Fin n'} (hs : s ∉ TT) : Jm A B s = 0 := by
  simp [Jm, nat_of_not_mem _ hs]

/-- **Reindexing the harmonic indices** `J(A, B)` (on the tops, in `ℤ`) as the box of the list of the tops. -/
theorem sum_jBox {M : Type*} [AddCommMonoid M] {A B : TT → ℤ} (hA : ∀ s, 0 ≤ A s) (hB : ∀ s, 0 ≤ B s)
    (G : (Fin n' → ℕ) → M) : ∑ j ∈ jBox A B, G (nat TT j) = ∑ j ∈ jBoxL (Jm A B) (lT TT), G j := by
  refine Finset.sum_nbij' (fun j => nat TT j) (fun j s => (j s : ℤ)) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro j hj
    simp only [jBoxL, Fintype.mem_piFinset]
    intro s
    by_cases hs : s ∈ TT
    · simp only [mem_lT, hs, ite_true, Finset.mem_range]
      exact Nat.lt_succ_of_le (nat_le_Jm hj s)
    · simp [mem_lT, hs, nat_of_not_mem _ hs]
  · intro j hj
    simp only [jBoxL, Fintype.mem_piFinset] at hj
    simp only [jBox, Fintype.mem_piFinset, Finset.mem_Icc, le_min_iff]
    intro s
    have h := hj s
    simp only [mem_lT, s.2, ite_true, Finset.mem_range] at h
    have hA' := nat_of_mem hA s
    have hB' := nat_of_mem hB s
    simp only [Jm] at h
    omega
  · intro j hj
    funext s
    simp only [nat, ext_coe]
    exact Int.toNat_of_nonneg (jBox_spec hj s).1
  · intro j hj
    funext s
    simp only [jBoxL, Fintype.mem_piFinset] at hj
    by_cases hs : s ∈ TT
    · simp [nat, ext_of_mem _ hs]
    · have h := hj s
      simp only [mem_lT, hs, ite_false, Finset.mem_singleton] at h
      simp [nat_of_not_mem _ hs, h]

end Data

/-! ## Degrees, constants and the budget -/

section Aux

variable {n' : ℕ} {TT : Finset (Fin n')}

/-- **The chain constant and the chain length** add up to the degrees: `u_s + 2J_s = k + A_s + B_s`. -/
theorem uS_add (k : ℕ) (A B : TT → ℤ) (s : Fin n') : uS k A B s + 2 * Jm A B s = k + nat TT A s + nat TT B s := by
  simp only [uS, D0b, dL_vL, dL_cL, pos_vL, pos_cL, degV, degC, Jm]
  split_ifs <;> omega

/-- **Adding a multiple of one pairing degree** to a chain degree. -/
theorem cdeg_add_single (D₀ : Fin (n' * 2) → ℕ) (c : Fin n' → ℕ) (s : Fin n') (i : ℕ) :
    cdeg vL cL D₀ c + i • pe (vL s) (cL s) = cdeg vL cL D₀ (c + Pi.single s i) := by
  simp only [cdeg, Pi.add_apply, add_smul, Finset.sum_add_distrib, add_assoc]
  congr 2
  rw [Finset.sum_eq_single s (fun t _ hts => by simp [hts]) (by simp)]
  simp

/-- **The degree of a product of pairings**: `∏_{s ∈ l} h_s^{j_s}·X` raises the chain step by `j` on `l`. -/
theorem hProd_mul_mem {k : ℕ} {Kf : Type} [Field Kf] (D₀ : Fin (n' * 2) → ℕ) (j : Fin n' → ℕ) :
    ∀ (l : List (Fin n')), l.Nodup → ∀ (c : Fin n' → ℕ) (X : LPol (Fin (n' * 2)) k Kf),
      X ∈ LHom Kf (cdeg vL cL D₀ c) →
        hProd k Kf vL cL j l * X ∈ LHom Kf (cdeg vL cL D₀ fun t => c t + if t ∈ l then j t else 0) := by
  intro l
  induction l with
  | nil => intro _ c X hX; simpa [hProd] using hX
  | cons s l ih =>
    intro hl c X hX
    have hsl := (List.nodup_cons.1 hl).1
    have h := hP_pow_mul_mem (vL s) (cL s) (j s) (ih (List.nodup_cons.1 hl).2 c X hX)
    rw [cdeg_add_single] at h
    simp only [hProd, List.map_cons, List.prod_cons] at h ⊢
    have hc : (fun t => c t + if t ∈ s :: l then j t else 0) =
        (fun t => c t + if t ∈ l then j t else 0) + Pi.single s (j s) := by
      funext t
      by_cases hts : t = s
      · subst hts; simp [hsl]
      · simp [hts]
    rw [mul_assoc, hc]
    exact h

/-- **Products of pairings are integral.** -/
theorem hProd_mem_intP {k : ℕ} {Kf : Type} [Field Kf] [CharZero Kf] {Ar : Subring Kf} (j : Fin n' → ℕ)
    (l : List (Fin n')) : hProd k Kf vL cL j l ∈ intP Ar (Fin (n' * 2) × Fin k) := by
  induction l with
  | nil => exact one_mem _
  | cons s l ih =>
    simp only [hProd, List.map_cons, List.prod_cons] at ih ⊢
    refine mul_mem (pow_mem ?_ _) ih
    exact Subring.sum_mem _ fun c _ => mul_mem (X_mem_intP _) (X_mem_intP _)

/-- **The letter change on a product of pairings**: `(∏ h_s^{j_s})∘Alet = (∏ det(C_s)^{j_s})·∏ h_s^{j_s}`. -/
theorem linS_hProd {k : ℕ} {Kf : Type} [Field Kf] (C₀ : Fin n' → Matrix (Fin k) (Fin k) Kf) (j : Fin n' → ℕ)
    (l : List (Fin n')) :
    linS k (Alet C₀) (hProd k Kf vL cL j l) = (l.map fun s => (C₀ s).det ^ j s).prod • hProd k Kf vL cL j l := by
  induction l with
  | nil => simp [hProd]
  | cons s l ih =>
    simp only [hProd, List.map_cons, List.prod_cons, map_mul, map_pow] at ih ⊢
    rw [ih, linS_hP _ (letCond_Alet C₀ s).1, smul_pow, smul_mul_smul_comm]

/-- **The twist constants of the pieces**: `tcst(dL(A − j, B − j)) = tcst(dL(A, B))·∏_s det(C_s)^{j_s}`. -/
theorem tcst_sub {k : ℕ} {Kf : Type} [Field Kf] (C₀ : Fin n' → Matrix (Fin k) (Fin k) Kf)
    (hC : ∀ s, (C₀ s).det ≠ 0) {A B j : TT → ℤ} (hj : j ∈ jBox A B) :
    tcst C₀ (dL (nat TT (A - j)) (nat TT (B - j))) =
      tcst C₀ (dL (nat TT A) (nat TT B)) * ((lT TT).map fun s => (C₀ s).det ^ nat TT j s).prod := by
  have hA := nat_sub (A := A) fun s => ⟨(jBox_spec hj s).1, (jBox_spec hj s).2.1⟩
  have hB := nat_sub (A := B) fun s => ⟨(jBox_spec hj s).1, (jBox_spec hj s).2.2⟩
  rw [lT, Finset.prod_map_toList, Finset.prod_subset (Finset.subset_univ TT) (fun s _ hs => by
    simp [nat_of_not_mem _ hs]), tcst, tcst, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  have hle := nat_le_Jm hj s
  have hle' : nat TT j s ≤ degC (nat TT A) (nat TT B) s := by
    simp only [Jm, degC] at hle ⊢; split_ifs <;> omega
  rw [dL_cL, dL_cL, ← zpow_natCast, ← zpow_add₀ (hC s)]
  congr 1
  simp only [degC, hA, hB] at hle' ⊢
  split_ifs at hle' ⊢ <;> rw [Nat.cast_sub hle'] <;> ring

/-- **The budget** (Annex I's `u = N·⌈(k + 1)λ_a⌉`): the losses `(k + 1)·⌊log_p(k + A_s + B_s)⌋` of the tops add up to
at most `u` when `A_s + B_s + 1 ≤ 8a`. -/
theorem budget {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) {a : ℝ} {A B : TT → ℤ} (hA : ∀ s, 0 ≤ A s)
    (hB : ∀ s, 0 ≤ B s) (hAB : ∀ s, ((A s + B s + 1 : ℤ) : ℝ) ≤ 8 * a) :
    ((lT TT).map fun s => (k + 1) * Nat.log p (k + nat TT A s + nat TT B s)).sum ≤
      uH TT.card k (lamA p k a) := by
  rw [lT, Finset.sum_map_toList, uH, ← smul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun s hs => ?_
  have hA' := nat_of_mem hA ⟨s, hs⟩
  have hB' := nat_of_mem hB ⟨s, hs⟩
  have h8 := hAB ⟨s, hs⟩
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hn : ((k + nat TT A s + nat TT B s : ℕ) : ℝ) ≤ 8 * a + k := by
    have hA'' : ((nat TT A s : ℕ) : ℝ) = (A ⟨s, hs⟩ : ℝ) := by exact_mod_cast hA'
    have hB'' : ((nat TT B s : ℕ) : ℝ) = (B ⟨s, hs⟩ : ℝ) := by exact_mod_cast hB'
    push_cast at h8 ⊢
    linarith
  have hpos : (0 : ℝ) < ((k + nat TT A s + nat TT B s : ℕ) : ℝ) := by
    have : 1 ≤ k + nat TT A s + nat TT B s := by omega
    exact_mod_cast this
  have hlog : (Nat.log p (k + nat TT A s + nat TT B s) : ℝ) ≤ Real.logb p (8 * a + k) :=
    (Real.natLog_le_logb _ _).trans (Real.logb_le_logb_of_le hp1 hpos hn)
  have : (((k + 1) * Nat.log p (k + nat TT A s + nat TT B s) : ℕ) : ℝ) ≤ ((k : ℝ) + 1) * lamA p k a := by
    rw [lamA]
    push_cast
    nlinarith
  exact_mod_cast this.trans (Nat.le_ceil _)

end Aux

/-! ## The harmonic splitting -/

section Split

variable {n' k : ℕ} [NeZero k] {Kf : Type} [Field Kf] [CharZero Kf] {TT : Finset (Fin n')}

/-- **The flat model determines the harmonic projection** of a piece: on the letter degree of `fl(A − j, B − j)`,
`β P₁ = β P₂` forces `π₀P₁ = π₀P₂` (`π₀P₁ − π₀P₂` is harmonic at every position and killed by `β`). -/
theorem pz_eq (hk : 3 ≤ k) {A B j : TT → ℤ} (hj : j ∈ jBox A B) {P₁ P₂ : LPol (Fin (n' * 2)) k Kf}
    (h₁ : P₁ ∈ LHom Kf (dL (nat TT (A - j)) (nat TT (B - j))))
    (h₂ : P₂ ∈ LHom Kf (dL (nat TT (A - j)) (nat TT (B - j)))) (hβ : beta Kf P₁ = beta Kf P₂) :
    piL k Kf vL cL (uS k A B) (fun s => Jm A B s - nat TT j s) 0 (lT TT) P₁ =
      piL k Kf vL cL (uS k A B) (fun s => Jm A B s - nat TT j s) 0 (lT TT) P₂ := by
  set J' : Fin n' → ℕ := fun s => Jm A B s - nat TT j s
  have hΔ : P₁ - P₂ ∈ LHom Kf (cdeg vL cL (D0b A B) J') := by rw [← dL_sub hj]; exact sub_mem h₁ h₂
  have hJ' : ∀ s ∈ lT TT, J' s = J' s ∧ (0 : Fin n' → ℕ) s ≤ J' s := fun s _ => ⟨rfl, Nat.zero_le _⟩
  have hZ := piL_mem (K := Kf) (D0b A B) (uS k A B) J' 0 (lT TT) lT_nodup J' _ hΔ hJ'
  have hc : (fun s => if s ∈ lT TT then J' s - (0 : Fin n' → ℕ) s else J' s) = J' := by
    funext s; split_ifs <;> simp
  rw [hc] at hZ
  have hharm : ∀ s, lapP (vL s) (cL s) (piL k Kf vL cL (uS k A B) J' 0 (lT TT) (P₁ - P₂)) = 0 := by
    intro s
    by_cases hs : s ∈ lT TT
    · exact pairs.lapP_piL (by omega) (D0b A B) (D0_zero A B) J' 0 (lT TT) lT_nodup J' _ hΔ hJ' s hs
    · refine lapP_eq_zero (d := cdeg vL cL (D0b A B) J') (Or.inl ?_) hZ
      rw [mem_lT] at hs
      rw [(pairs.cdeg_apply _ _ _).1]
      have h0 : J' s = 0 := by simp [J', Jm_of_not_mem A B hs]
      have h1 : D0b A B (vL s) = 0 := by
        simp [D0b, dL_vL, degV, nat_of_not_mem _ hs, Jm_of_not_mem A B hs]
      omega
  have hβ0 : beta Kf (piL k Kf vL cL (uS k A B) J' 0 (lT TT) (P₁ - P₂)) = 0 := by
    rw [map_piL_zero (beta Kf) _ _ (lT TT) (fun s _ => beta_hP (by omega) s), map_sub, hβ, sub_self]
  have := eq_zero_of_beta hk hZ hharm hβ0
  rwa [map_sub, sub_eq_zero] at this

omit [NeZero k] [CharZero Kf] in
/-- **Letter changes keep the letter degrees.** -/
theorem linS_mem_LHom (A : Fin (n' * 2) → Matrix (Fin k) (Fin k) Kf) {d : Fin (n' * 2) → ℕ}
    {P : LPol (Fin (n' * 2)) k Kf} (hP : P ∈ LHom Kf d) : linS k A P ∈ LHom Kf d := by
  refine map_mem_LHom (fun v => ?_) hP
  rw [linS_X, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun e _ => ?_
  rw [mem_weightedHomogeneousSubmodule]
  exact (isWeightedHomogeneous_X Kf (LetterFock.rowW _ k) (v.1, e)).C_mul _

variable {O : Type} [CommRing O] [Algebra O Kf]

/-- **The harmonic splitting** (A-N7) for `k ≥ 3`, a prime `p` and `O` in which the integers prime to `p` are
invertible: `FirstAssembly.HarmSplit` with Annex I's `u = N·⌈(k + 1)λ_a⌉` and `a_max = 8a`. -/
theorem harmSplit_of (hk : 3 ≤ k) {p : ℕ} (hp : p.Prime) (hinv : ∀ m : ℕ, ¬ p ∣ m → (m : Kf)⁻¹ ∈ Oint O Kf)
    (a : ℝ) : HarmSplit O Kf p TT k (uH TT.card k (lamA p k a)) (8 * a) := by
  intro A B hA hB hAB
  have hk2 : 2 ≤ k := by omega
  set d := dL (nat TT A) (nat TT B)
  set J := Jm A B
  set u := uS k A B
  set l := lT TT
  set e := (l.map fun s => (k + 1) * Nat.log p (k + nat TT A s + nat TT B s)).sum
  have he : e ≤ uH TT.card k (lamA p k a) := budget hp (by omega) hA hB hAB
  have hd : d = cdeg vL cL (D0b A B) J := dL_eq_cdeg A B
  obtain ⟨Ψ', hΨ'⟩ := exists_leftInv (psi k Kf).toLinearMap (LHom Kf d) (psi_injOn hk2 d)
  have hsec : ∀ j' : Fin n' → ℕ, ∃ g : Pol (Unit × Fin n') k Kf →ₗ[Kf] LPol (Fin (n' * 2)) k Kf,
      ∀ x ∈ LHom Kf (cdeg vL cL (D0b A B) fun s => J s - j' s),
        g (beta Kf x) ∈ LHom Kf (cdeg vL cL (D0b A B) fun s => J s - j' s) ∧ beta Kf (g (beta Kf x)) = beta Kf x :=
    fun j' => exists_section (beta Kf).toLinearMap _
  choose sec hsec using hsec
  set prj : (Fin n' → ℕ) → Module.End Kf (LPol (Fin (n' * 2)) k Kf) := fun j' => piL k Kf vL cL u J j' l
  set pz : (Fin n' → ℕ) → Module.End Kf (LPol (Fin (n' * 2)) k Kf) :=
    fun j' => piL k Kf vL cL u (fun s => J s - j' s) 0 l
  let pr : (TT → ℤ) → Pol (Bool × Fin n') k Kf →ₗ[Kf] Pol (Unit × Fin n') k Kf :=
    fun j => (beta Kf).toLinearMap ∘ₗ prj (nat TT j) ∘ₗ Ψ'
  let io : (TT → ℤ) → Pol (Unit × Fin n') k Kf →ₗ[Kf] Pol (Bool × Fin n') k Kf :=
    fun j => (psi k Kf).toLinearMap ∘ₗ LinearMap.mulLeft Kf (hProd k Kf vL cL (nat TT j) l) ∘ₗ pz (nat TT j) ∘ₗ
      sec (nat TT j)
  -- the pieces of `H(A, B)` in the letter model
  have hprj_mem : ∀ j ∈ jBox A B, ∀ P ∈ LHom Kf d,
      prj (nat TT j) P ∈ LHom Kf (dL (nat TT (A - j)) (nat TT (B - j))) := fun j hj P hP => by
    have h := piL_mem (K := Kf) (D0b A B) u J (nat TT j) l lT_nodup J P (hd ▸ hP)
      (fun s _ => ⟨rfl, nat_le_Jm hj s⟩)
    rw [dL_sub hj]
    convert h using 3
    funext s
    by_cases hs : s ∈ l
    · simp [hs, J]
    · have hs' : s ∉ TT := fun h' => hs (mem_lT.2 h')
      simp [hs, J, Jm_of_not_mem A B hs', nat_of_not_mem _ hs']
  have hprj_harm : ∀ j ∈ jBox A B, ∀ P ∈ LHom Kf d, ∀ s ∈ l,
      lapP (vL s) (cL s) (prj (nat TT j) P) = 0 := fun j hj P hP s hs =>
    pairs.lapP_piL hk2 (D0b A B) (D0_zero A B) J (nat TT j) l lT_nodup J P (hd ▸ hP)
      (fun s _ => ⟨rfl, nat_le_Jm hj s⟩) s hs
  have hio_pr : ∀ j ∈ jBox A B, ∀ P ∈ LHom Kf d,
      io j (pr j (psi k Kf P)) = psi k Kf (hProd k Kf vL cL (nat TT j) l * prj (nat TT j) P) := by
    intro j hj P hP
    have hm := hprj_mem j hj P hP
    have hs := hsec (nat TT j) (prj (nat TT j) P) (by rw [← dL_sub hj]; exact hm)
    have hfix : pz (nat TT j) (prj (nat TT j) P) = prj (nat TT j) P :=
      piL_zero_of_lapP _ _ l _ (hprj_harm j hj P hP)
    have e1 : pz (nat TT j) (sec (nat TT j) (beta Kf (prj (nat TT j) P))) = pz (nat TT j) (prj (nat TT j) P) :=
      pz_eq hk hj (by rw [dL_sub hj]; exact hs.1) hm hs.2
    simp only [io, pr, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply]
    rw [show Ψ' (psi k Kf P) = P from hΨ' P hP, e1, hfix]
  refine ⟨io, pr, fun x hx => ?_, ?_⟩
  · obtain ⟨P, hP, rfl⟩ := exists_psi hk2 hA hB hx
    rw [Finset.sum_congr rfl fun j hj => hio_pr j hj P hP,
      sum_jBox hA hB (fun j' => psi k Kf (hProd k Kf vL cL j' l * prj j' P)), ← map_sum]
    congr 1
    exact pairs.sum_piL hk2 (D0b A B) (D0_zero A B) J l lT_nodup J P (hd ▸ hP) fun s _ => rfl
  · intro Λ hΛ j hj
    choose C₀ hC₀ using hΛ
    have hdet : ∀ s, (C₀ s).det ≠ 0 := fun s => (hC₀ s).1.ne_zero
    have hAj : ∀ s, 0 ≤ (A - j) s := fun s => by
      have := jBox_spec hj s; simp only [Pi.sub_apply]; omega
    have hBj : ∀ s, 0 ≤ (B - j) s := fun s => by
      have := jBox_spec hj s; simp only [Pi.sub_apply]; omega
    set dj := dL (nat TT (A - j)) (nat TT (B - j))
    set Γ := (l.map fun s => (C₀ s).det ^ nat TT j s).prod
    have hΓ : Γ ≠ 0 := by
      simp only [Γ]
      induction l with
      | nil => simp
      | cons s l ih => rw [List.map_cons, List.prod_cons]; exact mul_ne_zero (pow_ne_zero _ (hdet s)) ih
    have htc : tcst C₀ dj = tcst C₀ d * Γ := tcst_sub C₀ hdet hj
    have htc0 : tcst C₀ d ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => zpow_ne_zero _ (hdet s)
    have hL : ∀ (i : Fin n' → ℕ), (∀ s, i s ≤ J s) → ∀ s,
        2 ≤ u s ∧ Nat.log p (u s + 2 * i s) ≤ Nat.log p (k + nat TT A s + nat TT B s) :=
      fun i hi s => ⟨by simp only [u, uS]; omega, Nat.log_mono_right (by
        have := uS_add k A B s; have := hi s; simp only [u, J] at *; omega)⟩
    -- the loss `p^u`
    have hU : ∀ F ∈ intP (Oint O Kf) (Fin (n' * 2) × Fin k),
        ∀ (J' j' : Fin n' → ℕ), (∀ s, j' s ≤ J' s) → (∀ s, J' s ≤ J s) →
          (p : Kf) ^ uH TT.card k (lamA p k a) • piL k Kf vL cL u J' j' l F ∈ intP (Oint O Kf) _ := by
      intro F hF J' j' hj' hJ'
      have h := piL_mem_intP (A := Oint O Kf) (a := vL) (b := cL) (by omega) hp hinv u J' j'
        (fun s => Nat.log p (k + nat TT A s + nat TT B s)) l (fun s _ =>
          ⟨(hL J' hJ' s).1, hj' s, (hL J' hJ' s).2⟩) F hF
      rw [show uH TT.card k (lamA p k a) = (uH TT.card k (lamA p k a) - e) + e by omega, pow_add, mul_smul]
      exact smul_mem_intP (pow_mem (natCast_mem _ p) _) h
    have htp : ∀ X, twist (blockWt (lamH (k := k) TT A B)) (fun b => C₀ b.2) (psi k Kf X) =
        tcst C₀ d • psi k Kf (linS k (Alet C₀) X) := fun X => twist_psi hk2 hA hB C₀ X
    have htb : ∀ X, twist (wt1 (FirstMeans.flatWt (k := k) TT (A - j) (B - j))) (fun b => C₀ b.2) (beta Kf X) =
        tcst C₀ dj • beta Kf (linS k (Alet C₀) X) := fun X => twist_beta hk2 hAj hBj C₀ X
    refine ⟨fun x hx => ?_, fun v hv => ?_⟩
    · rw [mem_nablaB_iff (C := fun b => C₀ b.2) (fun b => hC₀ b.2)] at hx ⊢
      obtain ⟨hxn, hxt⟩ := hx
      obtain ⟨P, hP, rfl⟩ := exists_psi hk2 hA hB hxn
      rw [htp P, ← map_smul] at hxt
      set g := tcst C₀ d • linS k (Alet C₀) P
      have hg : g ∈ LHom Kf d := Submodule.smul_mem _ _ (linS_mem_LHom _ hP)
      have hgint := (psi_mem_nablaInt_iff hk2 hA hB hg).1 hxt
      have hpr : pr j (psi k Kf P) = beta Kf (prj (nat TT j) P) := by
        simp only [pr, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
        rw [show Ψ' (psi k Kf P) = P from hΨ' P hP]
      rw [hpr]
      refine ⟨Submodule.smul_mem _ _ (beta_mem_nabla hk2 hAj hBj (hprj_mem j hj P hP)), ?_⟩
      have hl1 := piL_linS (Alet C₀) (γ := fun s => (C₀ s).det) u J (nat TT j) l
        (fun s _ => letCond_Alet C₀ s) P
      have hl2 : linS k (Alet C₀) (prj (nat TT j) P) = (Γ⁻¹ * (tcst C₀ d)⁻¹) • prj (nat TT j) g := by
        rw [map_smul, show prj (nat TT j) (linS k (Alet C₀) P) = Γ • linS k (Alet C₀) (prj (nat TT j) P) from hl1,
          smul_smul, smul_smul, show Γ⁻¹ * (tcst C₀ d)⁻¹ * tcst C₀ d * Γ = 1 by field_simp, one_smul]
      rw [HermForms.twist_smul, htb, hl2, map_smul, smul_smul, smul_smul, htc,
        show (p : Kf) ^ uH TT.card k (lamA p k a) * (tcst C₀ d * Γ) * (Γ⁻¹ * (tcst C₀ d)⁻¹) =
          (p : Kf) ^ uH TT.card k (lamA p k a) by field_simp, ← map_smul]
      exact beta_mem_nablaInt hk2 hAj hBj (Submodule.smul_mem _ _ (hprj_mem j hj g hg))
        (hU g hgint J (nat TT j) (fun s => nat_le_Jm hj s) fun s => le_rfl)
    · rw [mem_nablaB_iff (C := fun b => C₀ b.2) (fun b => hC₀ b.2)] at hv ⊢
      obtain ⟨hvn, hvt⟩ := hv
      obtain ⟨Pv, hPv, rfl⟩ := exists_beta hk2 hAj hBj hvn
      rw [htb Pv, ← map_smul] at hvt
      obtain ⟨g, hg, hgint, hgβ⟩ := exists_beta_of_mem_nablaInt hk2 hAj hBj hvt
      set Pv' := tcst C₀ dj • linS k (Alet C₀) Pv
      have hPv' : Pv' ∈ LHom Kf dj := Submodule.smul_mem _ _ (linS_mem_LHom _ hPv)
      have hpzg : pz (nat TT j) Pv' = pz (nat TT j) g := pz_eq hk hj hPv' hg hgβ.symm
      have hs := hsec (nat TT j) Pv (by rw [← dL_sub hj]; exact hPv)
      have hio : io j (beta Kf Pv) = psi k Kf (hProd k Kf vL cL (nat TT j) l * pz (nat TT j) Pv) := by
        simp only [io, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply]
        rw [pz_eq hk hj (by rw [dL_sub hj]; exact hs.1) hPv hs.2]
      rw [hio]
      have hdeg : ∀ X ∈ LHom Kf dj, hProd k Kf vL cL (nat TT j) l * X ∈ LHom Kf d := fun X hX => by
        have h := hProd_mul_mem (k := k) (Kf := Kf) (D0b A B) (nat TT j) l lT_nodup _ X (by rw [← dL_sub hj]; exact hX)
        rw [hd]
        convert h using 3
        funext s
        by_cases hs' : s ∈ l
        · simp only [hs', ite_true]; have := nat_le_Jm hj s; simp only [J] at this ⊢; omega
        · have hs'' : s ∉ TT := fun h' => hs' (mem_lT.2 h')
          simp [hs', J, Jm_of_not_mem A B hs'', nat_of_not_mem _ hs'']
      have hpzmem : ∀ X ∈ LHom Kf dj, pz (nat TT j) X ∈ LHom Kf dj := fun X hX => by
        have h := piL_mem (K := Kf) (D0b A B) u (fun s => J s - nat TT j s) 0 l lT_nodup
          (fun s => J s - nat TT j s) X (by rw [← dL_sub hj]; exact hX) (fun s _ => ⟨rfl, Nat.zero_le _⟩)
        rw [show dj = cdeg vL cL (D0b A B) (fun s => J s - nat TT j s) from dL_sub hj]
        convert h using 3
        funext s
        split_ifs <;> simp
      refine ⟨Submodule.smul_mem _ _ (psi_mem_nabla hk2 hA hB (hdeg _ (hpzmem Pv hPv))), ?_⟩
      have hl3 := piL_linS (Alet C₀) (γ := fun s => (C₀ s).det) u (fun s => J s - nat TT j s) 0 l
        (fun s _ => letCond_Alet C₀ s) Pv
      have hl4 : linS k (Alet C₀) (pz (nat TT j) Pv) = (tcst C₀ dj)⁻¹ • pz (nat TT j) g := by
        have h1 : (l.map fun s => (C₀ s).det ^ (0 : Fin n' → ℕ) s).prod = 1 := by simp
        rw [h1, one_smul] at hl3
        rw [← hl3, ← hpzg, map_smul, inv_smul_smul₀ (by rw [htc]; exact mul_ne_zero htc0 hΓ)]
      rw [HermForms.twist_smul, htp, map_mul, linS_hProd, hl4, smul_mul_smul_comm, map_smul, smul_smul,
        smul_smul, htc, show (p : Kf) ^ uH TT.card k (lamA p k a) * tcst C₀ d *
          ((l.map fun s => (C₀ s).det ^ nat TT j s).prod * (tcst C₀ d * Γ)⁻¹) =
          (p : Kf) ^ uH TT.card k (lamA p k a) by field_simp; rfl, ← map_smul, ← mul_smul_comm]
      refine (psi_mem_nablaInt_iff hk2 hA hB (hdeg _ (Submodule.smul_mem _ _ (hpzmem g hg)))).2 ?_
      exact mul_mem (hProd_mem_intP _ _) (hU g hgint (fun s => J s - nat TT j s) 0 (fun _ => Nat.zero_le _)
        fun s => Nat.sub_le _ _)

/-- **The harmonic splitting** (A-N7) at a setting `Unram` (`k ≥ 3`): `FirstAssembly.HarmSplit` with Annex I's
`u = N·⌈(k + 1)λ_a⌉` and `a_max = 8a`, for every set of tops (the integers prime to `p` are units of `O`). -/
theorem harmSplit {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ} (hU : Unram p n' W Qq O Kf ι σ j ϖ)
    (hk : 3 ≤ k) (TT : Finset (Fin n')) (a : ℝ) : HarmSplit O Kf p TT k (uH TT.card k (lamA p k a)) (8 * a) := by
  have : NeZero k := ⟨by omega⟩
  exact harmSplit_of hk hU.prime
    (fun _ hm => WeylSandwich.inv_natCast_mem_Oint hU.prime (WeylSandwich.not_isUnit_natCast_p hU) hm) a

/-- **The first local theorem (L5)** with the off-top step and the harmonic splitting discharged
(`OffTop.first_local'`, `harmSplit`): from the inputs `FlatDim`, `InputRank`, `SegMean`, `κ_P ≤ C_P·N·N₁/Y` and
`CloudStep` alone. -/
theorem first_local'' (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (Ct CI CA CP : ℝ) (hCt : 0 ≤ Ct) (hCI : 0 ≤ CI) (hCA : 0 ≤ CA)
    (hCP : 0 ≤ CP) :
    ∃ CH C : ℝ, 0 < C ∧ ∀ (p n' k : ℕ) (TT : Finset (Fin n')) (G' N₁ : ℕ) (Y Yb a b' bl bu : ℝ) (c D cStar : ℕ),
      Even n' → 5 ≤ p → FirstHyp C₀ CH p n' k TT G' N₁ Y Yb a b' bl bu c D cStar →
      ∀ (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
        [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
        (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (ϖ : O), Unram p n' W Qq O Kf ι σ j ϖ →
      FlatDim Kf TT k →
      ∀ (κP : ℝ) (κT : Fin n' → (TT → ℤ) → (TT → ℤ) → ℝ),
        InputRank W k p ι σ ϖ TT (WAp k Y a c (Jsh C₀ N₁ k a b')) (WBp bl bu c (Jsh C₀ N₁ k a b'))
          (t0F Ct C₀ N₁ p TT k G' a b' c cStar) (c4F TT c cStar) (FirstMeans.D0 CI TT.card Y N₁ k (lamA p k a)) κP κT →
        SegMean TT (WAp k Y a c (Jsh C₀ N₁ k a b')) (WBp bl bu c (Jsh C₀ N₁ k a b')) κT CA N₁ Y →
        κP ≤ CP * TT.card * N₁ / Y →
        CloudStep W k p ι σ ϖ TT c (Dcl TT.card k (lamA p k a)) b' a →
        ∃ κ : (TT → ℤ) → (TT → ℤ) → ℝ, (∀ aa bb, 0 ≤ κ aa bb) ∧ boxMean TT k Y a bl bu κ ≤ C * TT.card * N₁ / Y ∧
          ∀ (aw bw : Fin n' → ℤ) (lam0 : Fin n' → Fin k → ℤ), IsShape TT aw bw c lam0 →
            (∀ s ∈ TT, aw s ∈ aWin k Y a ∧ bw s ∈ bWin bl bu) →
            ∀ t : ℕ, depthI C (C₀ * N₁ ^ 2 * Real.log a) p n' k TT G' N₁ a b' c cStar aw bw ≤ t →
              ∀ L : Submodule W (Fin k → Qq), L.IsLattice Qq →
                LocalLattice.LLPAt p 1 ι σ ϖ lam0 t D (κ (fun s => aw s) (fun s => bw s)) cStar L := by
  obtain ⟨CH, C, hC, h⟩ := OffTop.first_local' C₀ hC₀ Ct CI CA CP hCt hCI hCA hCP
  refine ⟨CH, C, hC, ?_⟩
  intro p n' k TT G' N₁ Y Yb a b' bl bu c D cStar hn' hp hF W Qq O Kf _ _ _ _ _ _ _ _ _ _ _ ι σ j ϖ hU hFD κP κT
    hI1 hseg hκP hcl
  have hk : 3 ≤ k := by have := hF.k_ge; omega
  exact h p n' k TT G' N₁ Y Yb a b' bl bu c D cStar hn' hp hF W Qq O Kf ι σ j ϖ hU hFD (harmSplit hU hk TT a) κP κT
    hI1 hseg hκP hcl

end Split

end

end HarmSplitPf
