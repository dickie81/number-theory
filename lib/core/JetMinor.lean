import Mathlib

/-!
# The jet pairing, minors and directional Hasse derivatives

D2-1 of the served valuation of the theta chain (layer 1, series).

**The jet pairing** (`jetPair`) of a polynomial `Q` with a power series `F` is `Σ_κ Q_κ·κ!·F_κ` (`κ! = mfact κ`):
apply `Q(∂)` to `F` and evaluate at `0`. The frame jets of the chain pair `F` with products of **minors**
(`minorAt`): at a position `s`, with an `l × a` frame block `T` and Z-columns `I`, the determinant of
`(i, c) ↦ Σ_α T_{iα}·Z_{s, I c, α}` (variables `P × Fin b × Fin a`: position, target index, source index).

**Directional Hasse derivatives** (`hasseDir`): the `t^β`-coefficient of `Q(Z + Σ_k t_k·dir_k)` (`shiftPoly`). A top
column records the direction `ξ` in the slots `(s, β, ·)` (`colDir`).

**Degrees in a set of variables** (`SDegLE`): every monomial has degree at most `d` in the variables of `S`. It is
closed under sums and products (degrees add), and a determinant has degree at most the sum of its column degrees (the
Leibniz formula, `sDegLE_det`). A coefficient of degree above the bound vanishes (`SDegLE.coeff_eq_zero`).

**Main results.**
* *Rank-one updates* (`det_add_rankOne`): `det(B + w·uᵀ) = det B + Σ_c u_c·det(B with column c replaced by w)`, by
  multilinearity in the columns; two columns `w` give `0`.
* *Hits beyond the columns vanish* (`hasseDir_minorProd_eq_zero`): along directions at one position `s₀` with one
  vector `ξ`, the shift adds `t_k·w` (`w_i = Σ_α T_{iα}ξ_α`, the same vector for every column) to the columns of a
  minor at `s₀` whose Z-column is `col k`: a rank-one update, so the minor is affine in these `t_k`; minors elsewhere
  do not move. So the product has degree at most the number of minors at `s₀` in these `t_k`.
* *Hits beyond the selected columns vanish* (`hasseDir_minorProd_eq_zero_cols`): with a vector per direction but only
  Z-columns in `J`, a column of a minor at `s₀` moves only if its Z-column is in `J`, so by the Leibniz formula the
  minor has degree at most `|I ∩ J|` (a minor with a repeated Z-column is `0`).

**Frame jets** (the definitions the frame-jet bounds and the bridge of the local contract are stated with): column
data of a target weight on one orbit (`ColData`: columns at each position `s ∈ ZMod n′`, their heights and Z-columns),
the frame jet of one orbit (`frameJet`) and of all orbits (`frameJetV`), the degree of the column product (`degC`),
`ρ_p = 1/(p² − 1)` (`rhoL`) and the column weights of a Hecke edge (`heckeExp`).
-/

open Finset

noncomputable section

namespace JetMinor

/-! ## The definitions -/

section Defs

variable {σ : Type}

/-- **`κ! = ∏_x κ_x!`.** -/
def mfact (κ : σ →₀ ℕ) : ℕ := κ.prod fun _ e => e.factorial

/-- **The jet pairing** `⟨Q, F⟩ = Σ_κ Q_κ·κ!·F_κ`: apply `Q(∂)` to `F` and evaluate at `0`. -/
def jetPair {K : Type} [Field K] (Q : MvPolynomial σ K) (F : MvPowerSeries σ K) : K :=
  ∑ κ ∈ Q.support, Q.coeff κ * (mfact κ : K) * MvPowerSeries.coeff κ F

/-- **The minor at position `s`**: rows `T i` (an `l × a` frame block), Z-columns `I`, entry
`(i, c) ↦ Σ_α T_{iα}·Z_{s, I c, α}` (variables `P × Fin b × Fin a`, chain order: position, target index, source
index). -/
def minorAt {K P : Type} [Field K] {a b l : ℕ} (s : P) (T : Fin l → Fin a → K) (I : Fin l → Fin b) :
    MvPolynomial (P × Fin b × Fin a) K :=
  (Matrix.of fun (i c : Fin l) =>
    ∑ α, MvPolynomial.C (T i α) * (MvPolynomial.X (s, I c, α) : MvPolynomial (P × Fin b × Fin a) K)).det

/-- **The direction** of a top column: `ξ` in the slots `(s, β, ·)`. -/
def colDir {K P : Type} [Field K] [DecidableEq P] {a b : ℕ} (s : P) (ξ : Fin a → K) (β : Fin b) :
    P × Fin b × Fin a → K :=
  fun x => if x.1 = s ∧ x.2.1 = β then ξ x.2.2 else 0

/-- **The shift** `Q(Z + Σ_k t_k·dir_k)` as a polynomial in the `t_k`. -/
def shiftPoly {K ι κ : Type} [Field K] [Fintype κ] (dir : κ → ι → K) (Q : MvPolynomial ι K) :
    MvPolynomial κ (MvPolynomial ι K) :=
  MvPolynomial.aeval (fun x => MvPolynomial.C (MvPolynomial.X x) +
    ∑ k, MvPolynomial.C (MvPolynomial.C (dir k x)) * MvPolynomial.X k) Q

/-- **The directional Hasse derivative** of multi-order `β`: the `t^β`-coefficient of `Q(Z + Σ_k t_k dir_k)`. -/
def hasseDir {K ι κ : Type} [Field K] [Fintype κ] (dir : κ → ι → K) (β : κ →₀ ℕ) (Q : MvPolynomial ι K) :
    MvPolynomial ι K :=
  (shiftPoly dir Q).coeff β

end Defs

/-! ## Degrees in a set of variables -/

section SDeg

variable {R κ : Type} [CommRing R] {S : Finset κ}

/-- **Degree at most `d` in the variables of `S`**: every monomial `m` of `p` has `Σ_{k ∈ S} m_k ≤ d`. -/
def SDegLE (S : Finset κ) (d : ℕ) (p : MvPolynomial κ R) : Prop :=
  ∀ m ∈ p.support, ∑ k ∈ S, m k ≤ d

/-- **A larger bound.** -/
theorem SDegLE.mono {d e : ℕ} {p : MvPolynomial κ R} (h : SDegLE S d p) (hde : d ≤ e) : SDegLE S e p :=
  fun m hm => (h m hm).trans hde

/-- **`0` has every degree.** -/
theorem sDegLE_zero (d : ℕ) : SDegLE S d (0 : MvPolynomial κ R) := fun m hm => by simp at hm

/-- **Sums keep the degree.** -/
theorem SDegLE.add {d : ℕ} {p q : MvPolynomial κ R} (hp : SDegLE S d p) (hq : SDegLE S d q) :
    SDegLE S d (p + q) := by
  classical
  intro m hm
  rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
  exacts [hp m h, hq m h]

/-- **Finite sums keep the degree.** -/
theorem SDegLE.sum {ι : Type} (s : Finset ι) {d : ℕ} {f : ι → MvPolynomial κ R}
    (h : ∀ i ∈ s, SDegLE S d (f i)) : SDegLE S d (∑ i ∈ s, f i) :=
  Finset.sum_induction f (SDegLE S d) (fun _ _ => SDegLE.add) (sDegLE_zero d) h

/-- **Degrees add under products.** -/
theorem SDegLE.mul {d e : ℕ} {p q : MvPolynomial κ R} (hp : SDegLE S d p) (hq : SDegLE S e q) :
    SDegLE S (d + e) (p * q) := by
  classical
  intro m hm
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul p q hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  exact add_le_add (hp _ h₁) (hq _ h₂)

/-- **Degrees add under finite products.** -/
theorem SDegLE.prod {ι : Type} (s : Finset ι) (d : ι → ℕ) {f : ι → MvPolynomial κ R}
    (h : ∀ i ∈ s, SDegLE S (d i) (f i)) : SDegLE S (∑ i ∈ s, d i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro m hm
    rw [Finset.prod_empty, ← MvPolynomial.C_1, MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hm
    rw [← (ite_ne_right_iff.1 hm).1]
    simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Constants have degree `0`.** -/
theorem sDegLE_C (c : R) : SDegLE S 0 (MvPolynomial.C c : MvPolynomial κ R) := fun m hm => by
  classical
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hm
  rw [← (ite_ne_right_iff.1 hm).1]
  simp

/-- **Integers have degree `0`.** -/
theorem sDegLE_intCast (n : ℤ) : SDegLE S 0 (n : MvPolynomial κ R) := by
  rw [← map_intCast (MvPolynomial.C : R →+* MvPolynomial κ R)]
  exact sDegLE_C _

/-- **A variable has degree at most `1`**, and `0` off `S`. -/
theorem sDegLE_X [DecidableEq κ] (k : κ) : SDegLE S (if k ∈ S then 1 else 0) (MvPolynomial.X k : MvPolynomial κ R) := by
  intro m hm
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X] at hm
  rw [← (ite_ne_right_iff.1 hm).1]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq]

/-- **A variable has degree at most `1`.** -/
theorem sDegLE_X_one (k : κ) : SDegLE S 1 (MvPolynomial.X k : MvPolynomial κ R) := by
  classical
  exact (sDegLE_X k).mono (by split_ifs <;> omega)

/-- **A coefficient beyond the degree vanishes.** -/
theorem SDegLE.coeff_eq_zero {d : ℕ} {p : MvPolynomial κ R} (hp : SDegLE S d p) {m : κ →₀ ℕ}
    (hm : d < ∑ k ∈ S, m k) : p.coeff m = 0 := by
  by_contra h
  exact absurd (hp m (MvPolynomial.mem_support_iff.2 h)) (not_le.2 hm)

/-- **The degree of a determinant** is at most the sum of its column degrees (the Leibniz formula). -/
theorem sDegLE_det {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n (MvPolynomial κ R)) (e : n → ℕ)
    (h : ∀ i c, SDegLE S (e c) (M i c)) : SDegLE S (∑ c, e c) M.det := by
  rw [Matrix.det_apply']
  refine SDegLE.sum _ fun τ _ => ?_
  have := (sDegLE_intCast (S := S) (R := R) (Equiv.Perm.sign τ : ℤ)).mul
    (SDegLE.prod univ e fun i _ => h (τ i) i)
  rwa [zero_add] at this

end SDeg

/-! ## Rank-one updates of a determinant -/

section RankOne

variable {R n : Type} [CommRing R] [Fintype n] [DecidableEq n]

/-- The rank-one update of the columns in `J`. -/
private theorem det_add_rankOne_aux (w u : n → R) (J : Finset n) :
    ∀ B : Matrix n n R, (Matrix.of fun i c => B i c + if c ∈ J then w i * u c else 0).det =
      B.det + ∑ c ∈ J, u c * (B.updateCol c w).det := by
  induction J using Finset.induction_on with
  | empty => intro B; simp; rfl
  | insert a J ha ih =>
    intro B
    set M : Matrix n n R := Matrix.of fun i c => B i c + if c ∈ J then w i * u c else 0
    have hM : (Matrix.of fun i c => B i c + if c ∈ insert a J then w i * u c else 0) =
        M.updateCol a (fun i => B i a + u a * w i) := by
      ext i c
      by_cases hc : c = a
      · subst hc
        simp [M, mul_comm]
      · simp [M, hc, Finset.mem_insert]
    have hMa : M.updateCol a (fun i => B i a) = M := by
      ext i c
      by_cases hc : c = a
      · subst hc
        simp [M, ha]
      · simp [hc]
    have hMw : M.updateCol a w =
        Matrix.of fun i c => (B.updateCol a w) i c + if c ∈ J then w i * u c else 0 := by
      ext i c
      by_cases hc : c = a
      · subst hc
        simp [M, ha]
      · simp [M, hc]
    have hzero : ∀ c ∈ J, ((B.updateCol a w).updateCol c w).det = 0 := fun c hc => by
      have hca : c ≠ a := fun h => ha (h ▸ hc)
      refine Matrix.det_zero_of_column_eq hca fun i => ?_
      simp [Matrix.updateCol_apply]
    rw [hM, show (fun i => B i a + u a * w i) = (fun i => B i a) + u a • w from rfl, Matrix.det_updateCol_add,
      Matrix.det_updateCol_smul, hMa, hMw, ih B, ih (B.updateCol a w),
      Finset.sum_eq_zero (s := J) (f := fun c => u c * ((B.updateCol a w).updateCol c w).det)
        fun c hc => by rw [hzero c hc, mul_zero], Finset.sum_insert ha]
    ring

/-- **The rank-one update of a determinant**: `det(B + w·uᵀ) = det B + Σ_c u_c·det(B with column c ↦ w)`. -/
theorem det_add_rankOne (B : Matrix n n R) (w u : n → R) :
    (Matrix.of fun i c => B i c + w i * u c).det = B.det + ∑ c, u c * (B.updateCol c w).det := by
  simpa using det_add_rankOne_aux w u univ B

end RankOne

/-! ## Shifted minors -/

section Shift

variable {K P κ : Type} [Field K] [Fintype κ] {a b : ℕ}

/-- **The shift of a frame entry** `Σ_α t_α·Z_{s,β,α}`. -/
theorem shiftPoly_entry (dir : κ → P × Fin b × Fin a → K) (s : P) (t : Fin a → K) (β : Fin b) :
    shiftPoly dir (∑ α, MvPolynomial.C (t α) * MvPolynomial.X (s, β, α)) =
      ∑ α, MvPolynomial.C (MvPolynomial.C (t α)) * (MvPolynomial.C (MvPolynomial.X (s, β, α)) +
        ∑ k, MvPolynomial.C (MvPolynomial.C (dir k (s, β, α))) * MvPolynomial.X k) := by
  simp [shiftPoly, MvPolynomial.algebraMap_apply]

/-- **The shift of a minor** is the minor of the shifted entries. -/
theorem shiftPoly_minorAt (dir : κ → P × Fin b × Fin a → K) (s : P) {l : ℕ} (T : Fin l → Fin a → K)
    (I : Fin l → Fin b) :
    shiftPoly dir (minorAt s T I) = (Matrix.of fun i c => ∑ α, MvPolynomial.C (MvPolynomial.C (T i α)) *
      (MvPolynomial.C (MvPolynomial.X (s, I c, α)) +
        ∑ k, MvPolynomial.C (MvPolynomial.C (dir k (s, I c, α))) * MvPolynomial.X k)).det := by
  rw [minorAt, shiftPoly, AlgHom.map_det]
  exact congrArg Matrix.det (Matrix.ext fun i c => shiftPoly_entry dir s (T i) (I c))

/-- **The shift of a product** is the product of the shifts. -/
theorem shiftPoly_prod {ι C : Type} (dir : κ → ι → K) (s : Finset C) (f : C → MvPolynomial ι K) :
    shiftPoly dir (∏ c ∈ s, f c) = ∏ c ∈ s, shiftPoly dir (f c) :=
  map_prod _ _ _

omit [Fintype κ] in
/-- **A shift term `c·t_k` has degree `0`** when `k ∉ S` or `c = 0`. -/
theorem sDegLE_shiftTerm {ι : Type} {S : Finset κ} (k : κ) (c : K) (h : k ∉ S ∨ c = 0) :
    SDegLE S 0 (MvPolynomial.C (MvPolynomial.C c) * MvPolynomial.X k : MvPolynomial κ (MvPolynomial ι K)) := by
  classical
  rcases h with h | h
  · have := (sDegLE_C (S := S) (MvPolynomial.C c : MvPolynomial ι K)).mul
      (sDegLE_X (S := S) (R := MvPolynomial ι K) k)
    simpa [h] using this
  · simpa [h] using sDegLE_zero (S := S) (R := MvPolynomial ι K) 0

omit [Fintype κ] in
/-- **The degree of a shifted entry** `Σ_α t_α·(Z_x + Σ_{k ∈ ks} dir_k(x)·t_k)` is that of its shift terms. -/
theorem sDegLE_entry {ι A : Type} [Fintype A] {S : Finset κ} {e : ℕ} (ks : Finset κ) (dir : κ → ι → K)
    (x : A → ι) (t : A → K) (h : ∀ α, ∀ k ∈ ks, SDegLE S e
      (MvPolynomial.C (MvPolynomial.C (dir k (x α))) * MvPolynomial.X k : MvPolynomial κ (MvPolynomial ι K))) :
    SDegLE S e (∑ α, MvPolynomial.C (MvPolynomial.C (t α)) * (MvPolynomial.C (MvPolynomial.X (x α)) +
      ∑ k ∈ ks, MvPolynomial.C (MvPolynomial.C (dir k (x α))) * MvPolynomial.X k)) := by
  refine SDegLE.sum _ fun α _ => ?_
  have := (sDegLE_C (S := S) (MvPolynomial.C (t α))).mul
    (((sDegLE_C (S := S) (MvPolynomial.X (x α))).mono (Nat.zero_le e)).add
    (SDegLE.sum ks fun k hk => h α k hk))
  rwa [zero_add] at this

omit [Fintype κ] in
/-- **A determinant of degree-`0` entries has degree `0`.** -/
theorem sDegLE_det_zero {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] {S : Finset κ}
    (M : Matrix n n (MvPolynomial κ R)) (h : ∀ i c, SDegLE S 0 (M i c)) : SDegLE S 0 M.det := by
  simpa using sDegLE_det M (fun _ => 0) h

end Shift

/-! ## Hits beyond the columns vanish -/

section Hits

variable {K P κ : Type} [Field K] [DecidableEq P] [Fintype κ] {a b : ℕ}

/-- **A shifted minor with one direction vector**: of degree at most `1` in the directions `S` at its position `s₀`,
and `0` elsewhere (the shift is the rank-one update `w·uᵀ`, `w_i = Σ_α T_{iα}ξ_α`,
`u_c = Σ_{k ∈ S, col k = I c} t_k`). -/
theorem sDegLE_shift_minor (pos : κ → P) (ξ : Fin a → K) (col : κ → Fin b) (S : Finset κ) (s₀ : P)
    (hpos : ∀ k ∈ S, pos k = s₀) (s : P) {l : ℕ} (T : Fin l → Fin a → K) (I : Fin l → Fin b) :
    SDegLE S (if s = s₀ then 1 else 0) (shiftPoly (fun k => colDir (pos k) ξ (col k)) (minorAt s T I)) := by
  classical
  set dir : κ → P × Fin b × Fin a → K := fun k => colDir (pos k) ξ (col k)
  rw [shiftPoly_minorAt]
  by_cases hs : s = s₀
  swap
  · rw [ite_eq_right hs]
    refine sDegLE_det_zero _ fun i c => ?_
    refine sDegLE_entry univ dir (fun α => (s, I c, α)) (T i) fun α k _ => sDegLE_shiftTerm k _ ?_
    by_cases hk : k ∈ S
    · refine Or.inr (ite_eq_right ?_)
      rintro ⟨h, -⟩
      exact hs (h.trans (hpos k hk))
    · exact Or.inl hk
  subst hs
  rw [ite_eq_left rfl]
  set u : Fin l → MvPolynomial κ (MvPolynomial (P × Fin b × Fin a) K) :=
    fun c => ∑ k ∈ S, if col k = I c then MvPolynomial.X k else 0
  set w : Fin l → MvPolynomial κ (MvPolynomial (P × Fin b × Fin a) K) :=
    fun i => MvPolynomial.C (MvPolynomial.C (∑ α, T i α * ξ α))
  set Bm : Matrix (Fin l) (Fin l) (MvPolynomial κ (MvPolynomial (P × Fin b × Fin a) K)) :=
    Matrix.of fun i c => ∑ α, MvPolynomial.C (MvPolynomial.C (T i α)) * (MvPolynomial.C (MvPolynomial.X (s, I c, α)) +
      ∑ k ∈ Sᶜ, MvPolynomial.C (MvPolynomial.C (dir k (s, I c, α))) * MvPolynomial.X k)
  have hS : ∀ c α, ∑ k ∈ S, MvPolynomial.C (MvPolynomial.C (dir k (s, I c, α))) * MvPolynomial.X k =
      MvPolynomial.C (MvPolynomial.C (ξ α)) * u c := fun c α => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [dir, colDir, hpos k hk, true_and]
    by_cases h : I c = col k
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
      simp
  have hM : (Matrix.of fun i c => ∑ α, MvPolynomial.C (MvPolynomial.C (T i α)) *
      (MvPolynomial.C (MvPolynomial.X (s, I c, α)) +
        ∑ k, MvPolynomial.C (MvPolynomial.C (dir k (s, I c, α))) * MvPolynomial.X k)) =
      Matrix.of fun i c => Bm i c + w i * u c := by
    refine Matrix.ext fun i c => ?_
    simp only [Matrix.of_apply, Bm, w, ← Finset.sum_add_sum_compl S, hS, map_sum, map_mul, Finset.sum_mul,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring
  rw [hM, det_add_rankOne]
  have hB : ∀ i c, SDegLE S 0 (Bm i c) := fun i c =>
    sDegLE_entry Sᶜ dir (fun α => (s, I c, α)) (T i) fun α k hk =>
      sDegLE_shiftTerm k _ (Or.inl (Finset.mem_compl.1 hk))
  have hu : ∀ c, SDegLE S 1 (u c) := fun c => SDegLE.sum S fun k _ => by
    split_ifs
    · exact sDegLE_X_one k
    · exact sDegLE_zero 1
  refine ((sDegLE_det_zero Bm hB).mono (Nat.zero_le 1)).add (SDegLE.sum _ fun c _ => ?_)
  refine (hu c).mul (sDegLE_det_zero _ fun i c' => ?_)
  by_cases hc : c' = c
  · subst hc
    rw [Matrix.updateCol_self]
    exact sDegLE_C _
  · simpa [Matrix.updateCol_apply, hc] using hB i c'

/-- **Hits beyond the columns vanish** (one position, one direction vector `ξ`): the Hasse derivative of a product
of minors along directions at the position `s₀` with a common `ξ` vanishes in total order `>` the number of columns
at `s₀` (each minor at `s₀` is affine in the joint shift: columns moved by multiples of one vector). -/
theorem hasseDir_minorProd_eq_zero {C : ℕ} (l : Fin C → ℕ) (sf : Fin C → P) (T : ∀ c, Fin (l c) → Fin a → K)
    (I : ∀ c, Fin (l c) → Fin b) (pos : κ → P) (ξ : Fin a → K) (col : κ → Fin b) (S : Finset κ) (s₀ : P)
    (hpos : ∀ k ∈ S, pos k = s₀) (β : κ →₀ ℕ) (_hβ : ∀ k, β k ≠ 0 → k ∈ S)
    (hbig : (univ.filter fun c => sf c = s₀).card < ∑ k ∈ S, β k) :
    hasseDir (fun k => colDir (pos k) ξ (col k)) β (∏ c, minorAt (sf c) (T c) (I c)) = 0 := by
  classical
  have h := SDegLE.prod univ (fun c => if sf c = s₀ then 1 else 0) fun c _ =>
    sDegLE_shift_minor pos ξ col S s₀ hpos (sf c) (T c) (I c)
  rw [Finset.sum_boole] at h
  unfold hasseDir
  rw [shiftPoly_prod]
  exact h.coeff_eq_zero (by simpa using hbig)

/-- **A shifted minor with directions in the Z-columns `J`**: of degree at most `|I ∩ J|` in the directions `S` at
its position `s₀`, and `0` elsewhere (only the columns on `J` move; a repeated Z-column makes the minor `0`). -/
theorem sDegLE_shift_minor_cols (pos : κ → P) (ξ : κ → Fin a → K) (col : κ → Fin b) (S : Finset κ) (s₀ : P)
    (J : Finset (Fin b)) (hpos : ∀ k ∈ S, pos k = s₀) (hcol : ∀ k ∈ S, col k ∈ J) (s : P) {l : ℕ}
    (T : Fin l → Fin a → K) (I : Fin l → Fin b) :
    SDegLE S (if s = s₀ then ((univ.image I) ∩ J).card else 0)
      (shiftPoly (fun k => colDir (pos k) (ξ k) (col k)) (minorAt s T I)) := by
  classical
  by_cases hinj : Function.Injective I
  · rw [shiftPoly_minorAt]
    refine (sDegLE_det _ (fun c => if s = s₀ ∧ I c ∈ J then 1 else 0) fun i c =>
      sDegLE_entry univ _ (fun α => (s, I c, α)) (T i) fun α k _ => ?_).mono ?_
    · by_cases hk : k ∈ S
      · by_cases hc : s = s₀ ∧ I c ∈ J
        · rw [ite_eq_left hc]
          simpa using (sDegLE_C (S := S) (MvPolynomial.C (colDir (pos k) (ξ k) (col k) (s, I c, α)) :
            MvPolynomial (P × Fin b × Fin a) K)).mul (sDegLE_X_one (S := S) k)
        · rw [ite_eq_right hc]
          refine sDegLE_shiftTerm k _ (Or.inr (ite_eq_right ?_))
          rintro ⟨h1, h2⟩
          exact hc ⟨h1.trans (hpos k hk), (show I c = col k from h2) ▸ hcol k hk⟩
      · exact (sDegLE_shiftTerm k _ (Or.inl hk)).mono (Nat.zero_le _)
    · by_cases hs : s = s₀
      · have hcard : (univ.filter fun c => I c ∈ J).card = ((univ.image I) ∩ J).card := by
          rw [← Finset.card_image_of_injective _ hinj]
          congr 1
          ext y
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
          constructor
          · rintro ⟨c, hc, rfl⟩
            exact ⟨⟨c, rfl⟩, hc⟩
          · rintro ⟨⟨c, rfl⟩, hc⟩
            exact ⟨c, hc, rfl⟩
        simp only [hs, true_and, ite_true, Finset.sum_boole, Nat.cast_id]
        exact hcard.le
      · simp [hs]
  · obtain ⟨c₁, c₂, h12, hne⟩ : ∃ c₁ c₂, I c₁ = I c₂ ∧ c₁ ≠ c₂ := by
      simp only [Function.Injective, not_forall] at hinj
      obtain ⟨c₁, c₂, h, hne⟩ := hinj
      exact ⟨c₁, c₂, h, hne⟩
    have h0 : minorAt s T I = 0 := Matrix.det_zero_of_column_eq hne fun i => by simp [h12]
    rw [h0, shiftPoly, map_zero]
    exact sDegLE_zero _

/-- **Hits beyond the selected columns vanish**: the same with only directions in the Z-columns `J`, bounded by
`Σ_{c at s₀} |I c ∩ J|`. -/
theorem hasseDir_minorProd_eq_zero_cols {C : ℕ} (l : Fin C → ℕ) (sf : Fin C → P)
    (T : ∀ c, Fin (l c) → Fin a → K) (I : ∀ c, Fin (l c) → Fin b) (pos : κ → P) (ξ : κ → Fin a → K)
    (col : κ → Fin b) (S : Finset κ) (s₀ : P) (J : Finset (Fin b)) (hpos : ∀ k ∈ S, pos k = s₀)
    (hcol : ∀ k ∈ S, col k ∈ J) (β : κ →₀ ℕ) (_hβ : ∀ k, β k ≠ 0 → k ∈ S)
    (hbig : ∑ c ∈ univ.filter (fun c => sf c = s₀), ((univ.image (I c)) ∩ J).card < ∑ k ∈ S, β k) :
    hasseDir (fun k => colDir (pos k) (ξ k) (col k)) β (∏ c, minorAt (sf c) (T c) (I c)) = 0 := by
  classical
  have h := SDegLE.prod univ (fun c => if sf c = s₀ then ((univ.image (I c)) ∩ J).card else 0) fun c _ =>
    sDegLE_shift_minor_cols pos ξ col S s₀ J hpos hcol (sf c) (T c) (I c)
  rw [← Finset.sum_filter] at h
  unfold hasseDir
  rw [shiftPoly_prod]
  exact h.coeff_eq_zero hbig

end Hits

/-! ## Frame jets -/

section FrameJets

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {n' a b : ℕ}

/-- **Column data** of a target weight on one orbit: at position `s`, `colN s` columns of heights `hts s c ≤ a`,
each on the Z-columns `I s c` (the target index). -/
structure ColData (n' a b : ℕ) where
  /-- The number of columns at each position. -/
  colN : ZMod n' → ℕ
  /-- Their heights. -/
  hts : ∀ s, Fin (colN s) → ℕ
  /-- The heights are at most `a`. -/
  hts_le : ∀ s c, hts s c ≤ a
  /-- The Z-columns of each column. -/
  I : ∀ s c, Fin (hts s c) → Fin b

variable [NeZero n']

/-- **The frame jet** of one orbit: the jet pairing of the product of the column minors, the minor of a column of
height `l` at `s` on the first `l` rows of the frame `T s` (a `Δ`/`∇` bideterminant in the frame). -/
def frameJet (T : ZMod n' → Fin a → Fin a → ℂ_[ℓ]) (D : ColData n' a b)
    (F : MvPowerSeries (ZMod n' × Fin b × Fin a) ℂ_[ℓ]) : ℂ_[ℓ] :=
  jetPair (∏ s, ∏ c, minorAt s (fun i α => T s (Fin.castLE (D.hts_le s c) i) α) (D.I s c)) F

/-- **The degree of the column product.** -/
def degC (D : ColData n' a b) : ℕ := ∑ s, ∑ c, D.hts s c

/-- **`ρ_p = 1/(p² − 1)`** (`v(ϖ)`). -/
def rhoL (p : ℕ) : ℝ := 1 / ((p : ℝ) ^ 2 - 1)

/-- **The column weights of a type-`i` Hecke edge** in standard position (rows `β < i` scaled by `p` at even
positions, by `p⁻¹` at odd ones): `Σ_s Σ_c (even s: min(h, i) − |I ∩ [0,i)|; odd s: |I ∩ [0,i)|)`. -/
def heckeExp (i : ℕ) (D : ColData n' a b) : ℕ :=
  ∑ s, ∑ c, if s.val % 2 = 0 then
      min (D.hts s c) i - ((univ.image (D.I s c)) ∩ univ.filter (fun β : Fin b => β.val < i)).card
    else ((univ.image (D.I s c)) ∩ univ.filter (fun β : Fin b => β.val < i)).card

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The frame jet of all orbits**: per-orbit frames and column data. -/
def frameJetV (T : V × ZMod n' → Fin a → Fin a → ℂ_[ℓ]) (D : V → ColData n' a b)
    (F : MvPowerSeries ((V × ZMod n') × Fin b × Fin a) ℂ_[ℓ]) : ℂ_[ℓ] :=
  jetPair (∏ v, ∏ s, ∏ c,
    minorAt (v, s) (fun i α => T (v, s) (Fin.castLE ((D v).hts_le s c) i) α) ((D v).I s c)) F

end FrameJets

end JetMinor
