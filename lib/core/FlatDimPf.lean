import OffTop
import CapacitySpan

/-!
# `FlatDim` from the path basis

The dimension of `∇` at the flat weights (`FirstAssembly.FlatDim`, the Weyl count `dim V(fl(α, β)) = ∏_s Har_m(α_s,
β_s)`), from the path basis of `PathStraighten` and the bideterminant spanning of `WeylSpan`; hence the first local
theorem without the input `FlatDim` (`first_local_flat`).

**The upper bound** (`flatDim_le`, the half `FirstAssembly.key_ineq` uses). At a top `s` the block shape is
`natW(fl) = (p + q, q, …, q, 0)` (`sh`, `nu1_eq`), whose bideterminants (`WeylSpan.span_bidet`) are products of
`p` entries of the column `0` and `q` minors on the columns `0, …, k − 2` (for `k = 2` the `p + q` entries of the column
`0`). The entries are the coordinates of `v = x_{·,0}`, the minors are `0` or `±η_r` with `η = adj(x)_{k−1,·}`
(`minor_last`, by a permutation of the rows), so every bideterminant is the image under `ev : X_{0,a} ↦ v_a,
X_{1,a} ↦ η_a` of a polynomial of multidegree `(p, q)` in a vector letter and a covector letter (`bidetBlock_mem`).
These are spanned by the path polynomials of that word (`pathFam_basis`); its Pieri paths end at
`(p − j, 0, …, 0, −(q − j))`, and for `j ≥ 1` the column `p` reads `⟨v, η⟩`, killed by `ev` since
`Σ_a x_{a,0}·adj(x)_{k−1,a} = (adj(x)·x)_{k−1,0} = 0` (`ev_pathFam_eq_zero`). The surviving `j = 0` members number
`dimW(flatW) = Har` (`WeylCount.dimW_flatW`); products over the blocks span (`prod_mem_span_pi`).

**The lower bound** (in `flatDim`). The path polynomials of the canonical row path (`PR`: the letter `j` is the
column `j`, of degree `ν_j`) have the column states `x_0 ∧ … ∧ x_{h−1}` (`run_row`), invariant under adding earlier
columns (`W_init_uni`), so they lie in `∇` once placed in a block (`emb`, `prod_mem_nabla`); they are independent
(`emb_row_indep`: the path basis and the projection `proj`), and products of independent families in distinct blocks
are independent (`blocks_indep`, from `tensor_indep'`). They number `∏_s dimW(sh) = ∏_s Har` (`dimW_sh`).
-/

namespace FlatDimPf

open MvPolynomial Finset WeylFock PathBasis TwistedDegree

noncomputable section

/-! ## Maximal minors of a tall matrix -/

section Minors

variable {R : Type*} [CommRing R] {m : ℕ}

/-- **A maximal minor of a `(m + 1) × m` matrix** with arbitrary rows is `0` or `±` the minor omitting one row. -/
theorem det_rows (Y : Matrix (Fin (m + 1)) (Fin m) R) (I : Fin m → Fin (m + 1)) :
    (Y.submatrix I id).det = 0 ∨ ∃ r : Fin (m + 1), (Y.submatrix I id).det = (Y.submatrix r.succAbove id).det ∨
      (Y.submatrix I id).det = -(Y.submatrix r.succAbove id).det := by
  classical
  by_cases hI : Function.Injective I
  · obtain ⟨r, hr⟩ : ∃ r, r ∉ Set.range I := by
      by_contra h
      have hs : Function.Surjective I := fun r => by
        by_contra hr; exact h ⟨r, hr⟩
      have := Fintype.card_le_of_surjective I hs
      simp at this
    have hex : ∀ a, ∃ z, r.succAbove z = I a := fun a =>
      Fin.exists_succAbove_eq fun h => hr ⟨a, h⟩
    choose σ hσ using hex
    have hσi : Function.Injective σ := fun a b h => hI (by rw [← hσ a, ← hσ b, h])
    let e : Equiv.Perm (Fin m) := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσi)
    have hY : Y.submatrix I id = (Y.submatrix r.succAbove id).submatrix e id := by
      ext a b; simp [e, hσ]
    right
    refine ⟨r, ?_⟩
    rw [hY, Matrix.det_permute]
    rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h
    · left; simp [h]
    · right; simp [h]
  · left
    simp only [Function.Injective, not_forall] at hI
    obtain ⟨a, b, hab, hne⟩ := hI
    exact Matrix.det_zero_of_row_eq hne (by ext c; simp [hab])

/-- **The last row of the adjugate** is `±` the minors on the first `m` columns. -/
theorem adj_last (A : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (r : Fin (m + 1)) :
    A.adjugate (Fin.last m) r = (-1) ^ (r.val + m) * (A.submatrix r.succAbove Fin.castSucc).det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, Fin.val_last]

/-- **A maximal minor on the first `m` columns** lies in `{0} ∪ ±` the last row of the adjugate. -/
theorem minor_last (A : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (I : Fin m → Fin (m + 1)) :
    ∃ (r : Fin (m + 1)) (c : R), (c = 0 ∨ c = 1 ∨ c = -1) ∧
      (A.submatrix I Fin.castSucc).det = c * A.adjugate (Fin.last m) r := by
  have hsq : ∀ r : Fin (m + 1), ((-1 : R) ^ (r.val + m)) * (-1) ^ (r.val + m) = 1 := fun r => by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  have e : A.submatrix I Fin.castSucc = (A.submatrix id Fin.castSucc).submatrix I id := by ext; simp
  rcases det_rows (A.submatrix id Fin.castSucc) I with h | ⟨r, h | h⟩
  · exact ⟨0, 0, Or.inl rfl, by rw [e, h, zero_mul]⟩
  · refine ⟨r, (-1) ^ (r.val + m), ?_, ?_⟩
    · rcases neg_one_pow_eq_or R (r.val + m) with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    · rw [e, h, adj_last, ← mul_assoc, hsq, one_mul]; rfl
  · refine ⟨r, -(-1) ^ (r.val + m), ?_, ?_⟩
    · rcases neg_one_pow_eq_or R (r.val + m) with h' | h'
      · rw [h']; exact Or.inr (Or.inr rfl)
      · rw [h', neg_neg]; exact Or.inr (Or.inl rfl)
    · rw [e, h, adj_last, neg_mul, ← mul_assoc, hsq, one_mul]; rfl

end Minors

/-! ## The word of a vector letter and a covector letter -/

section Word

variable {m : ℕ}

/-- **The flags**: the letter `0` is a vector letter, the others covector letters. -/
def vec2 : ℕ → Bool := fun t => decide (t = 0)

/-- **The degrees** `(p, q)`. -/
def B2 (p q : ℕ) : ℕ → ℕ := fun t => if t = 0 then p else if t = 1 then q else 0

/-- **The first row** of length `p`. -/
def row1 (m p : ℕ) : Fin (m + 1) → ℤ := fun a => if a.val = 0 then p else 0

/-- **The weights of the path `j = 0`**: `0`, `(p, 0, …, 0)`, `flatW m p q`. -/
def mu0 (m p q : ℕ) : ℕ → Fin (m + 1) → ℤ :=
  fun t => if t = 0 then 0 else if t = 1 then row1 m p else WeylCount.flatW m p q

/-- **The first row sums to `p`.** -/
theorem sum_row1 (m p : ℕ) : ∑ a, row1 m p a = p := by
  rw [← Finset.add_sum_erase _ _ (mem_univ (0 : Fin (m + 1)))]
  rw [Finset.sum_eq_zero fun b hb => ?_]
  · simp [row1]
  · have : b.val ≠ 0 := fun h => Finset.ne_of_mem_erase hb (by ext; simpa using h)
    simp [row1, this]

/-- **The path `j = 0`** of the word. -/
def P0 (hm : 1 ≤ m) (p q : ℕ) : PieriPath (m + 1) 2 vec2 (B2 p q) where
  mu := mu0 m p q
  zero := by simp [mu0]
  step t ht := by
    interval_cases t
    · show IsStrip _ _ _
      simp only [mu0, B2, ite_true, show (0 + 1 : ℕ) ≠ 0 by omega, show (0 + 1 : ℕ) = 1 by omega, ite_false]
      refine ⟨fun a => ?_, fun a a' h => ?_, ?_⟩
      · simp only [row1, Pi.zero_apply]; split_ifs <;> omega
      · simp only [row1, Pi.zero_apply]; split_ifs <;> omega
      · rw [sum_row1]; simp
    · show IsStrip _ _ _
      simp only [mu0, B2, show (1 : ℕ) ≠ 0 by omega, ite_false, ite_true, show (1 + 1 : ℕ) ≠ 0 by omega,
        show (1 + 1 : ℕ) ≠ 1 by omega]
      refine ⟨fun a => ?_, fun a a' h => ?_, ?_⟩
      · simp only [row1, WeylCount.flatW]; split_ifs <;> omega
      · simp only [row1, WeylCount.flatW]; split_ifs <;> omega
      · rw [WeylCount.sum_flatW hm, sum_row1]
        ring
  stop t ht := by
    simp only [mu0, show t ≠ 0 by omega, show t ≠ 1 by omega, ite_false, show (2 : ℕ) ≠ 0 by omega,
      show (2 : ℕ) ≠ 1 by omega]

/-- **The first weight of every path of the word** is the first row. -/
theorem mu_one {p q : ℕ} (P : PieriPath (m + 1) 2 vec2 (B2 p q)) : P.mu 1 = row1 m p := by
  have hs0 : IsStrip 0 (P.mu 1) p := by
    have := P.step 0 (by omega); rwa [P.zero] at this
  have hz : ∀ b : Fin (m + 1), b.val ≠ 0 → P.mu 1 b = 0 := fun b hb => by
    have h1 := hs0.2.1 ⟨b.val - 1, by omega⟩ b (by simp; omega)
    have h2 := hs0.1 b
    simp only [Pi.zero_apply] at h1 h2
    omega
  funext a
  by_cases ha : a.val = 0
  · have hsum := hs0.2.2
    simp only [Pi.zero_apply, Finset.sum_const_zero, zero_add] at hsum
    rw [← Finset.add_sum_erase _ _ (mem_univ (0 : Fin (m + 1))),
      Finset.sum_eq_zero fun b hb => hz b fun h => Finset.ne_of_mem_erase hb (by ext; simpa using h),
      add_zero] at hsum
    have : a = 0 := Fin.ext ha
    subst this
    simp [row1, hsum]
  · simp [row1, ha, hz a ha]

/-- **Every path other than `j = 0` carries `⟨v, η⟩`**: under any ring homomorphism killing
`Σ_a X_{1,a}·X_{0,a}`, its path polynomials vanish. -/
theorem ev_pathFam_eq_zero (hm : 1 ≤ m) {K A : Type*} [CommRing K] [CommRing A]
    (ev : MvPolynomial (ℕ × Fin (m + 1)) K →+* A) (hev : ∑ a, ev (X (1, a)) * ev (X (0, a)) = 0) {p q : ℕ}
    (x : PathIdx (m + 1) 2 vec2 (B2 p q)) (hx : x.1 ≠ P0 hm p q) : ev (pathFam K x) = 0 := by
  classical
  obtain ⟨P, I, hI⟩ := x
  simp only at hx
  have h1 := mu_one P
  have hs1 : IsStrip (P.mu 2) (P.mu 1) q := P.step 1 (by omega)
  have h2le : ∀ a, P.mu 2 a ≤ row1 m p a := fun a => h1 ▸ hs1.1 a
  have h20 : 0 ≤ P.mu 2 0 := by
    have := hs1.2.1 0 ⟨1, by omega⟩ (by simp)
    rw [h1] at this
    simpa [row1] using this
  have hmid : ∀ a : Fin (m + 1), a.val ≠ 0 → a.val ≠ m → P.mu 2 a = 0 := fun a ha0 ham => by
    have h3 := hs1.2.1 a ⟨a.val + 1, by omega⟩ (by simp)
    have h4 := h2le a
    rw [h1] at h3
    simp only [row1, show a.val + 1 ≠ 0 by omega, ite_false, ha0] at h3 h4
    omega
  have h2p : P.mu 2 0 < p := by
    by_contra hge
    apply hx
    apply CapacitySpan.PieriPath.ext'
    have hp0 : P.mu 2 0 = p := le_antisymm (by simpa [row1] using h2le 0) (by omega)
    have hlast : P.mu 2 (Fin.last m) = -q := by
      have hsum := hs1.2.2
      rw [h1, sum_row1] at hsum
      have e2 : ∑ a, P.mu 2 a = P.mu 2 0 + P.mu 2 (Fin.last m) := by
        have hne : Fin.last m ≠ 0 := fun h => by simp [Fin.ext_iff] at h; omega
        rw [← Finset.add_sum_erase _ _ (mem_univ (0 : Fin (m + 1))),
          ← Finset.add_sum_erase _ _ (mem_erase.2 ⟨hne, mem_univ (Fin.last m)⟩),
          Finset.sum_eq_zero fun b hb => hmid b
            (fun h => Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hb) (by ext; simpa using h))
            (fun h => Finset.ne_of_mem_erase hb (by ext; simpa using h)), add_zero]
      rw [e2, hp0] at hsum
      omega
    funext t a
    simp only [P0, mu0]
    rcases Nat.lt_or_ge t 2 with ht | ht
    · interval_cases t
      · simp [P.zero]
      · simp [h1]
    · rw [P.stop t (by omega)]
      simp only [show t ≠ 0 by omega, show t ≠ 1 by omega, ite_false, WeylCount.flatW]
      by_cases ha0 : a.val = 0
      · have : a = 0 := Fin.ext ha0
        subst this; simp [hp0]
      · by_cases ham : a.val = m
        · have : a = Fin.last m := Fin.ext ham
          subst this; simp [hlast, show m ≠ 0 by omega]
        · simp [ha0, ham, hmid a ha0 ham]
  -- the column `p` reads `⟨v, η⟩`
  have hp1 : 1 ≤ (p : ℤ) := by omega
  have hc0 : colH (P.mu 0) p = 0 := by
    rw [P.zero]; unfold colH; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a _ h; simp only [Pi.zero_apply] at h; omega
  have hc1 : colH (P.mu 1) p = 1 := by
    rw [h1]; unfold colH
    refine Finset.card_eq_one.2 ⟨0, Finset.eq_singleton_iff_unique_mem.2 ⟨by simp [row1], fun a ha => ?_⟩⟩
    rw [Finset.mem_filter] at ha
    by_contra hne
    have : a.val ≠ 0 := fun h' => hne (Fin.ext h')
    have h' := ha.2
    simp only [row1, this, ite_false] at h'
    omega
  have hc2 : colH (P.mu 2) p = 0 := by
    unfold colH; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a _ h
    by_cases ha : a.val = 0
    · have : a = 0 := Fin.ext ha
      subst this; omega
    · have := h2le a; simp only [row1, ha, ite_false] at this; omega
  have hIp : I p = ∅ := by
    have := hI.1 p
    rw [hc2] at this
    unfold colSet at this
    simp only [hp1, ite_true] at this
    exact Finset.card_eq_zero.1 this
  have hK : colK K P.mu p 2 (I p) = ∑ a, X (1, a) * X (0, a) := by
    have hg : colStep P.mu p 0 = .wed := by
      rw [colStep_grow (μ := P.mu) (c := p) (t := 0) (by show colH (P.mu 0) p < colH (P.mu 1) p; omega)]
      simp [hp1]
    have hd : colStep P.mu p 1 = .con := by
      rw [colStep_drop (μ := P.mu) (c := p) (t := 1) (by show colH (P.mu 2) p < colH (P.mu 1) p; omega)]
      simp [hp1]
    rw [hIp, colK, CapStates.colSt_one_eq_run, CapStates.run_succ, CapStates.run_succ, hg, hd]
    simp only [Step.app, CapStates.run]
    rw [contr, Finset.compl_empty]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [sg, st0, wedge, Finset.filter_singleton]
  have hmem : (p : ℤ) ∈ colRange P.mu 2 := by
    have := abs_le_colRange P.mu (show 1 ≤ 2 by omega) 0
    rw [h1] at this
    simp only [row1, Fin.val_zero, ite_true, Nat.abs_cast] at this
    simp only [colRange, mem_Icc]
    have hp0 : (0 : ℤ) ≤ p := Int.natCast_nonneg p
    constructor <;> linarith
  show ev (pathPoly K P.mu 2 I) = 0
  rw [pathPoly, ← Finset.mul_prod_erase _ _ hmem, map_mul, hK, map_sum]
  simp only [map_mul]
  rw [hev, zero_mul]

end Word

/-! ## One block: the bideterminants of a flat shape -/

section Block

variable {Φ : Type*} {m : ℕ} {K : Type*} [Field K]

/-- **The flat shape** `(p + q, q, …, q, 0)`: `natW` of a flat weight. -/
def sh (m p q : ℕ) : Fin (m + 1) → ℕ := fun i => if i.val = 0 then p + q else if i.val = m then 0 else q

/-- **The evaluation of the word in a block**: `X_{0,a} ↦ x_{a,0}`, `X_{1,a} ↦ adj(x)_{m,a}`. -/
def evB (τ : Φ) : MvPolynomial (ℕ × Fin (m + 1)) K →+* Pol Φ (m + 1) K :=
  eval₂Hom MvPolynomial.C fun v =>
    if v.1 = 0 then X (τ, v.2, 0) else if v.1 = 1 then (xMat τ).adjugate (Fin.last m) v.2 else 0

/-- **`ev` kills `⟨v, η⟩`**: `Σ_a adj(x)_{m,a}·x_{a,0} = (adj(x)·x)_{m,0} = 0`. -/
theorem evB_pair (hm : 1 ≤ m) (τ : Φ) :
    ∑ a : Fin (m + 1), evB (K := K) τ (X (1, a)) * evB τ (X (0, a)) = 0 := by
  simp only [evB, coe_eval₂Hom, eval₂_X, show (1 : ℕ) ≠ 0 by omega, ite_false, ite_true]
  have h := congrFun (congrFun (Matrix.adjugate_mul (xMat (L := K) τ)) (Fin.last m)) 0
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_ne (by simp [Fin.ext_iff]; omega), smul_zero] at h
  rw [← h]
  rfl

/-- **The degree `(a, b)` in the letters `0, 1`.** -/
def deg2 (a b : ℕ) : ℕ → ℕ := fun t => if t = 0 then a else if t = 1 then b else 0

/-- **The images of the polynomials of degree `(a, b)`.** -/
def E (τ : Φ) (a b : ℕ) : Set (Pol Φ (m + 1) K) :=
  evB τ '' {F | IsWeightedHomogeneous (LetterFock.rowW ℕ (m + 1)) F (deg2 a b)}

/-- **The images multiply.** -/
theorem E_mul {τ : Φ} {a b a' b' : ℕ} {x y : Pol Φ (m + 1) K} (hx : x ∈ E τ a b) (hy : y ∈ E τ a' b') :
    x * y ∈ E τ (a + a') (b + b') := by
  obtain ⟨F, hF, rfl⟩ := hx
  obtain ⟨G, hG, rfl⟩ := hy
  refine ⟨F * G, ?_, map_mul _ _ _⟩
  have h := IsWeightedHomogeneous.mul (show IsWeightedHomogeneous _ F _ from hF)
    (show IsWeightedHomogeneous _ G _ from hG)
  show IsWeightedHomogeneous _ _ _
  convert h using 1
  funext t; simp only [deg2, Pi.add_apply]; split_ifs <;> omega

/-- **Products of images.** -/
theorem E_prod {τ : Φ} {ι : Type*} (s : Finset ι) (f : ι → Pol Φ (m + 1) K) (a b : ι → ℕ)
    (h : ∀ i ∈ s, f i ∈ E τ (a i) (b i)) : ∏ i ∈ s, f i ∈ E τ (∑ i ∈ s, a i) (∑ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, ?_, map_one _⟩
    show IsWeightedHomogeneous _ _ _
    convert isWeightedHomogeneous_one K (LetterFock.rowW ℕ (m + 1)) using 1
    funext t; simp [deg2]
  | insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi, sum_insert hi]
    exact E_mul (h i (mem_insert_self i s)) (ih fun j hj => h j (mem_insert_of_mem hj))

/-- **The weight of a letter variable.** -/
theorem isWH_X_letter (t : ℕ) (a : Fin (m + 1)) :
    IsWeightedHomogeneous (LetterFock.rowW ℕ (m + 1)) (X (t, a) : MvPolynomial (ℕ × Fin (m + 1)) K)
      (Pi.single t 1) :=
  isWeightedHomogeneous_X K (LetterFock.rowW ℕ (m + 1)) (t, a)

/-- **An entry of the column `0` is an image of degree `(1, 0)`.** -/
theorem minor_mem_E10 (τ : Φ) (s : Fin (m + 1)) (hs : s.val = 0) (I : Fin (s + 1) → Fin (m + 1)) :
    minor τ s I ∈ E (K := K) τ 1 0 := by
  obtain ⟨sv, hsv⟩ := s
  simp only at hs
  subst hs
  refine ⟨X (0, I 0), ?_, ?_⟩
  · show IsWeightedHomogeneous _ _ _
    convert isWH_X_letter (K := K) 0 (I 0) using 1
    funext t; simp [deg2, Pi.single_apply]
  · simp only [evB, coe_eval₂Hom, eval₂_X, ite_true, minor]
    rw [Matrix.det_eq_elem_of_card_eq_one (by simp) 0]
    simp only [Matrix.submatrix_apply, xMat, Matrix.of_apply]
    rfl

/-- **A maximal minor on the leading columns is an image of degree `(0, 1)`.** -/
theorem minor_mem_E01 (τ : Φ) (s : Fin (m + 1)) (hs : s.val + 1 = m) (I : Fin (s + 1) → Fin (m + 1)) :
    minor τ s I ∈ E (K := K) τ 0 1 := by
  set e : Fin (s + 1) ≃ Fin m := finCongr hs
  have hmin : minor τ s I = ((xMat (L := K) τ).submatrix (I ∘ e.symm) Fin.castSucc).det := by
    rw [minor, ← Matrix.det_submatrix_equiv_self e]
    congr 1
  obtain ⟨r, c, hc, hdet⟩ := minor_last (xMat (L := K) τ) (I ∘ e.symm)
  rw [hmin, hdet]
  have hX : IsWeightedHomogeneous (LetterFock.rowW ℕ (m + 1)) (X (1, r) : MvPolynomial (ℕ × Fin (m + 1)) K)
      (deg2 0 1) := by
    convert isWH_X_letter (K := K) 1 r using 1
    funext t; simp only [deg2, Pi.single_apply]; split_ifs <;> omega
  have hev : evB (K := K) τ (X (1, r)) = (xMat τ).adjugate (Fin.last m) r := by
    simp [evB]
  rcases hc with rfl | rfl | rfl
  · exact ⟨0, isWeightedHomogeneous_zero _ _ _, by rw [map_zero, zero_mul]⟩
  · exact ⟨X (1, r), hX, by rw [hev, one_mul]⟩
  · exact ⟨-X (1, r), hX.neg, by rw [map_neg, hev, neg_one_mul]⟩

/-- **The flat shape is antitone.** -/
theorem antitone_sh (m p q : ℕ) : Antitone (sh m p q) := fun i j (hij : i.val ≤ j.val) => by
  have := j.isLt
  simp only [sh]
  split_ifs <;> omega

/-- **The multiplicities of the flat shape sum to `p + q`.** -/
theorem sum_mult_sh (m p q : ℕ) : ∑ s, mult (sh m p q) s = p + q := by
  have h := congrFun (congrFun (sum_mult (Φ := Unit) (ν := fun _ => sh m p q) fun _ => antitone_sh m p q) ())
    (0 : Fin (m + 1))
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Fin.val_zero, zero_le, ite_true,
    mul_one, Finset.univ_unique, Finset.sum_singleton] at h
  rw [h]
  simp [sh]

/-- **Which factors of a flat bideterminant are maximal minors.** -/
theorem mult_sh_last (hm : 1 ≤ m) {p q : ℕ} {s : Fin (m + 1)} (c : Fin (mult (sh m p q) s))
    (hc : ¬ (s.val = 0 ∧ c.val < p)) : s.val + 1 = m := by
  have hcm := c.isLt
  have hmult : mult (sh m p q) s =
      sh m p q s - (if h : s.val + 1 < m + 1 then sh m p q ⟨s.val + 1, h⟩ else 0) := rfl
  by_cases hs0 : s.val = 0
  · by_cases hm1 : m = 1
    · omega
    · exfalso
      have hcp : p ≤ c.val := by omega
      have h1 : s.val + 1 < m + 1 := by omega
      have hv : mult (sh m p q) s = p := by
        rw [hmult, dite_eq_left_of_eq_true (eq_true h1)]
        simp only [sh, hs0, ite_true, show (0 + 1 : ℕ) ≠ 0 by omega, show (0 + 1 : ℕ) ≠ m by omega, ite_false]
        omega
      omega
  · by_cases hsm : s.val = m
    · exfalso
      have hs : sh m p q s = 0 := by simp [sh, hsm, show m ≠ 0 by omega]
      have hv : mult (sh m p q) s = 0 := by rw [hmult, hs]; simp
      omega
    · by_contra hne
      have h1 : s.val + 1 < m + 1 := by omega
      have hv : mult (sh m p q) s = 0 := by
        rw [hmult, dite_eq_left_of_eq_true (eq_true h1)]
        simp only [sh, hs0, hsm, ite_false, show s.val + 1 ≠ 0 by omega, hne]
        omega
      omega

/-- **A flat bideterminant is the image of a polynomial of degree `(p, q)`.** -/
theorem bidetBlock_mem (hm : 1 ≤ m) (τ : Φ) (p q : ℕ)
    (rows : (s : Fin (m + 1)) → Fin (mult (sh m p q) s) → Fin (s + 1) → Fin (m + 1)) :
    ∏ s, ∏ c, minor τ s (rows s c) ∈ E (K := K) τ p q := by
  classical
  let a : (s : Fin (m + 1)) → Fin (mult (sh m p q) s) → ℕ := fun s c => if s.val = 0 ∧ c.val < p then 1 else 0
  let b : (s : Fin (m + 1)) → Fin (mult (sh m p q) s) → ℕ := fun s c => if s.val = 0 ∧ c.val < p then 0 else 1
  have hfac : ∀ s c, minor τ s (rows s c) ∈ E (K := K) τ (a s c) (b s c) := fun s c => by
    by_cases h : s.val = 0 ∧ c.val < p
    · simp only [a, b, h, and_self, ite_true]
      exact minor_mem_E10 τ s h.1 _
    · simp only [a, b, h, ite_false]
      exact minor_mem_E01 τ s (mult_sh_last hm c h) _
  have hsa : ∑ s, ∑ c, a s c = p := by
    rw [Finset.sum_eq_single (0 : Fin (m + 1)) (fun s _ hs => Finset.sum_eq_zero fun c _ => by
      simp [a, hs]) (by simp)]
    simp only [a, Fin.val_zero, true_and]
    rw [Finset.sum_boole]
    have hge : p ≤ mult (sh m p q) 0 := by
      simp only [mult, sh, Fin.val_zero, ite_true]
      split_ifs <;> simp_all
    rw [Fin.card_filter_val_lt]
    simp [hge]
  have hsb : ∑ s, ∑ c, b s c = q := by
    have hab : ∀ s, ∑ c, b s c = mult (sh m p q) s - ∑ c, a s c := fun s => by
      have h1 : ∀ c, a s c + b s c = 1 := fun c => by simp only [a, b]; split_ifs <;> rfl
      have h2 : ∑ c, (a s c + b s c) = mult (sh m p q) s := by simp [h1]
      rw [Finset.sum_add_distrib] at h2
      omega
    have hle : ∀ s, ∑ c, a s c ≤ mult (sh m p q) s := fun s => by
      calc ∑ c, a s c ≤ ∑ _c : Fin (mult (sh m p q) s), 1 := Finset.sum_le_sum fun c _ => by
            simp only [a]; split_ifs <;> omega
        _ = mult (sh m p q) s := by simp
    rw [Finset.sum_congr rfl fun s _ => hab s, Finset.sum_tsub_distrib _ fun s _ => hle s, sum_mult_sh, hsa]
    omega
  have := E_prod (K := K) (τ := τ) univ (fun s => ∏ c, minor τ s (rows s c)) (fun s => ∑ c, a s c)
    (fun s => ∑ c, b s c) fun s _ => E_prod univ _ _ _ fun c _ => hfac s c
  rwa [hsa, hsb] at this

/-- **The word evaluation is linear.** -/
theorem evB_smul (τ : Φ) (c : K) (F : MvPolynomial (ℕ × Fin (m + 1)) K) :
    evB τ (c • F) = c • evB τ F := by
  rw [smul_eq_C_mul, map_mul, smul_eq_C_mul]
  simp [evB]

/-- **The surviving members** `ev(Ψ(P₀, I))`, `I` a standard filling of `flatW m p q`. -/
def gB (τ : Φ) (p q : ℕ) (I : {I // IsStdFilling (WeylCount.flatW m p q) I}) : Pol Φ (m + 1) K :=
  evB τ (pathPoly K (mu0 m p q) 2 I.1)

/-- **The images of degree `(p, q)` are spanned by the surviving members.** -/
theorem E_subset_span (hm : 1 ≤ m) (τ : Φ) (p q : ℕ) :
    E (K := K) τ p q ⊆ (Submodule.span K (Set.range (gB (K := K) (m := m) τ p q)) : Set (Pol Φ (m + 1) K)) := by
  classical
  let _ : Fintype (PathIdx (m + 1) 2 vec2 (B2 p q)) := Fintype.ofFinite _
  rintro _ ⟨F, hF, rfl⟩
  have hF' : F ∈ weightedHomogeneousSubmodule K (LetterFock.rowW ℕ (m + 1)) (PathSpan.mdeg 2 (B2 p q)) := by
    rw [mem_weightedHomogeneousSubmodule]
    convert (show IsWeightedHomogeneous _ F _ from hF) using 1
    funext t; simp only [PathSpan.mdeg, B2, deg2]; split_ifs <;> omega
  rw [CapacitySpan.eq_sum_repr (vec := vec2) hF', map_sum]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [evB_smul]
  refine Submodule.smul_mem _ _ ?_
  by_cases hx : x.1 = P0 hm p q
  · obtain ⟨P, I, hI⟩ := x
    simp only at hx
    subst hx
    have hI' : IsStdFilling (WeylCount.flatW m p q) I := by simpa [P0, mu0] using hI
    exact Submodule.subset_span ⟨⟨I, hI'⟩, rfl⟩
  · rw [ev_pathFam_eq_zero hm (evB τ) (evB_pair hm τ) x hx]
    exact zero_mem _

end Block

/-! ## All blocks: the upper bound -/

section Global

/-- **Products of spanned elements** lie in the span of the products of the spanning families. -/
theorem prod_mem_span_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] {κ : ι → Type*} [∀ i, Fintype (κ i)] (g : ∀ i, κ i → A) (x : ι → A)
    (hx : ∀ i, x i ∈ Submodule.span K (Set.range (g i))) :
    ∏ i, x i ∈ Submodule.span K (Set.range fun f : (∀ i, κ i) => ∏ i, g i (f i)) := by
  classical
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun K).1 (hx i)
  rw [← Finset.prod_congr rfl fun i _ => hc i, Finset.prod_univ_sum]
  refine Submodule.sum_mem _ fun f _ => ?_
  have e : ∏ i, c i (f i) • g i (f i) = (∏ i, c i (f i)) • ∏ i, g i (f i) := by
    simp only [Algebra.smul_def, Finset.prod_mul_distrib, map_prod]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩)

/-- **`Har` is symmetric.** -/
theorem har_comm (m a b : ℕ) : WeylCount.har m a b = WeylCount.har m b a := by
  simp only [WeylCount.har, mul_comm]

/-- **`Har(0, 0) = 1`.** -/
theorem har_zero {m : ℕ} (hm : 1 ≤ m) : WeylCount.har m 0 0 = 1 := by
  simp only [WeylCount.har, zero_add, Nat.choose_self, Nat.choose_eq_zero_of_lt (show m - 1 < m by omega)]

/-- **The block shapes of a flat weight**: `natW` of `fl(α, β)` at a top `s` is `sh(α_s, β_s)` (even `s`) or
`sh(β_s, α_s)` (odd `s`). -/
theorem nu1_flatWt {n' m : ℕ} (hm : 1 ≤ m) (TT : Finset (Fin n')) {α β : TT → ℤ} (hα : ∀ s, 0 ≤ α s)
    (hβ : ∀ s, 0 ≤ β s) (s : Fin n') :
    LocalLattice.nu1 (FirstMeans.flatWt (k := m + 1) TT α β) ((), s) =
      if Even s.val then sh m (FirstMeans.ext TT α s).toNat (FirstMeans.ext TT β s).toNat
      else sh m (FirstMeans.ext TT β s).toNat (FirstMeans.ext TT α s).toNat := by
  have ha := FirstMeans.ext_nonneg hα s
  have hb := FirstMeans.ext_nonneg hβ s
  have hw : ∀ j : Fin (m + 1), FirstMeans.flatWt (k := m + 1) TT α β s j =
      if j.val = 0 then FirstMeans.ext TT α s else if j.val = m then -FirstMeans.ext TT β s else 0 := fun j => by
    unfold FirstMeans.flatWt
    have := j.isLt
    split_ifs <;> first | rfl | omega
  funext i
  have hi := i.isLt
  simp only [LocalLattice.nu1, LocalLattice.wt1, InertModel.blockWt, InertModel.lamAt, natW, detShift]
  by_cases he : Even s.val
  · simp only [he, ite_true, show 0 < m + 1 by omega, dite_true, show m + 1 - 1 = m by omega, hw, sh]
    split_ifs <;> omega
  · simp only [he, ite_false, show 0 < m + 1 by omega, dite_true, show m + 1 - 1 = m by omega, hw, sh,
      Fin.val_rev]
    split_ifs <;> omega

/-- **The block degrees of a flat weight**: `(α_s, β_s)` at an even top, `(β_s, α_s)` at an odd one. -/
def pqf {n' : ℕ} (TT : Finset (Fin n')) (α β : TT → ℤ) : Unit × Fin n' → ℕ × ℕ := fun b =>
  if Even b.2.val then ((FirstMeans.ext TT α b.2).toNat, (FirstMeans.ext TT β b.2).toNat)
  else ((FirstMeans.ext TT β b.2).toNat, (FirstMeans.ext TT α b.2).toNat)

/-- **The shape of `∇` at a flat weight**, block by block. -/
theorem nu1_eq {n' m : ℕ} (hm : 1 ≤ m) (TT : Finset (Fin n')) {α β : TT → ℤ} (hα : ∀ s, 0 ≤ α s)
    (hβ : ∀ s, 0 ≤ β s) :
    LocalLattice.nu1 (FirstMeans.flatWt (k := m + 1) TT α β) = fun b => sh m (pqf TT α β b).1 (pqf TT α β b).2 := by
  funext b
  obtain ⟨⟨⟩, s⟩ := b
  rw [nu1_flatWt hm TT hα hβ s]
  simp only [pqf]
  split_ifs <;> rfl

/-- **The product of the block `Har`s** is the product over the tops. -/
theorem prod_har_pqf {n' m : ℕ} (hm : 1 ≤ m) (TT : Finset (Fin n')) (α β : TT → ℤ) :
    ∏ b : Unit × Fin n', WeylCount.har m (pqf TT α β b).1 (pqf TT α β b).2 =
      ∏ s : TT, WeylCount.har m (α s).toNat (β s).toNat := by
  classical
  rw [Fintype.prod_prod_type, Fintype.prod_unique]
  have h1 : ∀ s : Fin n', WeylCount.har m (pqf TT α β ((), s)).1 (pqf TT α β ((), s)).2 =
      WeylCount.har m (FirstMeans.ext TT α s).toNat (FirstMeans.ext TT β s).toNat := fun s => by
    simp only [pqf]
    split_ifs
    · rfl
    · exact har_comm _ _ _
  simp only [h1]
  rw [← Finset.prod_mul_prod_compl TT, Finset.prod_eq_one (s := TTᶜ) fun s hs => by
    simp only [FirstMeans.ext, show s ∉ TT from Finset.mem_compl.1 hs, dite_false, Int.toNat_zero]
    exact har_zero hm, mul_one, ← Finset.prod_coe_sort TT]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp [FirstMeans.ext, s.2]

/-- **`FlatDim`, the half `FirstAssembly` uses** (`key_ineq` needs only `≤`): `∇` at a flat weight is spanned by the
images `ev(Ψ(P₀, I))`, `∏_s Har(α_s, β_s)` of them. -/
theorem flatDim_le {n' : ℕ} (Kf : Type) [Field Kf] [CharZero Kf] {k : ℕ} (hk : 2 ≤ k) (TT : Finset (Fin n'))
    (α β : TT → ℤ) (hα : ∀ s, 0 ≤ α s) (hβ : ∀ s, 0 ≤ β s) :
    LocalLattice.dimV Kf (FirstMeans.flatWt (k := k) TT α β) ≤
      ∏ s : TT, WeylCount.har (k - 1) (α s).toNat (β s).toNat := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  set pq := pqf TT α β
  let κ : Unit × Fin n' → Type := fun b => {I // IsStdFilling (WeylCount.flatW m (pq b).1 (pq b).2) I}
  have hfin : ∀ b, Finite (κ b) := fun b => (card_stdFilling (WeylCount.antitone_flatW _ _ _)).1
  let _ : ∀ b, Fintype (κ b) := fun b => Fintype.ofFinite _
  let F : (∀ b, κ b) → Pol (Unit × Fin n') (m + 1) Kf := fun f => ∏ b, gB b (pq b).1 (pq b).2 (f b)
  have hle : nabla Kf (fun b => sh m (pq b).1 (pq b).2) ≤ Submodule.span Kf (Set.range F) := by
    rw [← span_bidet fun b => antitone_sh _ _ _, Submodule.span_le]
    rintro _ ⟨rows, rfl⟩
    exact prod_mem_span_pi (fun b => gB (K := Kf) b (pq b).1 (pq b).2) _ fun b =>
      E_subset_span hm b (pq b).1 (pq b).2 (bidetBlock_mem hm b (pq b).1 (pq b).2 (rows b))
  have hcard : ∀ b, Fintype.card (κ b) = WeylCount.har m (pq b).1 (pq b).2 := fun b => by
    rw [Fintype.card_eq_nat_card, (card_stdFilling (WeylCount.antitone_flatW _ _ _)).2, WeylCount.dimW_flatW hm]
  show Module.finrank Kf (nabla Kf (LocalLattice.nu1 (FirstMeans.flatWt (k := m + 1) TT α β))) ≤ _
  rw [nu1_eq hm TT hα hβ]
  have : FiniteDimensional Kf (Submodule.span Kf (Set.range F)) :=
    FiniteDimensional.span_of_finite Kf (Set.finite_range F)
  calc Module.finrank Kf (nabla Kf fun b => sh m (pq b).1 (pq b).2)
      ≤ Module.finrank Kf (Submodule.span Kf (Set.range F)) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (∀ b, κ b) := finrank_range_le_card F
    _ = ∏ b, WeylCount.har m (pq b).1 (pq b).2 := by
        rw [Fintype.card_pi]; exact Finset.prod_congr rfl fun b _ => hcard b
    _ = _ := by rw [prod_har_pqf hm]; rfl

end Global

/-! ## The lower bound: the canonical row path -/

section Row

variable {m : ℕ}

/-- **The row word**: `m + 1` vector letters, the letter `j` of degree `ν_j`. -/
def BR (ν : Fin (m + 1) → ℕ) : ℕ → ℕ := fun t => if h : t < m + 1 then ν ⟨t, h⟩ else 0

/-- **The canonical row path**: the first `t` rows of `ν` after `t` letters. -/
def muR (ν : Fin (m + 1) → ℕ) : ℕ → Fin (m + 1) → ℤ := fun t a => if a.val < t then (ν a : ℤ) else 0

/-- **The canonical row path is a Pieri path** (`ν` antitone). -/
def PR {ν : Fin (m + 1) → ℕ} (hν : Antitone ν) : PieriPath (m + 1) (m + 1) (fun _ => true) (BR ν) where
  mu := muR ν
  zero := by funext a; simp [muR]
  step t ht := by
    show IsStrip _ _ _
    refine ⟨fun a => ?_, fun a a' h => ?_, ?_⟩
    · simp only [muR]; split_ifs <;> omega
    · simp only [muR]
      have : ν a' ≤ ν a := hν (Fin.le_def.2 (by omega))
      split_ifs <;> omega
    · have e : ∀ a : Fin (m + 1), muR ν (t + 1) a = muR ν t a + if a.val = t then (ν a : ℤ) else 0 := fun a => by
        simp only [muR]; split_ifs <;> omega
      rw [Finset.sum_congr rfl fun a _ => e a, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero,
        add_zero]
      congr 1
      rw [show (univ.filter fun a : Fin (m + 1) => a.val = t) = {⟨t, ht⟩} by
        ext a; simp [Fin.ext_iff]]
      simp [BR, ht]
  stop t ht := by funext a; simp only [muR]; split_ifs <;> omega

/-- **The initial segment** `[0, h)` of the coordinates. -/
def init (m h : ℕ) : Finset (Fin (m + 1)) := univ.filter fun a => a.val < h

/-- **The heights of the canonical row path**: `min(t, h_c)` for `c ≥ 1`. -/
theorem colH_muR {ν : Fin (m + 1) → ℕ} (hν : Antitone ν) {c : ℤ} (hc : 1 ≤ c) (t : ℕ) :
    colH (muR ν t) c = min t (colH (muR ν (m + 1)) c) := by
  set w : Fin (m + 1) → ℤ := fun a => (ν a : ℤ)
  have hanti : Antitone w := fun a b h => by show (ν b : ℤ) ≤ ν a; exact_mod_cast hν h
  have hA : ∀ a : Fin (m + 1), c ≤ w a ↔ a.val < colH w c := fun a => by
    constructor
    · intro h; have := le_colH hanti h; omega
    · intro h; by_contra hne; have := colH_le_of_lt hanti (not_le.1 hne); omega
  have hH : colH w c ≤ m + 1 := CapacitySpan.colH_le_n w c
  have e : ∀ t, (univ.filter fun a : Fin (m + 1) => c ≤ muR ν t a) =
      univ.filter fun a : Fin (m + 1) => a.val < min t (colH w c) := fun t => by
    ext a
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [mem_univ, true_and, muR]
    by_cases h : a.val < t
    · simp only [h, ite_true]
      rw [show c ≤ (ν a : ℤ) ↔ c ≤ w a from Iff.rfl, hA]
      omega
    · simp only [h, ite_false]
      constructor <;> intro <;> omega
  have hcard : ∀ t, colH (muR ν t) c = min t (colH w c) := fun t => by
    show (univ.filter fun a : Fin (m + 1) => c ≤ muR ν t a).card = _
    rw [e, Fin.card_filter_val_lt]
    omega
  rw [hcard, hcard, min_eq_right hH]

/-- **The steps of a column `c ≥ 1` of the row path**: wedge for the first `h_c` letters. -/
theorem colStep_muR {ν : Fin (m + 1) → ℕ} (hν : Antitone ν) {c : ℤ} (hc : 1 ≤ c) (t : ℕ) :
    colStep (muR ν) c t = if t < colH (muR ν (m + 1)) c then .wed else .keep := by
  unfold colStep
  rw [colH_muR hν hc t, colH_muR hν hc (t + 1)]
  simp only [hc, ite_true]
  split_ifs <;> first | rfl | omega

/-- **The state of a column of the row path**: the wedge of the first `h` letter vectors. -/
theorem run_row {Λ : Type*} [CommRing Λ] (y : ℕ → Fin (m + 1) → Λ) (h : ℕ) (hh : h ≤ m + 1) :
    ∀ t, CapStates.run y (fun u => if u < h then .wed else .keep) st0 t =
      CapStates.W (Matrix.of fun j d => y j.val d) (init m (min t h)) := by
  intro t
  induction t with
  | zero => rw [CapStates.run, show init m (min 0 h) = ∅ by ext a; simp [init], CapStates.W_empty]
  | succ t ih =>
    rw [CapStates.run_succ, ih]
    by_cases ht : t < h
    · simp only [ht, ite_true, Step.app]
      have hm : t < m + 1 := by omega
      have := CapStates.wedge_W_top (Matrix.of fun j d => y j.val d) (J := init m (min t h)) (m := ⟨t, hm⟩)
        (fun j hj => by simp [init] at hj; exact Fin.lt_def.2 (by simp; omega))
      change wedge (Matrix.of (fun (j : Fin (m + 1)) d => y j.val d) ⟨t, hm⟩) _ = _
      rw [this]
      congr 1
      ext a; simp [init, Fin.ext_iff]; omega
    · simp only [ht, ite_false, Step.app]
      congr 2; omega

/-- **Adding earlier rows does not change a wedge of initial rows.** -/
theorem W_init_uni {Λ : Type*} [CommRing Λ] (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) Λ)
    (u : Matrix (Fin (m + 1)) (Fin (m + 1)) Λ) (hu : u.IsUpperTriangular) (hu1 : ∀ i, u i i = 1) :
    ∀ h ≤ m + 1, CapStates.W (Matrix.of fun j d => ∑ c, u c j * Y c d) (init m h) = CapStates.W Y (init m h) := by
  intro h
  induction h with
  | zero => intro _; rw [show init m 0 = ∅ by ext a; simp [init], CapStates.W_empty, CapStates.W_empty]
  | succ h ih =>
    intro hh
    have hlt : ∀ j ∈ init m h, j < (⟨h, by omega⟩ : Fin (m + 1)) := fun j hj => by
      simp [init] at hj; exact Fin.lt_def.2 (by simp; omega)
    have hins : init m (h + 1) = insert ⟨h, by omega⟩ (init m h) := by
      ext a; simp [init, Fin.ext_iff]; omega
    rw [hins, ← CapStates.wedge_W_top _ hlt, ← CapStates.wedge_W_top _ hlt, ih (by omega)]
    funext K
    change wedge (fun d => ∑ c, u c ⟨h, by omega⟩ * Y c d) _ K = _
    rw [CapStates.wedge_comb (fun c => u c ⟨h, by omega⟩) Y]
    rw [Finset.sum_eq_single (⟨h, by omega⟩ : Fin (m + 1))]
    · rw [hu1, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with hlt' | hgt
      · rw [CapStates.wedge_W_mem Y _ (show c ∈ init m h by simp [init]; exact hlt')]
        simp
      · rw [hu hgt, zero_mul]
    · simp

end Row

/-! ## The row path polynomials of a block lie in `∇` -/

section RowNabla

variable {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {m : ℕ} {K : Type*} [Field K]

/-- **The block embedding**: the letter `j ≤ m` becomes the column `j` of the block `τ`. -/
def emb (τ : Φ) : MvPolynomial (ℕ × Fin (m + 1)) K →+* Pol Φ (m + 1) K :=
  eval₂Hom MvPolynomial.C fun v => if h : v.1 < m + 1 then X (τ, v.2, ⟨v.1, h⟩) else 0

/-- **The letter mixing** `y_j ↦ Σ_c u_{cj}·y_c` of the letters `j ≤ m`. -/
def mix (u : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : MvPolynomial (ℕ × Fin (m + 1)) K →+*
    MvPolynomial (ℕ × Fin (m + 1)) K :=
  eval₂Hom MvPolynomial.C fun v =>
    if h : v.1 < m + 1 then ∑ c, MvPolynomial.C (u c ⟨v.1, h⟩) * X (c.val, v.2) else X v

omit [Fintype Φ] [DecidableEq Φ] in
/-- **Right multiplication by `u` is the letter mixing.** -/
theorem rsub_emb (u : Φ → Matrix (Fin (m + 1)) (Fin (m + 1)) K) (τ : Φ) (F : MvPolynomial (ℕ × Fin (m + 1)) K) :
    rsub u (emb τ F) = emb τ (mix (u τ) F) := by
  change ((rsub u).toRingHom.comp (emb τ)) F = ((emb τ).comp (mix (u τ))) F
  congr 1
  refine MvPolynomial.ringHom_ext (fun r => by simp [emb, mix]) fun v => ?_
  obtain ⟨j, a⟩ := v
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, emb, mix, coe_eval₂Hom, eval₂_X]
  by_cases hj : j < m + 1
  · simp only [hj, dite_true, rsub_X, eval₂_sum, eval₂_mul, eval₂_C, eval₂_X, Fin.is_lt, Fin.eta]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  · simp only [hj, dite_false, map_zero, eval₂_X]

/-- **The row path polynomials are invariant under the unitriangular letter mixing.** -/
theorem mix_rowPoly {ν : Fin (m + 1) → ℕ} (hν : Antitone ν) (u : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hu : u.IsUpperTriangular) (hu1 : ∀ i, u i i = 1) (I : ℤ → Finset (Fin (m + 1))) :
    mix u (pathPoly K (muR ν) (m + 1) I) = pathPoly K (muR ν) (m + 1) I := by
  rw [pathPoly, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  by_cases hc : 1 ≤ c
  · set h := colH (muR ν (m + 1)) c
    have hh : h ≤ m + 1 := CapacitySpan.colH_le_n _ _
    have hst : colStep (muR ν) c = fun t => if t < h then .wed else .keep := funext (colStep_muR hν hc)
    rw [colK, CapStates.colSt_one_eq_run, hst, run_row _ h hh, CapStates.map_W]
    have hmat : (Matrix.of fun (j : Fin (m + 1)) d => (X (j.val, d) : MvPolynomial (ℕ × Fin (m + 1)) K)).map
        (mix u) = Matrix.of fun j d => ∑ c, (u.map MvPolynomial.C) c j *
          (Matrix.of fun (j : Fin (m + 1)) d => (X (j.val, d) : MvPolynomial (ℕ × Fin (m + 1)) K)) c d := by
      refine Matrix.ext fun j d => ?_
      simp [mix, Fin.is_le]
    rw [hmat, W_init_uni _ (u.map MvPolynomial.C) (fun i j hij => by simp [hu hij]) (fun i => by simp [hu1])
      _ (by omega)]
  · have hconst : ∀ t ≤ m + 1, colH (muR ν t) c = colH (muR ν 0) c := fun t _ => by
      have e : ∀ t, colH (muR ν t) c = m + 1 := fun t => by
        unfold colH
        rw [Finset.filter_true_of_mem fun a _ => by simp only [muR]; split_ifs <;> omega]
        simp
      rw [e, e]
    rw [colK_of_const (R := K) hconst]
    simp only [st0]
    split_ifs <;> simp

omit [Fintype Φ] in
/-- **The block embedding of a weighted-homogeneous polynomial** in the letters `≤ m`. -/
theorem emb_isWH (τ : Φ) {F : MvPolynomial (ℕ × Fin (m + 1)) K} {d : ℕ → ℕ}
    (hF : IsWeightedHomogeneous (LetterFock.rowW ℕ (m + 1)) F d) (hd : ∀ u, m + 1 ≤ u → d u = 0) :
    IsWeightedHomogeneous (colW Φ (m + 1)) (emb τ F) (Pi.single τ fun j => d j.val) := by
  classical
  rw [F.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun e he => ?_
  have hw := hF (mem_support_iff.1 he)
  have hlt : ∀ v ∈ e.support, v.1 < m + 1 := fun v hv => by
    by_contra hge
    have h1 := congrFun hw v.1
    rw [hd v.1 (by omega), Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at h1
    simp only [LetterFock.rowW] at h1
    have h2 : e v * (LetterFock.rowW ℕ (m + 1) v v.1) ≤ ∑ w ∈ e.support, (e w • LetterFock.rowW ℕ (m + 1) w) v.1 :=
      Finset.single_le_sum (f := fun w => (e w • LetterFock.rowW ℕ (m + 1) w) v.1) (fun _ _ => Nat.zero_le _) hv
    simp only [LetterFock.rowW, Pi.single_eq_same, mul_one] at h2
    have := Finsupp.mem_support_iff.1 hv
    omega
  set col : ℕ × Fin (m + 1) → Fin (m + 1) := fun v => ⟨min v.1 m, by omega⟩
  have hcol : ∀ v (hv : v ∈ e.support), col v = ⟨v.1, hlt v hv⟩ := fun v hv => by
    have := hlt v hv
    exact Fin.ext (by simp only [col]; omega)
  rw [emb, coe_eval₂Hom, eval₂_monomial, Finsupp.prod]
  rw [Finset.prod_congr rfl fun v hv => show (if h : v.1 < m + 1 then X (τ, v.2, ⟨v.1, h⟩) else 0 :
      Pol Φ (m + 1) K) ^ e v = X (τ, v.2, col v) ^ e v by rw [dite_eq_left_of_eq_true (eq_true (hlt v hv)), hcol v hv]]
  have hprod := IsWeightedHomogeneous.prod (R := K) (w := colW Φ (m + 1)) e.support
    (fun v => X (τ, v.2, col v) ^ e v) (fun v => e v • colW Φ (m + 1) (τ, v.2, col v)) fun v _ =>
      (isWeightedHomogeneous_X K (colW Φ (m + 1)) (τ, v.2, col v)).pow (e v)
  have hdeg : ∑ v ∈ e.support, e v • colW Φ (m + 1) (τ, v.2, col v) = Pi.single τ fun j => d j.val := by
    funext τ' j
    have hj := congrFun hw j.val
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at hj
    simp only [Finset.sum_apply, Pi.smul_apply, colW, Pi.single_apply, smul_eq_mul, LetterFock.rowW] at hj ⊢
    by_cases hτ : τ' = τ
    · subst hτ
      simp only [ite_true]
      rw [← hj]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [hcol v hv]
      by_cases h : j.val = v.1
      · have : j = ⟨v.1, hlt v hv⟩ := Fin.ext h
        simp [this]
      · have : j ≠ ⟨v.1, hlt v hv⟩ := fun h' => h (by rw [h'])
        simp [this, h]
    · simp [hτ]
  rw [← hdeg, ← zero_add (∑ v ∈ e.support, e v • colW Φ (m + 1) (τ, v.2, col v))]
  exact (isWeightedHomogeneous_C _ _).mul hprod

/-- **Products of row path polynomials of the blocks lie in `∇`.** -/
theorem prod_mem_nabla {ν : Φ → Fin (m + 1) → ℕ} (hν : ∀ b, Antitone (ν b)) (I : Φ → ℤ → Finset (Fin (m + 1))) :
    ∏ b, emb (K := K) b (pathPoly K (muR (ν b)) (m + 1) (I b)) ∈ nabla K ν := by
  refine mem_nabla_iff.2 ⟨?_, fun u hu => ?_⟩
  · have h := IsWeightedHomogeneous.prod (R := K) (w := colW Φ (m + 1)) univ
      (fun b => emb (K := K) b (pathPoly K (muR (ν b)) (m + 1) (I b))) (fun b => Pi.single b (ν b)) fun b _ => by
        have hw : IsWeightedHomogeneous (LetterFock.rowW ℕ (m + 1)) (pathPoly K (muR (ν b)) (m + 1) (I b))
            (fun u => if u < m + 1 then BR (ν b) u else 0) := (PR (hν b)).pathPoly_isWH (R := K) (I b)
        have := emb_isWH (K := K) b hw (fun u hu => by simp [show ¬ u < m + 1 by omega])
        convert this using 2
        funext j
        simp [BR, j.isLt]
    rwa [Finset.univ_sum_single] at h
  · rw [map_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [rsub_emb, mix_rowPoly (hν b) (u b) (hu b).1 (hu b).2]

omit [Fintype Φ] [DecidableEq Φ] in
/-- **The block embedding lands in the variables of the block.** -/
theorem emb_supported (τ : Φ) (F : MvPolynomial (ℕ × Fin (m + 1)) K) :
    emb τ F ∈ supported K {p : Φ × Fin (m + 1) × Fin (m + 1) | p.1 = τ} := by
  induction F using MvPolynomial.induction_on with
  | C a => simp only [emb, coe_eval₂Hom, eval₂_C]; exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
  | mul_X p v hp =>
    rw [map_mul]
    refine Subalgebra.mul_mem _ hp ?_
    simp only [emb, coe_eval₂Hom, eval₂_X]
    split_ifs
    · exact CapacitySpan.X_mem_supported' rfl
    · exact Subalgebra.zero_mem _

/-- **The block projection**: the column `j` of the block `τ` back to the letter `j`. -/
def proj (τ : Φ) : Pol Φ (m + 1) K →ₐ[K] MvPolynomial (ℕ × Fin (m + 1)) K :=
  aeval fun p => if p.1 = τ then X (p.2.2.val, p.2.1) else 0

omit [Fintype Φ] in
/-- **The projection undoes the embedding** on path polynomials of `m + 1` letters. -/
theorem proj_emb (τ : Φ) (μ : ℕ → Fin (m + 1) → ℤ) (I : ℤ → Finset (Fin (m + 1))) :
    proj (K := K) τ (emb τ (pathPoly K μ (m + 1) I)) = pathPoly K μ (m + 1) I := by
  set φ : MvPolynomial (ℕ × Fin (m + 1)) K →+* MvPolynomial (ℕ × Fin (m + 1)) K :=
    (proj (K := K) τ).toRingHom.comp (emb τ) with hφ
  have hX : ∀ u < m + 1, (fun a : Fin (m + 1) => φ (X (u, a))) = fun a => X (u, a) := fun u hu => by
    funext a
    have hu' : u ≤ m := by omega
    simp [hφ, proj, emb, hu']
  change φ _ = _
  rw [pathPoly, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [colK, map_colSt]
  exact congrFun (colSt_congr (y := fun t a => φ (X (t, a))) (y' := fun t a => X (t, a)) _ _ hX) _

omit [Fintype Φ] in
/-- **The row path polynomials of a block are independent.** -/
theorem emb_row_indep (τ : Φ) {ν : Fin (m + 1) → ℕ} (hν : Antitone ν) :
    LinearIndependent K (fun I : {I // IsStdFilling (muR ν (m + 1)) I} =>
      emb (K := K) τ (pathPoly K (muR ν) (m + 1) I.1)) := by
  refine LinearIndependent.of_comp (proj (K := K) τ).toLinearMap ?_
  have h := (CapacitySpan.pathFam_linearIndependent K m (m + 1) (fun _ => true) (BR ν)).comp
    (fun I : {I // IsStdFilling (muR ν (m + 1)) I} => (⟨PR hν, I⟩ : PathIdx (m + 1) (m + 1) _ _))
    fun I J h => Subtype.ext (by simpa using congrArg (fun z : PathIdx (m + 1) (m + 1) _ _ => z.2.1) h)
  convert h using 1
  funext I
  simp only [Function.comp_apply, AlgHom.toLinearMap_apply, proj_emb]
  rfl

end RowNabla

/-! ## Products of independent families in disjoint blocks -/

section Indep

variable {σ K : Type*} [Field K]

/-- **The coefficient of a product in disjoint variables.** -/
theorem coeff_mul_disj {S : Set σ} {p q : MvPolynomial σ K} (hp : p ∈ supported K S) (hq : q ∈ supported K Sᶜ)
    {m1 m2 : σ →₀ ℕ} (h1 : ∀ v ∈ m1.support, v ∈ S) (h2 : ∀ v ∈ m2.support, v ∈ Sᶜ) :
    (p * q).coeff (m1 + m2) = p.coeff m1 * q.coeff m2 := by
  classical
  have hp' := CapacitySpan.support_of_supported hp
  have hq' := CapacitySpan.support_of_supported hq
  rw [coeff_mul, Finset.sum_eq_single (m1, m2)]
  · intro x hx hne
    by_cases hp0 : p.coeff x.1 = 0
    · rw [hp0, zero_mul]
    by_cases hq0 : q.coeff x.2 = 0
    · rw [hq0, mul_zero]
    exfalso
    have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    have hpx := hp' x.1 (mem_support_iff.2 hp0)
    have hqx := hq' x.2 (mem_support_iff.2 hq0)
    have e : ∀ v, x.1 v + x.2 v = m1 v + m2 v := fun v => by
      have := DFunLike.congr_fun hx' v
      simpa only [Finsupp.add_apply] using this
    apply hne
    have e1 : x.1 = m1 := by
      ext v
      by_cases hv : v ∈ S
      · have a1 : x.2 v = 0 := by by_contra h; exact hqx v (Finsupp.mem_support_iff.2 h) hv
        have a2 : m2 v = 0 := by by_contra h; exact h2 v (Finsupp.mem_support_iff.2 h) hv
        have := e v; omega
      · have a1 : x.1 v = 0 := by by_contra h; exact hv (hpx v (Finsupp.mem_support_iff.2 h))
        have a2 : m1 v = 0 := by by_contra h; exact hv (h1 v (Finsupp.mem_support_iff.2 h))
        rw [a1, a2]
    have e2 : x.2 = m2 := by
      ext v; have := e v; rw [e1] at this; omega
    exact Prod.ext e1 e2
  · intro h
    exact absurd ((Finset.HasAntidiagonal.mem_antidiagonal (n := m1 + m2) (a := (m1, m2))).2 rfl) h

/-- **Independent families in disjoint variables**: `Σ_k u_k·V_k = 0` with `u` independent in the variables `S` and
the `V_k` in the variables `Sᶜ` forces every `V_k = 0`. -/
theorem tensor_indep' {κ : Type*} [Fintype κ] (S : Set σ) (u : κ → MvPolynomial σ K) (hu : LinearIndependent K u)
    (hsu : ∀ k, u k ∈ supported K S) (V : κ → MvPolynomial σ K) (hsV : ∀ k, V k ∈ supported K Sᶜ)
    (h : ∑ k, u k * V k = 0) : ∀ k, V k = 0 := by
  classical
  intro k0
  ext m2
  by_cases hm2 : ∀ v ∈ m2.support, v ∈ Sᶜ
  · let r : κ → K := fun k => (V k).coeff m2
    have hr : ∑ k, r k • u k = 0 := by
      ext m1
      rw [coeff_sum]
      simp only [coeff_smul, smul_eq_mul, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
      by_cases hm1 : ∀ v ∈ m1.support, v ∈ S
      · have hc := congrArg (fun F : MvPolynomial σ K => F.coeff (m1 + m2)) h
        simp only [coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hc
        rw [Finset.sum_congr rfl fun k _ => coeff_mul_disj (hsu k) (hsV k) hm1 hm2] at hc
        rw [← hc]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      · obtain ⟨v, hv, hvS⟩ : ∃ v ∈ m1.support, v ∉ S := by simpa using hm1
        refine Finset.sum_eq_zero fun k _ => ?_
        have : (u k).coeff m1 = 0 := by
          by_contra hne
          exact hvS (CapacitySpan.support_of_supported (hsu k) m1 (mem_support_iff.2 hne) v hv)
        rw [this, mul_zero]
    have := (Fintype.linearIndependent_iff.1 hu) r hr k0
    simp only [r] at this
    rw [this]; simp
  · obtain ⟨v, hv, hvS⟩ : ∃ v ∈ m2.support, v ∉ Sᶜ := by simpa using hm2
    have : (V k0).coeff m2 = 0 := by
      by_contra hne
      exact hvS (CapacitySpan.support_of_supported (hsV k0) m2 (mem_support_iff.2 hne) v hv)
    rw [this]; simp

/-- **Products of independent families in distinct blocks are independent.** -/
theorem blocks_indep {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {m : ℕ} {κ : Φ → Type*} [∀ b, Fintype (κ b)]
    (G : ∀ b, κ b → Pol Φ (m + 1) K) (hG : ∀ b, LinearIndependent K (G b))
    (hS : ∀ b x, G b x ∈ supported K {p : Φ × Fin (m + 1) × Fin (m + 1) | p.1 = b}) :
    LinearIndependent K (fun f : (∀ b, κ b) => ∏ b, G b (f b)) := by
  classical
  have key : ∀ s : Finset Φ, ∀ c : (∀ b, κ b) → K, ∑ f, c f • ∏ b ∈ s, G b (f b) = 0 →
      ∀ g : (∀ b, κ b), ∑ f ∈ univ.filter (fun f : (∀ b, κ b) => ∀ b ∈ s, f b = g b), c f = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro c h g
      rw [Finset.filter_true_of_mem fun f _ b hb => absurd hb (Finset.notMem_empty b)]
      simp only [Finset.prod_empty] at h
      rw [← Finset.sum_smul] at h
      exact (smul_eq_zero.1 h).resolve_right one_ne_zero
    | insert b0 s hb0 ih =>
      intro c h g
      have hsub : ∀ b ∈ s, {p : Φ × Fin (m + 1) × Fin (m + 1) | p.1 = b} ⊆
          {p : Φ × Fin (m + 1) × Fin (m + 1) | p.1 = b0}ᶜ := fun b hb p hp h' => by
        have e : b = b0 := (show p.1 = b from hp).symm.trans h'
        exact hb0 (e ▸ hb)
      have hsupp : ∀ x, (∑ f ∈ univ.filter (fun f : (∀ b, κ b) => f b0 = x), c f • ∏ b ∈ s, G b (f b)) ∈
          supported K {p : Φ × Fin (m + 1) × Fin (m + 1) | p.1 = b0}ᶜ := fun x =>
        Subalgebra.sum_mem _ fun f _ => Subalgebra.smul_mem _ (Subalgebra.prod_mem _ fun b hb =>
          supported_mono (hsub b hb) (hS b (f b))) _
      have h' : ∑ x : κ b0, G b0 x * (∑ f ∈ univ.filter (fun f : (∀ b, κ b) => f b0 = x),
          c f • ∏ b ∈ s, G b (f b)) = 0 := by
        rw [← h, ← Finset.sum_fiberwise univ (fun f : (∀ b, κ b) => f b0)]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun f hf => ?_
        rw [← (mem_filter.1 hf).2, Finset.prod_insert hb0, mul_smul_comm]
      have hV := tensor_indep' _ (G b0) (hG b0) (hS b0) _ hsupp h' (g b0)
      have hih := ih (fun f => if f b0 = g b0 then c f else 0) (by
        rw [← hV, Finset.sum_filter]
        exact Finset.sum_congr rfl fun f _ => by split_ifs <;> simp) g
      rw [← hih, Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun f _ => ?_
      by_cases h1 : f b0 = g b0
      · simp [h1]
      · simp [h1]
  rw [Fintype.linearIndependent_iff]
  intro c hc g
  have := key univ c hc g
  rwa [show univ.filter (fun f : (∀ b, κ b) => ∀ b ∈ univ, f b = g b) = {g} by
    ext f
    simp only [mem_filter, mem_univ, true_and, mem_singleton, forall_const]
    exact ⟨fun h => funext h, fun h b => h ▸ rfl⟩, Finset.sum_singleton] at this

end Indep

/-! ## `FlatDim` -/

section Final

/-- **The canonical row path ends at the shape.** -/
theorem muR_last {m : ℕ} (ν : Fin (m + 1) → ℕ) : muR ν (m + 1) = fun a => (ν a : ℤ) := by
  funext a; simp [muR, a.isLt]

/-- **`dimW` of a flat shape is `Har`.** -/
theorem dimW_sh {m : ℕ} (hm : 1 ≤ m) (p q : ℕ) :
    WeylCount.dimW (m + 1) (fun a => (sh m p q a : ℤ)) = WeylCount.har m p q := by
  have e : (fun a => (sh m p q a : ℤ)) = fun a => WeylCount.flatW m p q a + q := by
    funext a
    simp only [sh, WeylCount.flatW]
    split_ifs <;> push_cast <;> omega
  rw [e, WeylCount.dimW_add_const (WeylCount.antitone_flatW m p q), WeylCount.dimW_flatW hm]

/-- **`FlatDim`** (`FirstAssembly.FlatDim`): `dim V(fl(α, β)) = ∏_s Har_m(α_s, β_s)`. The bound `≤` is
`flatDim_le`; `≥`: the row path polynomials of the blocks (the standard bideterminants, `prod_mem_nabla`) lie in `∇`
and their products are independent (`emb_row_indep`, `blocks_indep`), `∏_s dimW(sh) = ∏_s Har` of them. -/
theorem flatDim {n' : ℕ} (Kf : Type) [Field Kf] [CharZero Kf] {k : ℕ} (hk : 2 ≤ k) (TT : Finset (Fin n')) :
    FirstAssembly.FlatDim Kf TT k := by
  classical
  intro α β hα hβ
  refine le_antisymm (flatDim_le Kf hk TT α β hα hβ) ?_
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  set pq := pqf TT α β
  set ν : Unit × Fin n' → Fin (m + 1) → ℕ := fun b => sh m (pq b).1 (pq b).2 with hνdef
  have hanti : ∀ b, Antitone (ν b) := fun b => antitone_sh _ _ _
  let κ : Unit × Fin n' → Type := fun b => {I // IsStdFilling (muR (ν b) (m + 1)) I}
  have hfin : ∀ b, Finite (κ b) := fun b => by
    simp only [κ, muR_last]; exact (card_stdFilling (fun i j h => by exact_mod_cast hanti b h)).1
  let _ : ∀ b, Fintype (κ b) := fun b => Fintype.ofFinite _
  have hind := blocks_indep (fun b (I : κ b) => emb (K := Kf) b (pathPoly Kf (muR (ν b)) (m + 1) I.1))
    (fun b => emb_row_indep b (hanti b)) fun b x => emb_supported b _
  have hmem : ∀ f : (∀ b, κ b), ∏ b, emb (K := Kf) b (pathPoly Kf (muR (ν b)) (m + 1) (f b).1) ∈ nabla Kf ν :=
    fun f => prod_mem_nabla hanti fun b => (f b).1
  have hfd : FiniteDimensional Kf (nabla Kf ν) := by
    rw [← span_bidet hanti]; exact FiniteDimensional.span_of_finite Kf (Set.finite_range _)
  let v : (∀ b, κ b) → nabla Kf ν := fun f =>
    ⟨∏ b, emb (K := Kf) b (pathPoly Kf (muR (ν b)) (m + 1) (f b).1), hmem f⟩
  have hv : LinearIndependent Kf v := by
    apply LinearIndependent.of_comp (nabla Kf ν).subtype
    have e : (nabla Kf ν).subtype ∘ v =
        fun f => ∏ b, emb (K := Kf) b (pathPoly Kf (muR (ν b)) (m + 1) (f b).1) := by
      funext f; rfl
    rw [e]; exact hind
  have hcard := hv.fintype_card_le_finrank
  have hk : ∀ b, Fintype.card (κ b) = WeylCount.har m (pq b).1 (pq b).2 := fun b => by
    rw [Fintype.card_eq_nat_card]
    simp only [κ, muR_last]
    rw [(card_stdFilling (fun i j h => by exact_mod_cast hanti b h)).2]
    exact dimW_sh hm _ _
  show ∏ s : TT, WeylCount.har (m + 1 - 1) (α s).toNat (β s).toNat ≤
    Module.finrank Kf (nabla Kf (LocalLattice.nu1 (FirstMeans.flatWt (k := m + 1) TT α β)))
  rw [nu1_eq hm TT hα hβ, show m + 1 - 1 = m by omega, ← prod_har_pqf hm]
  calc ∏ b : Unit × Fin n', WeylCount.har m (pq b).1 (pq b).2 = Fintype.card (∀ b, κ b) := by
        rw [Fintype.card_pi]; exact (Finset.prod_congr rfl fun b _ => hk b).symm
    _ ≤ _ := hcard

end Final

/-! ## The first local theorem without `FlatDim` -/

section FirstLocal

open WeylFock HermForms InertModel LocalLattice LocalRank FirstMeans FirstAssembly

/-- **The first local theorem (L5)** with `FlatDim` discharged (`flatDim`): `OffTop.first_local'` from the inputs
`HarmSplit`, `InputRank`, `SegMean`, `κ_P ≤ C_P·N·N₁/Y` and `CloudStep` alone (`k ≥ 2` is in `FirstHyp`). -/
theorem first_local_flat (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (Ct CI CA CP : ℝ) (hCt : 0 ≤ Ct) (hCI : 0 ≤ CI) (hCA : 0 ≤ CA)
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
        CloudStep W k p ι σ ϖ TT c (Dcl TT.card k (lamA p k a)) b' a →
        ∃ κ : (TT → ℤ) → (TT → ℤ) → ℝ, (∀ aa bb, 0 ≤ κ aa bb) ∧ boxMean TT k Y a bl bu κ ≤ C * TT.card * N₁ / Y ∧
          ∀ (aw bw : Fin n' → ℤ) (lam0 : Fin n' → Fin k → ℤ), IsShape TT aw bw c lam0 →
            (∀ s ∈ TT, aw s ∈ aWin k Y a ∧ bw s ∈ bWin bl bu) →
            ∀ t : ℕ, depthI C (C₀ * N₁ ^ 2 * Real.log a) p n' k TT G' N₁ a b' c cStar aw bw ≤ t →
              ∀ L : Submodule W (Fin k → Qq), L.IsLattice Qq →
                LLPAt p 1 ι σ ϖ lam0 t D (κ (fun s => aw s) (fun s => bw s)) cStar L := by
  obtain ⟨CH, C, hC, h⟩ := OffTop.first_local' C₀ hC₀ Ct CI CA CP hCt hCI hCA hCP
  refine ⟨CH, C, hC, ?_⟩
  intro p n' k TT G' N₁ Y Yb a b' bl bu c D cStar hn' hp hF W Qq O Kf _ _ _ _ _ _ _ _ _ _ _ ι σ j ϖ hU hHS κP κT
    hI1 hseg hκP hcl
  exact h p n' k TT G' N₁ Y Yb a b' bl bu c D cStar hn' hp hF W Qq O Kf ι σ j ϖ hU
    (flatDim Kf (by have := hF.k_ge; omega) TT) hHS κP κT hI1 hseg hκP hcl

end FirstLocal

end

end FlatDimPf
