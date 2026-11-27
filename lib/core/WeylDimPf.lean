import FlatDimPf
import FirstCloudDim

/-!
# The Weyl dimension formula for `∇` (`FirstCloud.WeylDim`)

Annex I's I8, an input of the cloud step (`FirstCloud.cloudStep`): for a dominant weight `λ` on one orbit,
`dim V(λ) = ∏_s dimW_k(λ_s)` (`weylDim`), generalising the flat case `FlatDimPf.flatDim` to every dominant weight.
Block by block, `∇(ν)` has the basis of the block products of the standard row path polynomials (`finrank_nabla`).

**The lower bound** is that of `FlatDimPf.flatDim`, which holds for every shape: the path polynomials of the
canonical row path `P_row` (`FlatDimPf.PR`: the letter `j` is the column `j`, of degree `ν_j`) with a standard
filling lie in `∇` (`FlatDimPf.prod_mem_nabla`) and are independent across the blocks (`FlatDimPf.blocks_indep`);
they number `∏_b dimW(ν_b)` (`card_std`).

**The upper bound** (`nabla_le_span`): `∇` is spanned by the bideterminants (`WeylFock.span_bidet`), and every
bideterminant straightens into the standard row path polynomials (classical standard monomial theory).
* A minor with rows `I` is `0` or `±` the wedge `y_0 ∧ ⋯ ∧ y_s` read at the set `I` (`det_eq_smul_wst`; for
  increasing rows, the expansion along the last letter, `det_eq_wst`), and the columns `c ≥ 1` of the row path are
  exactly these wedges (`colK_muR`). Matching the factors `(s, c)` of `D_{s+1}` with the columns `ν_{s+1} + 1 + c` of
  the shape (`colOf`, `prod_cols`), a letter bideterminant is `±Ψ(P_row, C)` for a filling `C` (`psi_fill`).
* `PathSpan.straighten` writes `Ψ(P_row, C)` as a `ℤ`-combination of standard `Ψ(Q, I)` with `Q = P_row` or `Q ≺ P_row`
  in the lexicographic order of the potentials. The row path is the least path of its word (`not_lt_rowH`): with
  vector letters only, a column changed by the letter `s` has height at most `s` before it, so the potential grows by
  at least `B_s·(n − s)` (`phi_ge`), with equality for the row path (`phi_eq`, `rowH_chg`). So only `Q = P_row`
  remains, and the standard `Ψ(P_row, I)` are the row path polynomials (`psi_rowH_std`). The column path of a Pieri
  path (`toH`, the converse of `PathSpan.HPath.toPieri`) carries the straightening of `PathSpan` to `PathBasis`.
-/

namespace WeylDimPf

open MvPolynomial Finset TwistedDegree PathBasis WeylFock

noncomputable section

section Wedge

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **The wedge of the first `h` letters** `y_0 ∧ ⋯ ∧ y_{h−1}`, as a state (`y_{h−1}` outermost). -/
def wst (y : ℕ → Fin n → R) : ℕ → Finset (Fin n) → R
  | 0 => st0
  | h + 1 => wedge (y h) (wst y h)

/-- **One more letter in the wedge.** -/
theorem wst_succ (y : ℕ → Fin n → R) (h : ℕ) : wst y (h + 1) = wedge (y h) (wst y h) := rfl

/-- **The wedge of the first `h` letters at increasing coordinates** is the minor `det [y_j(I_i)]_{i,j<h}`
(expansion along the last letter). -/
theorem det_eq_wst (y : ℕ → Fin n → R) : ∀ (h : ℕ) (I : Fin h → Fin n), StrictMono I →
    (Matrix.of fun i j : Fin h => y j.val (I i)).det = wst y h (univ.image I) := by
  intro h
  induction h with
  | zero =>
    intro I _
    rw [Matrix.det_isEmpty, wst, univ_eq_empty, image_empty]
    simp [st0]
  | succ h ih =>
    intro I hI
    rw [Matrix.det_succ_column _ (Fin.last h), wst_succ, wedge, sum_image fun a _ b _ hab => hI.injective hab]
    refine sum_congr rfl fun i _ => ?_
    have hsub : (Matrix.of fun i j : Fin (h + 1) => y j.val (I i)).submatrix i.succAbove (Fin.last h).succAbove =
        Matrix.of fun i' j' : Fin h => y j'.val ((I ∘ i.succAbove) i') := by
      ext a b; simp [Fin.succAbove_last]
    have himg : univ.image (I ∘ i.succAbove) = (univ.image I).erase (I i) := by
      rw [← image_image, Fin.image_succAbove_univ, ← image_erase hI.injective]
      congr 1; ext x; simp
    have hsg : (sg (I i) (univ.image I) : R) = (-1) ^ ((i : ℕ) + (Fin.last h : ℕ)) := by
      have hc : ((univ.image I).filter (I i < ·)).card = h - i := by
        rw [filter_image, card_image_of_injective _ hI.injective]
        have : (univ.filter fun j => I i < I j) = Ioi i := by ext j; simp [hI.lt_iff_lt]
        rw [this, Fin.card_Ioi]; omega
      rw [sg, hc]
      refine PathSpan.neg_one_pow_congr ?_
      have := i.isLt; simp only [Fin.val_last]; omega
    rw [hsub, ih _ (hI.comp (Fin.strictMono_succAbove i)), himg, hsg]
    simp only [Matrix.of_apply, Fin.val_last]

/-- **A minor with arbitrary rows** is an integer multiple (`0` or `±1`) of the wedge at the set of its rows. -/
theorem det_eq_smul_wst (y : ℕ → Fin n → R) {h : ℕ} (I : Fin h → Fin n) :
    ∃ ε : ℤ, (Matrix.of fun i j : Fin h => y j.val (I i)).det = (ε : R) * wst y h (univ.image I) := by
  classical
  by_cases hI : Function.Injective I
  · have hK : (univ.image I).card = h := by rw [card_image_of_injective _ hI, card_univ, Fintype.card_fin]
    set S := (univ.image I).orderEmbOfFin hK
    have hex : ∀ i, ∃ j, S j = I i := fun i => by
      have : I i ∈ univ.image (⇑S) := by rw [image_orderEmbOfFin_univ]; exact mem_image_of_mem _ (mem_univ i)
      obtain ⟨j, -, hj⟩ := mem_image.1 this
      exact ⟨j, hj⟩
    choose σ hσ using hex
    have hσi : Function.Injective σ := fun a b hab => hI (by rw [← hσ a, ← hσ b, hab])
    let e : Equiv.Perm (Fin h) := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσi)
    have hM : (Matrix.of fun i j : Fin h => y j.val (I i)) =
        (Matrix.of fun i j : Fin h => y j.val (S i)).submatrix e id := by
      ext a b; simp [e, hσ]
    refine ⟨(Equiv.Perm.sign e : ℤ), ?_⟩
    rw [hM, Matrix.det_permute, det_eq_wst y h S S.strictMono, image_orderEmbOfFin_univ]
  · refine ⟨0, ?_⟩
    simp only [Function.Injective, not_forall] at hI
    obtain ⟨a, b, hab, hne⟩ := hI
    rw [Int.cast_zero, zero_mul]
    exact Matrix.det_zero_of_row_eq hne (by ext c; simp [hab])

end Wedge

/-! ## The row path: columns and their states -/

section Row

variable {m : ℕ} {ν : Fin (m + 1) → ℕ}

/-- **The columns of the row path are wedges of initial letters**: for `c ≥ 1`, `K_c` is `y_0 ∧ ⋯ ∧ y_{h−1}`, `h` the
height of the column `c`. -/
theorem colK_muR (R : Type*) [CommRing R] (hν : Antitone ν) {c : ℤ} (hc : 1 ≤ c) :
    colK R (FlatDimPf.muR ν) c (m + 1) = wst (fun t a => X (t, a)) (colH (FlatDimPf.muR ν (m + 1)) c) := by
  obtain ⟨h, hdef⟩ : ∃ h, colH (FlatDimPf.muR ν (m + 1)) c = h := ⟨_, rfl⟩
  have hh : h ≤ m + 1 := hdef ▸ CapacitySpan.colH_le_n _ _
  rw [hdef]
  suffices H : ∀ t, colSt (fun t a => (X (t, a) : MvPolynomial (ℕ × Fin (m + 1)) R)) (colStep (FlatDimPf.muR ν) c)
      (fun _ => 1) t = wst (fun t a => X (t, a)) (min t h) by
    rw [colK, H, min_eq_right hh]
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [colSt_succ, ih, FlatDimPf.colStep_muR hν hc t, hdef]
    funext J
    by_cases ht : t < h
    · simp only [ht, ite_true, Step.app, pw, pow_one, min_eq_left ht.le, min_eq_left (Nat.succ_le_of_lt ht),
        wst_succ]
    · simp only [ht, ite_false, Step.app, pw, pow_one]
      rw [min_eq_right (by omega : h ≤ t), min_eq_right (by omega : h ≤ t + 1)]

/-- **The next row** `ν_{s+1}` (`0` after the last row): `mult ν s = ν_s − ν_{s+1}`. -/
def nx (ν : Fin (m + 1) → ℕ) (s : Fin (m + 1)) : ℕ := if h : s.val + 1 < m + 1 then ν ⟨s.val + 1, h⟩ else 0

/-- **The next row is shorter** (`ν` antitone). -/
theorem nx_le (hν : Antitone ν) (s : Fin (m + 1)) : nx ν s ≤ ν s := by
  unfold nx
  split_ifs with h
  · exact hν (Fin.le_def.2 (by simp))
  · exact Nat.zero_le _

/-- **The column of the `c`-th factor `D_{s+1}`** of a bideterminant: `ν_{s+1} + 1 + c`. -/
def colOf (ν : Fin (m + 1) → ℕ) (x : Σ s : Fin (m + 1), Fin (mult ν s)) : ℤ := (nx ν x.1 : ℤ) + 1 + (x.2 : ℕ)

/-- **The row path ends at the shape.** -/
theorem muR_last_apply (ν : Fin (m + 1) → ℕ) (a : Fin (m + 1)) : FlatDimPf.muR ν (m + 1) a = ν a := by
  rw [FlatDimPf.muR_last]

/-- **The columns of the factors lie in `[1, ν_0]`.** -/
theorem colOf_mem (hν : Antitone ν) (x : Σ s : Fin (m + 1), Fin (mult ν s)) :
    1 ≤ colOf ν x ∧ colOf ν x ≤ ν 0 := by
  have h1 : (x.2 : ℕ) < ν x.1 - nx ν x.1 := x.2.isLt
  have h2 := nx_le hν x.1
  have h3 : ν x.1 ≤ ν 0 := hν (Fin.zero_le _)
  unfold colOf
  omega

/-- **The column of a factor of `D_{s+1}` has height `s + 1`.** -/
theorem colH_colOf (hν : Antitone ν) (x : Σ s : Fin (m + 1), Fin (mult ν s)) :
    colH (FlatDimPf.muR ν (m + 1)) (colOf ν x) = x.1.val + 1 := by
  have h1 : (x.2 : ℕ) < ν x.1 - nx ν x.1 := x.2.isLt
  have h2 := nx_le hν x.1
  have key : ∀ a : Fin (m + 1), colOf ν x ≤ FlatDimPf.muR ν (m + 1) a ↔ a ≤ x.1 := by
    intro a
    rw [muR_last_apply]
    constructor
    · intro h
      by_contra hlt
      have hlt' : x.1.val < a.val := Fin.lt_def.1 (not_le.1 hlt)
      have h4 : x.1.val + 1 < m + 1 := by omega
      have h5 : ν a ≤ ν ⟨x.1.val + 1, h4⟩ := hν (Fin.le_def.2 (by simp only; omega))
      have h6 : nx ν x.1 = ν ⟨x.1.val + 1, h4⟩ := by simp [nx, h4]
      unfold colOf at h
      omega
    · intro h
      have h4 : ν x.1 ≤ ν a := hν h
      unfold colOf
      omega
  unfold colH
  rw [show (univ.filter fun a => colOf ν x ≤ FlatDimPf.muR ν (m + 1) a) = Iic x.1 by ext a; simp [key]]
  exact Fin.card_Iic _

/-- **Distinct factors have distinct columns.** -/
theorem colOf_injective (hν : Antitone ν) : Function.Injective (colOf ν) := by
  intro x y hxy
  have h := colH_colOf hν x
  rw [hxy, colH_colOf hν y] at h
  obtain ⟨s, c⟩ := x
  obtain ⟨t, d⟩ := y
  have hst : s = t := Fin.ext (by simp at h; omega)
  subst hst
  have : c = d := Fin.ext (by unfold colOf at hxy; simp at hxy; omega)
  subst this
  rfl

/-- **Every column in `[1, ν_0]` is the column of a factor**: the one of `D_{h}`, `h` its height. -/
theorem exists_colOf (hν : Antitone ν) {c : ℤ} (h1 : 1 ≤ c) (h2 : c ≤ ν 0) : ∃ x, colOf ν x = c := by
  have hanti : Antitone (FlatDimPf.muR ν (m + 1)) := fun a b hab => by
    rw [muR_last_apply, muR_last_apply]; exact_mod_cast hν hab
  obtain ⟨h, hdef⟩ : ∃ h, colH (FlatDimPf.muR ν (m + 1)) c = h := ⟨_, rfl⟩
  have hh1 : 1 ≤ h := by
    have := le_colH hanti (i := 0) (c := c) (by rw [muR_last_apply]; exact h2)
    rw [hdef] at this
    simpa using this
  have hh2 : h ≤ m + 1 := hdef ▸ CapacitySpan.colH_le_n _ _
  obtain ⟨s, hsv⟩ : ∃ s : Fin (m + 1), s.val = h - 1 := ⟨⟨h - 1, by omega⟩, rfl⟩
  have hs : c ≤ ν s := by
    by_contra hlt
    have := colH_le_of_lt hanti (i := s) (c := c) (by rw [muR_last_apply]; omega)
    rw [hdef] at this
    omega
  have hn : (nx ν s : ℤ) < c := by
    unfold nx
    split_ifs with hs1
    · by_contra hge
      have := le_colH hanti (i := ⟨s.val + 1, hs1⟩) (c := c) (by rw [muR_last_apply]; omega)
      rw [hdef] at this
      simp only at this
      omega
    · simp only [Nat.cast_zero]
      omega
  have h3 := nx_le hν s
  have hlt : (c - nx ν s - 1).toNat < mult ν s := by
    show _ < ν s - nx ν s
    omega
  exact ⟨⟨s, ⟨_, hlt⟩⟩, by unfold colOf; simp only; omega⟩

/-- **Reindexing the columns** `1, …, ν_0` of the row path by the factors `(s, c)`, `c < mult ν s`, of a
bideterminant. -/
theorem prod_cols {M : Type*} [CommMonoid M] (hν : Antitone ν) (g : ℤ → M) :
    ∏ c ∈ Icc (1 : ℤ) (ν 0), g c = ∏ s, ∏ c' : Fin (mult ν s), g (colOf ν ⟨s, c'⟩) := by
  rw [← Fintype.prod_sigma (fun x : (Σ s : Fin (m + 1), Fin (mult ν s)) => g (colOf ν x))]
  symm
  refine prod_nbij (colOf ν) (fun x _ => mem_Icc.2 (colOf_mem hν x)) (fun x _ y _ h => colOf_injective hν h)
    (fun c hc => ?_) (fun _ _ => rfl)
  obtain ⟨x, hx⟩ := exists_colOf hν (mem_Icc.1 hc).1 (mem_Icc.1 hc).2
  exact ⟨x, mem_coe.2 (mem_univ x), hx⟩

end Row

/-! ## The column path of a Pieri path and the minimality of the row path -/

section ColPath

open PathSpan

variable {n N T : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **The window of a Pieri path**: beyond its column range and its total degree. -/
def tOf (P : PieriPath n N vec B) : ℕ := (∑ t ∈ range (N + 1), ∑ a, |P.mu t a|).toNat + ∑ s ∈ range N, B s + 1

/-- **The column range lies inside the window.** -/
theorem colRange_sub (P : PieriPath n N vec B) : colRange P.mu N ⊆ Ioo (-(tOf P : ℤ)) (tOf P) := by
  intro c hc
  have h := Int.self_le_toNat (∑ t ∈ range (N + 1), ∑ a, |P.mu t a|)
  simp only [colRange, mem_Icc] at hc
  simp only [mem_Ioo, tOf, Nat.cast_add, Nat.cast_one]
  omega

/-- **The window exceeds the total degree** (the hypothesis of `PathSpan.straighten`). -/
theorem sum_lt_tOf (P : PieriPath n N vec B) : ∑ s ∈ range N, B s < tOf P := by
  unfold tOf; omega

/-- **The column path of a Pieri path** (the converse of `PathSpan.HPath.toPieri`): the heights
`colH (μ_{min(t, N)}) c`, in the window `tOf P`. -/
def toH (P : PieriPath n N vec B) : HPath n N (tOf P) vec B where
  h t c := colH (P.mu (min t N)) c
  zero c := by
    rw [Nat.zero_min, P.zero, colH_zero]
    unfold h0
    split_ifs <;> omega
  anti _ _ := fun _ _ hcc' => colH_anti _ hcc'
  le _ _ _ := CapacitySpan.colH_le_n _ _
  out t ht c hc := by
    have hc' : c ∉ colRange P.mu N := fun h => hc (colRange_sub P h)
    rw [min_eq_left ht, colH_of_notMem hc' ht, P.zero, colH_zero]
    unfold h0
    split_ifs <;> omega
  up t ht hv c := by
    rw [min_eq_left ht.le, min_eq_left (Nat.succ_le_of_lt ht)]
    exact (P.colH_step ht c).1 hv
  down t ht hv c := by
    rw [min_eq_left ht.le, min_eq_left (Nat.succ_le_of_lt ht)]
    exact (P.colH_step ht c).2 hv
  card t ht := by
    rw [min_eq_left ht.le, min_eq_left (Nat.succ_le_of_lt ht), ← P.card_change ht]
    congr 1
    ext c
    simp only [mem_filter]
    constructor
    · rintro ⟨-, hne⟩
      refine ⟨by_contra fun hc => hne ?_, hne⟩
      rw [colH_of_notMem hc ht.le, colH_of_notMem hc ht]
    · rintro ⟨hc, hne⟩
      exact ⟨Ioo_subset_Icc_self (colRange_sub P hc), hne⟩

/-- **The heights of the column path** are those of the weights. -/
theorem toH_h (P : PieriPath n N vec B) {t : ℕ} (ht : t ≤ N) (c : ℤ) : colH (P.mu t) c = (toH P).h t c := by
  show _ = colH (P.mu (min t N)) c
  rw [min_eq_left ht]

/-- **The potential after one more vector letter** grows by `Σ_{c changed} (n − h_t(c))`. -/
theorem phi_succ (Q : HPath n N T (fun _ => true) B) {t : ℕ} (ht : t < N) :
    phi Q (t + 1) = phi Q t + ∑ c ∈ Q.chg t, (n - Q.h t c) := by
  unfold phi HPath.chg
  rw [sum_filter, ← sum_add_distrib]
  refine sum_congr rfl fun c _ => ?_
  have := Q.up t ht rfl c
  split_ifs with hne
  · rw [show Q.h (t + 1) c = Q.h t c + 1 by omega, PathSpan.wt, PathSpan.wt, sum_range_succ]
  · rw [show Q.h (t + 1) c = Q.h t c by omega, add_zero]

/-- **With vector letters only, a column `c ≥ 1` has height at most `t` after `t` letters**, and the columns
`c ≤ 0` stay full. -/
theorem h_le_vec (Q : HPath n N T (fun _ => true) B) : ∀ t ≤ N, ∀ c, (1 ≤ c → Q.h t c ≤ t) ∧ (c ≤ 0 → Q.h t c = n) := by
  intro t
  induction t with
  | zero =>
    intro _ c
    rw [Q.zero]
    unfold h0
    constructor <;> intro hc <;> split_ifs <;> omega
  | succ t ih =>
    intro ht c
    have h1 := ih (by omega) c
    have h2 := Q.up t (by omega) rfl c
    have h3 := Q.le (t + 1) ht c
    constructor
    · intro hc; have := h1.1 hc; omega
    · intro hc; have := h1.2 hc; omega

/-- **The potentials of a vector path are at least those of filling the rows in order**:
`φ_t ≥ φ_0 + Σ_{s<t} B_s·(n − s)`. -/
theorem phi_ge (Q : HPath n N T (fun _ => true) B) :
    ∀ t ≤ N, phi Q 0 + ∑ s ∈ range t, B s * (n - s) ≤ phi Q t := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    rw [phi_succ Q (by omega), sum_range_succ]
    have hb : B t * (n - t) ≤ ∑ c ∈ Q.chg t, (n - Q.h t c) := by
      rw [← Q.card t (by omega)]
      rw [← smul_eq_mul, ← sum_const]
      refine sum_le_sum fun c hc => ?_
      have hne : Q.h t c ≠ Q.h (t + 1) c := (mem_filter.1 hc).2
      have hc1 : 1 ≤ c := by
        by_contra h'
        have := (h_le_vec Q t (by omega) c).2 (by omega)
        have := (h_le_vec Q (t + 1) ht c).2 (by omega)
        omega
      have := (h_le_vec Q t (by omega) c).1 hc1
      omega
    have := ih (by omega)
    omega

/-- **The potentials of the row path**: every column changed by the letter `s` has height `s` before it, so
`φ_t = φ_0 + Σ_{s<t} B_s·(n − s)`. -/
theorem phi_eq (R : HPath n N T (fun _ => true) B) (hR : ∀ t < N, ∀ c ∈ R.chg t, R.h t c = t) :
    ∀ t ≤ N, phi R t = phi R 0 + ∑ s ∈ range t, B s * (n - s) := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have e : ∑ c ∈ R.chg t, (n - R.h t c) = B t * (n - t) := by
      rw [sum_congr rfl fun c hc => (show n - R.h t c = n - t by rw [hR t (by omega) c hc]), sum_const,
        smul_eq_mul, ← R.card t (by omega)]
      rfl
    rw [phi_succ R (by omega), sum_range_succ, ih (by omega), e]
    ring

end ColPath

/-! ## Straightening along the row path -/

section Straight

open PathSpan

variable {m : ℕ} {ν : Fin (m + 1) → ℕ}

/-- **The columns changed by the letter `t` of the row path have height `t` before it.** -/
theorem rowH_chg (hν : Antitone ν) :
    ∀ t < m + 1, ∀ c ∈ (toH (FlatDimPf.PR hν)).chg t, (toH (FlatDimPf.PR hν)).h t c = t := by
  intro t ht c hc
  have hne : (toH (FlatDimPf.PR hν)).h t c ≠ (toH (FlatDimPf.PR hν)).h (t + 1) c := (mem_filter.1 hc).2
  have hc1 : 1 ≤ c := by
    by_contra h'
    have h1 := (h_le_vec (toH (FlatDimPf.PR hν)) t ht.le c).2 (by omega)
    have h2 := (h_le_vec (toH (FlatDimPf.PR hν)) (t + 1) ht c).2 (by omega)
    omega
  rw [← toH_h _ ht.le, ← toH_h _ ht] at hne
  rw [← toH_h _ ht.le]
  have e1 := FlatDimPf.colH_muR hν hc1 t
  have e2 := FlatDimPf.colH_muR hν hc1 (t + 1)
  change colH (FlatDimPf.muR ν t) c ≠ colH (FlatDimPf.muR ν (t + 1)) c at hne
  change colH (FlatDimPf.muR ν t) c = t
  rw [e1] at hne ⊢
  rw [e2] at hne
  omega

/-- **The row path is minimal** among the column paths of its word: its potentials are the least possible. -/
theorem not_lt_rowH (hν : Antitone ν)
    (Q : HPath (m + 1) (m + 1) (tOf (FlatDimPf.PR hν)) (fun _ => true) (FlatDimPf.BR ν)) :
    ¬ Q.lt (toH (FlatDimPf.PR hν)) := by
  rintro ⟨t, ht, -, hlt⟩
  have h1 := phi_ge Q t ht
  have h2 := phi_eq (toH (FlatDimPf.PR hν)) (rowH_chg hν) t ht
  have h0 : phi Q 0 = phi (toH (FlatDimPf.PR hν)) 0 := by
    unfold phi
    exact sum_congr rfl fun c _ => by rw [Q.zero, (toH (FlatDimPf.PR hν)).zero]
  omega

/-- **Straightening along the row path**: every `Ψ(P_row, C)` is a `ℤ`-combination of standard ones (no path lies
below the row path). -/
theorem psi_mem_span_std (hν : Antitone ν) (C : ℤ → Finset (Fin (m + 1))) :
    PathSpan.psi (toH (FlatDimPf.PR hν)) C ∈ Submodule.span ℤ
      {f | ∃ C', (toH (FlatDimPf.PR hν)).IsStd C' ∧ f = PathSpan.psi (toH (FlatDimPf.PR hν)) C'} := by
  refine Submodule.span_mono ?_ (straighten (by omega) (sum_lt_tOf _) (toH (FlatDimPf.PR hν)) C)
  rintro f ⟨Q, hQ, C', hC', rfl⟩
  rcases hQ with rfl | hQ
  · exact ⟨C', hC', rfl⟩
  · exact absurd hQ (not_lt_rowH hν Q)

/-- **Standard fillings depend on the weight only through its column heights.** -/
theorem isStdFilling_congr {n : ℕ} {lam lam' : Fin n → ℤ} (h : ∀ c, colH lam c = colH lam' c)
    {I : ℤ → Finset (Fin n)} (hI : IsStdFilling lam I) : IsStdFilling lam' I :=
  ⟨fun c => (hI.1 c).trans (h c), hI.2⟩

/-- **A standard window filling of the row path is a standard filling** of the shape `ν`. -/
theorem std_rowH (hν : Antitone ν) {C : ℤ → Finset (Fin (m + 1))} (hC : (toH (FlatDimPf.PR hν)).IsStd C) :
    IsStdFilling (FlatDimPf.muR ν (m + 1)) (colSet (winFill (tOf (FlatDimPf.PR hν)) C)) :=
  isStdFilling_congr (fun c => by rw [HPath.colH_toPieri _ le_rfl, ← toH_h _ le_rfl]; rfl)
    ((toH (FlatDimPf.PR hν)).isStdFilling_ext hC)

/-- **The heights of the row path** are those of the weights `muR`. -/
theorem rowH_hh (hν : Antitone ν) :
    ∀ t ≤ m + 1, ∀ c, colH (FlatDimPf.muR ν t) c = (toH (FlatDimPf.PR hν)).h t c :=
  fun _ ht c => toH_h (FlatDimPf.PR hν) ht c

/-- **The standard `Ψ` of the row path are the row path polynomials** of `PathBasis`. -/
theorem psi_rowH_std (hν : Antitone ν) {C : ℤ → Finset (Fin (m + 1))} (hC : (toH (FlatDimPf.PR hν)).IsStd C) :
    PathSpan.psi (toH (FlatDimPf.PR hν)) C =
      pathPoly ℤ (FlatDimPf.muR ν) (m + 1) (colSet (winFill (tOf (FlatDimPf.PR hν)) C)) := by
  rw [pathPoly_eq_prod (μ := FlatDimPf.muR ν) (FlatDimPf.PR hν).zero (std_rowH hν hC)
    (fun c hc => Ioo_subset_Icc_self (colRange_sub (FlatDimPf.PR hν) hc))]
  unfold PathSpan.psi
  refine prod_congr rfl fun c hc => ?_
  by_cases h1 : 1 ≤ c
  · rw [show colSet (winFill (tOf (FlatDimPf.PR hν)) C) c = C c by simp [colSet, h1, winFill, hc]]
    rw [colK_eq_colS_pos (rowH_hh hν) h1]
  · have hcard : (C c).card = m + 1 := by
      rw [hC.1 c hc]
      exact (h_le_vec _ (m + 1) le_rfl c).2 (by omega)
    have hCu : C c = univ := eq_univ_of_card _ (by simpa using hcard)
    rw [show colSet (winFill (tOf (FlatDimPf.PR hν)) C) c = univᶜ by simp [colSet, h1, winFill, hc, hCu], hCu,
      colK_compl (rowH_hh hν) (by omega) univ, hsg_mul_self, one_mul]

end Straight

/-! ## Bideterminants along the row path -/

section Bidet

open PathSpan

variable {m : ℕ} {ν : Fin (m + 1) → ℕ}

/-- **The heights of the row path outside `[1, ν_0]`**: `m + 1` at `c ≤ 0`, `0` beyond `ν_0`. -/
theorem colH_rowR_out (hν : Antitone ν) {c : ℤ} (hc : c ≤ 0 ∨ (ν 0 : ℤ) < c) (t : ℕ) :
    colH (FlatDimPf.muR ν t) c = if c ≤ 0 then m + 1 else 0 := by
  unfold colH
  split_ifs with h
  · rw [filter_true_of_mem fun a _ => ?_, card_univ, Fintype.card_fin]
    simp only [FlatDimPf.muR]
    split_ifs <;> omega
  · rw [filter_false_of_mem fun a _ => ?_, card_empty]
    have : ν a ≤ ν 0 := hν (Fin.zero_le _)
    simp only [FlatDimPf.muR]
    split_ifs <;> omega

/-- **The columns of the row path outside `[1, ν_0]` never move**: their states stay `[J = ∅]`. -/
theorem colK_rowR_out (R : Type*) [CommRing R] (hν : Antitone ν) {c : ℤ} (hc : c ≤ 0 ∨ (ν 0 : ℤ) < c) :
    colK R (FlatDimPf.muR ν) c (m + 1) = st0 :=
  colK_of_const fun t _ => by rw [colH_rowR_out hν hc, colH_rowR_out hν hc]

/-- **The filling of the row path by column sets** `G` on `[1, ν_0]`: full before, empty after. -/
def fill (ν : Fin (m + 1) → ℕ) (G : ℤ → Finset (Fin (m + 1))) (c : ℤ) : Finset (Fin (m + 1)) :=
  if c ≤ 0 then univ else if c ≤ ν 0 then G c else ∅

/-- **The columns `1, …, ν_0` lie in the column range of the row path.** -/
theorem Icc_sub_colRange (hν : Antitone ν) : Icc (1 : ℤ) (ν 0) ⊆ colRange (FlatDimPf.PR hν).mu (m + 1) := by
  intro c hc
  have h := abs_le_colRange (FlatDimPf.PR hν).mu (le_refl (m + 1)) 0
  change |FlatDimPf.muR ν (m + 1) 0| ≤ _ at h
  rw [muR_last_apply, abs_of_nonneg (Nat.cast_nonneg _)] at h
  rw [mem_Icc] at hc
  simp only [colRange, mem_Icc]
  constructor <;> omega

/-- **The columns `1, …, ν_0` lie in the window of the row path.** -/
theorem Icc_sub_win (hν : Antitone ν) : Icc (1 : ℤ) (ν 0) ⊆ win (tOf (FlatDimPf.PR hν)) :=
  fun _ hc => Ioo_subset_Icc_self (colRange_sub _ (Icc_sub_colRange hν hc))

/-- **`Ψ` of the row path at a filling by column sets** is the product over `1 ≤ c ≤ ν_0` of the wedges
`y_0 ∧ ⋯ ∧ y_{h_c − 1}` at the sets `G(c)`. -/
theorem psi_fill (hν : Antitone ν) (G : ℤ → Finset (Fin (m + 1))) :
    PathSpan.psi (toH (FlatDimPf.PR hν)) (fill ν G) =
      ∏ c ∈ Icc (1 : ℤ) (ν 0), wst (fun t a => X (t, a)) (colH (FlatDimPf.muR ν (m + 1)) c) (G c) := by
  unfold PathSpan.psi
  symm
  refine prod_subset_one_on_sdiff (Icc_sub_win hν) (fun c hc => ?_) (fun c hc => ?_)
  · obtain ⟨-, hc⟩ := mem_sdiff.1 hc
    rw [mem_Icc, not_and_or, not_le, not_le] at hc
    by_cases hc0 : c ≤ 0
    · have h := colK_compl (rowH_hh hν) hc0 univ
      rw [hsg_mul_self, one_mul, colK_rowR_out ℤ hν (Or.inl hc0)] at h
      rw [show fill ν G c = univ by simp [fill, hc0], ← h]
      simp [st0]
    · have hc1 : (ν 0 : ℤ) < c := by omega
      rw [← colK_eq_colS_pos (rowH_hh hν) (by omega), colK_rowR_out ℤ hν (Or.inr hc1),
        show fill ν G c = ∅ by simp [fill, hc0, show ¬ c ≤ (ν 0 : ℤ) by omega]]
      simp [st0]
  · have hc' := mem_Icc.1 hc
    rw [← colK_eq_colS_pos (rowH_hh hν) hc'.1, colK_muR ℤ hν hc'.1,
      show fill ν G c = G c by simp [fill, show ¬ c ≤ 0 by omega, hc'.2]]

/-- **The letter bideterminant** of shape `ν`: `∏_s ∏_c det [y_j(rows_{s,c}(i))]_{i,j≤s}`, the letter `j` read as
the column `j` (one block of `WeylFock.bidet`, before the block embedding `FlatDimPf.emb`). -/
def lbidet (R : Type*) [CommRing R] (ν : Fin (m + 1) → ℕ)
    (rows : (s : Fin (m + 1)) → Fin (mult ν s) → Fin (s + 1) → Fin (m + 1)) : MvPolynomial (ℕ × Fin (m + 1)) R :=
  ∏ s : Fin (m + 1), ∏ c : Fin (mult ν s),
    (Matrix.of fun i j : Fin (s + 1) => (X (j.val, rows s c i) : MvPolynomial (ℕ × Fin (m + 1)) R)).det

/-- **The standard row path polynomials** of the shape `ν`. -/
def stdSet (R : Type*) [CommRing R] (ν : Fin (m + 1) → ℕ) : Set (MvPolynomial (ℕ × Fin (m + 1)) R) :=
  {f | ∃ I, IsStdFilling (FlatDimPf.muR ν (m + 1)) I ∧ f = pathPoly R (FlatDimPf.muR ν) (m + 1) I}

/-- **Letter bideterminants straighten** into the standard row path polynomials (over `ℤ`): a letter bideterminant is
`±Ψ(P_row, C)` or `0` (`det_eq_smul_wst`, `psi_fill`, `prod_cols`), and `Ψ(P_row, C)` straightens
(`psi_mem_span_std`, `psi_rowH_std`). -/
theorem lbidet_mem (hν : Antitone ν) (rows : (s : Fin (m + 1)) → Fin (mult ν s) → Fin (s + 1) → Fin (m + 1)) :
    lbidet ℤ ν rows ∈ Submodule.span ℤ (stdSet ℤ ν) := by
  classical
  choose ε hε using fun s c => det_eq_smul_wst (fun t a => (X (t, a) : MvPolynomial (ℕ × Fin (m + 1)) ℤ)) (rows s c)
  have hε' : ∀ (s : Fin (m + 1)) (c : Fin (mult ν s)),
      (Matrix.of fun i j : Fin (s + 1) => (X (j.val, rows s c i) : MvPolynomial (ℕ × Fin (m + 1)) ℤ)).det =
      (ε s c : MvPolynomial (ℕ × Fin (m + 1)) ℤ) * wst (fun t a => X (t, a)) (s + 1) (univ.image (rows s c)) := hε
  set G : ℤ → Finset (Fin (m + 1)) := fun c =>
    if h : ∃ x, colOf ν x = c then univ.image (rows h.choose.1 h.choose.2) else ∅ with hGdef
  have hG : ∀ x, G (colOf ν x) = univ.image (rows x.1 x.2) := fun x => by
    have h : ∃ y, colOf ν y = colOf ν x := ⟨x, rfl⟩
    rw [hGdef]
    dsimp only
    rw [dite_eq_left h, colOf_injective hν h.choose_spec]
  have e : lbidet ℤ ν rows = ((∏ s, ∏ c, ε s c : ℤ) : MvPolynomial (ℕ × Fin (m + 1)) ℤ) *
      PathSpan.psi (toH (FlatDimPf.PR hν)) (fill ν G) := by
    rw [psi_fill hν, prod_cols hν, lbidet, Int.cast_prod, ← prod_mul_distrib]
    refine prod_congr rfl fun s _ => ?_
    rw [Int.cast_prod, ← prod_mul_distrib]
    refine prod_congr rfl fun c _ => ?_
    rw [hε' s c, hG ⟨s, c⟩, colH_colOf hν ⟨s, c⟩]
  rw [e, ← zsmul_eq_mul]
  refine Submodule.smul_mem _ _ (Submodule.span_le.2 ?_ (psi_mem_span_std hν _))
  rintro _ ⟨C', hC', rfl⟩
  exact Submodule.subset_span ⟨_, std_rowH hν hC', psi_rowH_std hν hC'⟩

end Bidet

/-! ## All blocks: `∇` is spanned by the standard row path polynomials -/

section Blocks

variable {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {m : ℕ} {K : Type*} [Field K]

/-- **The standard fillings of a shape are finite in number.** -/
theorem finite_std {ν : Fin (m + 1) → ℕ} (hν : Antitone ν) :
    Finite {I // IsStdFilling (FlatDimPf.muR ν (m + 1)) I} := by
  rw [FlatDimPf.muR_last]
  exact (card_stdFilling fun i j h => by exact_mod_cast hν h).1

/-- **The number of standard fillings of a shape** is its Weyl dimension. -/
theorem card_std {ν : Fin (m + 1) → ℕ} (hν : Antitone ν) :
    Nat.card {I // IsStdFilling (FlatDimPf.muR ν (m + 1)) I} = WeylCount.dimW (m + 1) fun a => (ν a : ℤ) := by
  rw [FlatDimPf.muR_last]
  exact (card_stdFilling fun i j h => by exact_mod_cast hν h).2

omit [Fintype Φ] [DecidableEq Φ] in
/-- **A minor of a block is the block embedding of a letter minor**, defined over `ℤ`. -/
theorem minor_eq_emb (τ : Φ) (s : Fin (m + 1)) (I : Fin (s + 1) → Fin (m + 1)) :
    minor (L := K) τ s I = FlatDimPf.emb τ (MvPolynomial.map (Int.castRingHom K)
      (Matrix.of fun i j : Fin (s + 1) => (X (j.val, I i) : MvPolynomial (ℕ × Fin (m + 1)) ℤ)).det) := by
  rw [← RingHom.comp_apply, RingHom.map_det, minor]
  congr 1
  refine Matrix.ext fun i j => ?_
  have hj : (j : ℕ) ≤ m := by have := j.isLt; have := s.isLt; omega
  simp [FlatDimPf.emb, xMat, hj, Fin.castLE]

omit [DecidableEq Φ] in
/-- **A bideterminant is the product of the block embeddings of letter bideterminants.** -/
theorem bidet_eq_prod_emb (ν : Φ → Fin (m + 1) → ℕ)
    (rows : (τ : Φ) → (s : Fin (m + 1)) → Fin (mult (ν τ) s) → Fin (s + 1) → Fin (m + 1)) :
    bidet K ν rows = ∏ τ, FlatDimPf.emb τ (MvPolynomial.map (Int.castRingHom K) (lbidet ℤ (ν τ) (rows τ))) := by
  unfold bidet lbidet
  refine prod_congr rfl fun τ _ => ?_
  rw [map_prod, map_prod]
  refine prod_congr rfl fun s _ => ?_
  rw [map_prod, map_prod]
  exact prod_congr rfl fun c _ => minor_eq_emb τ s (rows τ s c)

/-- **The block products of standard row path polynomials** (`FlatDimPf.prod_mem_nabla`, independent by
`FlatDimPf.blocks_indep`). -/
def stdProd (ν : Φ → Fin (m + 1) → ℕ) (f : ∀ b, {I // IsStdFilling (FlatDimPf.muR (ν b) (m + 1)) I}) :
    Pol Φ (m + 1) K :=
  ∏ b, FlatDimPf.emb b (pathPoly K (FlatDimPf.muR (ν b)) (m + 1) (f b).1)

/-- **`∇` is spanned by the block products of standard row path polynomials** (the straightening of the
bideterminants, `lbidet_mem`, which span by `WeylFock.span_bidet`). -/
theorem nabla_le_span [CharZero K] {ν : Φ → Fin (m + 1) → ℕ} (hν : ∀ b, Antitone (ν b)) :
    nabla K ν ≤ Submodule.span K (Set.range (stdProd (K := K) ν)) := by
  classical
  have := fun b => finite_std (hν b)
  let _ : ∀ b, Fintype {I // IsStdFilling (FlatDimPf.muR (ν b) (m + 1)) I} := fun b => Fintype.ofFinite _
  rw [← span_bidet hν, Submodule.span_le]
  rintro _ ⟨rows, rfl⟩
  rw [bidet_eq_prod_emb]
  refine FlatDimPf.prod_mem_span_pi (fun b (I : {I // IsStdFilling (FlatDimPf.muR (ν b) (m + 1)) I}) =>
    FlatDimPf.emb (K := K) b (pathPoly K (FlatDimPf.muR (ν b)) (m + 1) I.1)) _ fun b => ?_
  set f : MvPolynomial (ℕ × Fin (m + 1)) ℤ →+* Pol Φ (m + 1) K :=
    (FlatDimPf.emb b).comp (MvPolynomial.map (Int.castRingHom K)) with hf
  have h2 : f (lbidet ℤ (ν b) (rows b)) ∈ Submodule.span ℤ (f '' stdSet ℤ (ν b)) := by
    have h := Submodule.mem_map_of_mem (f := f.toAddMonoidHom.toIntLinearMap) (lbidet_mem (hν b) (rows b))
    rw [Submodule.map_span] at h
    exact h
  refine Submodule.span_le_restrictScalars ℤ K _ (Submodule.span_mono ?_ h2)
  rintro _ ⟨g, ⟨I, hI, rfl⟩, rfl⟩
  exact ⟨⟨I, hI⟩, by simp [hf, pathPoly_map]⟩

/-- **The block products of standard row path polynomials are independent** over every field
(`FlatDimPf.blocks_indep`, `FlatDimPf.emb_row_indep`). -/
theorem stdProd_linearIndependent {ν : Φ → Fin (m + 1) → ℕ} (hν : ∀ b, Antitone (ν b)) :
    LinearIndependent K (stdProd (K := K) ν) := by
  classical
  have := fun b => finite_std (hν b)
  let _ : ∀ b, Fintype {I // IsStdFilling (FlatDimPf.muR (ν b) (m + 1)) I} := fun b => Fintype.ofFinite _
  exact FlatDimPf.blocks_indep (fun b (I : {I // IsStdFilling (FlatDimPf.muR (ν b) (m + 1)) I}) =>
    FlatDimPf.emb (K := K) b (pathPoly K (FlatDimPf.muR (ν b)) (m + 1) I.1))
    (fun b => FlatDimPf.emb_row_indep b (hν b)) fun b _ => FlatDimPf.emb_supported b _

/-- **`∇` is the span of the block products of standard row path polynomials** (they lie in `∇`,
`FlatDimPf.prod_mem_nabla`, and span it, `nabla_le_span`). -/
theorem nabla_eq_span [CharZero K] {ν : Φ → Fin (m + 1) → ℕ} (hν : ∀ b, Antitone (ν b)) :
    nabla K ν = Submodule.span K (Set.range (stdProd (K := K) ν)) :=
  le_antisymm (nabla_le_span hν) (Submodule.span_le.2 (by
    rintro _ ⟨f, rfl⟩
    exact FlatDimPf.prod_mem_nabla hν fun b => (f b).1))

/-- **The Weyl dimension formula for `∇`, block by block**: `dim ∇(ν) = ∏_b dimW(ν_b)`; the block products of the
standard row path polynomials are a basis. -/
theorem finrank_nabla [CharZero K] {ν : Φ → Fin (m + 1) → ℕ} (hν : ∀ b, Antitone (ν b)) :
    Module.finrank K (nabla K ν) = ∏ b, WeylCount.dimW (m + 1) fun a => (ν b a : ℤ) := by
  classical
  have := fun b => finite_std (hν b)
  let _ : ∀ b, Fintype {I // IsStdFilling (FlatDimPf.muR (ν b) (m + 1)) I} := fun b => Fintype.ofFinite _
  rw [nabla_eq_span hν, finrank_span_eq_card (stdProd_linearIndependent hν), Fintype.card_pi]
  refine prod_congr rfl fun b _ => ?_
  rw [Fintype.card_eq_nat_card, card_std (hν b)]

end Blocks

/-! ## The Weyl dimension formula -/

section WeylDim

open InertModel LocalLattice

/-- **`dimW` of the block shape** of a weight: `natW` of `λ_s` or of its dual `−λ_s ∘ rev` has the Weyl dimension of
`λ_s` (`WeylCount.dimW_add_const`, `WeylCount.dimW_dual`). -/
theorem dimW_nu1 {n' m : ℕ} {lam0 : Fin n' → Fin (m + 1) → ℤ} (hlam : ∀ s, Antitone (lam0 s)) (s : Fin n') :
    WeylCount.dimW (m + 1) (fun a => (nu1 lam0 ((), s) a : ℤ)) = WeylCount.dimW (m + 1) (lam0 s) := by
  have ha : Antitone (lamAt lam0 s) := antitone_blockWt (fun _ => hlam) ((), s)
  have e : (fun a => (nu1 lam0 ((), s) a : ℤ)) = fun a => lamAt lam0 s a + -detShift (lamAt lam0 s) :=
    funext fun a => by
      have := natW_add_detShift ha a
      simp only [nu1, wt1, blockWt] at this ⊢
      omega
  rw [e, WeylCount.dimW_add_const ha]
  unfold lamAt
  split_ifs
  · rfl
  · exact WeylCount.dimW_dual (hlam s)

/-- **The Weyl dimension formula** (`FirstCloud.WeylDim`, Annex I's I8): for a dominant weight `λ` on one orbit,
`dim V(λ) = ∏_s dimW_k(λ_s)`. The block products of the standard row path polynomials lie in `∇`
(`FlatDimPf.prod_mem_nabla`), are independent (`FlatDimPf.blocks_indep`) and span (`nabla_le_span`: the
bideterminants straighten along the row path, the least path of its word); they number `∏_s dimW` (`card_std`). -/
theorem weylDim (Kf : Type) [Field Kf] [CharZero Kf] {n' k : ℕ} (hk : 1 ≤ k) : FirstCloud.WeylDim Kf n' k := by
  intro lam0 hlam
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hb : ∀ b, Antitone (nu1 lam0 b) := fun b => HermForms.natW_antitone (antitone_blockWt (fun _ => hlam) b)
  show Module.finrank Kf (nabla Kf (nu1 lam0)) = _
  rw [finrank_nabla hb, Fintype.prod_prod_type, Fintype.prod_unique]
  exact prod_congr rfl fun s _ => dimW_nu1 hlam s

end WeylDim

end

end WeylDimPf
