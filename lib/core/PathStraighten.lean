import PathSpan

/-!
# The path basis (T2 (i), (iii)): the Garnir relations, straightening and the basis

The assembly of the straightening machinery of `PathSpan` into the path basis theorem T2: over every commutative ring
the path polynomials `Ψ(P, I)` of `PathBasis` (a Pieri path and a standard filling of its end weight) form a basis of
the polynomials of multidegree `B`.

**Main results.**
* *The Garnir relations of every path* (`garnir_all`): every Garnir sum `gar_{h_j}(S_j, S_{j+1})(X, Y)`, `|X| > h_j`,
  of a column path lies in its lower part. By induction on the letters (`garnir_step`): the four state lemmas of
  `PathSpan`, applied to abstract states (`gs_wl`, `gs_wr`, `gs_wb`, `gs_cl`, `gs_cr`, `gs_cb`), reduce a Garnir sum
  of the path to `X_{N,a}` times Garnir sums of the truncation, except for one special term when a single column is
  stepped and nothing else is left to shuffle (the step moved to the other column: `special_vec`, `special_cov`);
  when both columns are stepped the special terms add up to `y ∧ y ∧ S = 0` or `y ⌟ y ⌟ T = 0`.
* *The straightening law* (`straighten`): every `Ψ(P, C)` lies in the `ℤ`-span of the standard `Ψ(Q, I)` with `Q = P`
  or `Q ≺ P` in the lexicographic order of the potentials (`HPath.lt`). At a violation
  `#col(c + 1)_{<t} > #col(c)_{<t}` the exchange relation `HPath.exch_mem` with `D = col(c + 1)_{<t} ∖ col(c)`
  rewrites `Ψ(P, C)` as a combination of fillings whose column `c + 1` is larger in the colexicographic order
  (`enc_lt_exch`: the exchanged part must reach beyond `t`), so the measure `Σ_c enc(col(c)ᶜ)·(2^n)^{c + T}` drops
  (`smeas_lt`), modulo the lower part (`HPath.psi_mem_of_std`).
* *Spanning* (`monomial_mem_allSpan`): every monomial of multidegree `B` is a `ℤ`-combination of path polynomials,
  splitting off the monomial of the last letter (`exists_monomial_eq_prod`) and extending the paths by the first-row
  strip (`mono_mul_allSpan`, as in `mono_mul_lower`).
* *Column paths are Pieri paths* (`HPath.toPieri`): the weights `μ_a = −T + #{c ∈ (−T, T] : a < h(c)}` (`wOf`) have
  the column heights `h` (`colH_wOf`), and heights growing by at most one give horizontal strips (`isStrip_wOf`). The
  columns `c ≥ 1` of `colK` and `colS` agree (`colK_eq_colS_pos`); the columns `c ≤ 0` are Hodge duals,
  `K_c(Jᶜ) = σ(J)·σ(univ)·S_c(J)` with `σ(J) = (−1)^{Σ_{x ∈ J} (n − 1 − x)}` (`colK_compl`, from
  `y ⌟ ⋆K = ⋆(y ∧ K)` and `y ∧ ⋆K = ⋆(y ⌟ K)`: `contr_hodge`, `wedge_hodge`). So a standard `Ψ(P, C)` is `±` a member
  of the path family (`HPath.psi_mem_span`), and the family spans the multidegree-`B` polynomials over every
  commutative ring (`mem_span_pathFam`, through `ℤ → R` and `pathPoly_map`).
* *The count* (`card_monomials`): the monomials of multidegree `B` in `m + 1` coordinates number
  `∏_{t < N} C(B_t + m, m)` (stars and bars, `Sym.equivNatSumOfFintype`), as many as the family members
  (`card_pathIdx`).
* *The basis* (`PathBasis.pathFam_basis`, `PathBasis.pathFam_basis_apply`): a spanning family of a free module with as
  many members as the rank is a basis over every commutative ring (`OrzechProperty`: a surjective linear map into a
  finite module with an injective one from the same source is injective; `pathVec_linearIndependent`).
-/

namespace PathSpan

open MvPolynomial Finset TwistedDegree PathBasis

noncomputable section

/-! ## One more letter in a Garnir sum, for abstract states -/

section GarStep

variable {n : ℕ} {p q : ℕ} {y : Fin n → MvPolynomial (ℕ × Fin n) ℤ} {S T : Finset (Fin n) → MvPolynomial (ℕ × Fin n) ℤ}
  {K m : MvPolynomial (ℕ × Fin n) ℤ} {L : Submodule ℤ (MvPolynomial (ℕ × Fin n) ℤ)}

/-- **Wedging the left state** (a vector letter stepping the column `j` only): the Garnir sums of `y ∧ S` and `T`
are combinations of `y_u` times Garnir sums of `S` and `T` with something to shuffle. -/
theorem gs_wl (H : ∀ X' Y' : Finset (Fin n), p < X'.card → X'.card + Y'.card = p + q → ∀ a,
      m * (y a * (gar p S T X' Y' * K)) ∈ L)
    {X Y : Finset (Fin n)} (hX : p + 1 < X.card) (hXY : X.card + Y.card = p + 1 + q) :
    m * (gar (p + 1) (wedge y S) T X Y * K) ∈ L := by
  rw [gar_wedge_left, sum_mul, mul_sum]
  refine sum_mem fun u hu => ?_
  have h1 : (X.erase u).card = X.card - 1 := card_erase_of_mem hu
  have := sign_mul_mem (H (X.erase u) Y (by omega) (by omega) u) (p + (X.filter (· < u)).card)
  convert this using 1
  ring

/-- **Wedging the right state** (a vector letter stepping the column `j + 1` only): up to Garnir sums with something
to shuffle, the Garnir sum of `S` and `y ∧ T` is, when `|X| = p + 1`, the special term `±(y ∧ S)(X)·T(Y)`. -/
theorem gs_wr (hT : IsDeg T q)
    (H : ∀ X' Y' : Finset (Fin n), p < X'.card → X'.card + Y'.card = p + q → ∀ a, y a * (gar p S T X' Y' * K) ∈ L)
    {X Y : Finset (Fin n)} (hX : p < X.card) (hXY : X.card + Y.card = p + q + 1) :
    gar p S (wedge y T) X Y * K - (if X.card = p + 1 then (-1) ^ Y.card * (wedge y S X * T Y * K) else 0) ∈ L := by
  rw [gar_wedge_right p y S hT hXY, add_mul, sum_mul, sum_mul]
  have h1 : ∑ v ∈ Y, sg v Y * y v * gar p S T X (Y.erase v) * K ∈ L := sum_mem fun v hv => by
    have hc : (Y.erase v).card = Y.card - 1 := card_erase_of_mem hv
    have hY : 0 < Y.card := card_pos.2 ⟨v, hv⟩
    have := sign_mul_mem (H X (Y.erase v) hX (by omega) v) ((Y.filter (v < ·)).card)
    convert this using 1
    rw [sg]
    ring
  split_ifs with hc
  · have e : ∑ v ∈ X, (-1) ^ (Y.card + (X.filter (v < ·)).card) * y v * gar p S T (X.erase v) Y * K =
        (-1) ^ Y.card * (wedge y S X * T Y * K) := by
      rw [wedge, sum_mul, sum_mul, mul_sum]
      refine sum_congr rfl fun v hv => ?_
      rw [gar_self p S T (by rw [card_erase_of_mem hv]; omega), sg, pow_add]
      ring
    rw [e, add_sub_cancel_right]
    exact h1
  · rw [sub_zero]
    refine add_mem h1 (sum_mem fun v hv => ?_)
    have hc' : (X.erase v).card = X.card - 1 := card_erase_of_mem hv
    have := sign_mul_mem (H (X.erase v) Y (by omega) (by omega) v) (Y.card + (X.filter (v < ·)).card)
    convert this using 1
    ring

/-- **Wedging both states** (a vector letter stepping both columns): the special terms add up to
`±(y ∧ y ∧ S)(X)·T(Y) = 0`. -/
theorem gs_wb (hT : IsDeg T q)
    (H : ∀ X' Y' : Finset (Fin n), p < X'.card → X'.card + Y'.card = p + q → ∀ a b,
      y a * (y b * (gar p S T X' Y' * K)) ∈ L)
    {X Y : Finset (Fin n)} (hX : p + 1 < X.card) (hXY : X.card + Y.card = p + 1 + q + 1) :
    gar (p + 1) (wedge y S) (wedge y T) X Y * K ∈ L := by
  rw [gar_wedge_right (p + 1) y (wedge y S) hT hXY, add_mul, sum_mul, sum_mul]
  refine add_mem (sum_mem fun v hv => ?_) ?_
  · have hc : (Y.erase v).card = Y.card - 1 := card_erase_of_mem hv
    have hY : 0 < Y.card := card_pos.2 ⟨v, hv⟩
    have := sign_mul_mem (gs_wl (m := y v) (fun X' Y' h1 h2 a => H X' Y' h1 h2 v a) (Y := Y.erase v) hX (by omega))
      ((Y.filter (v < ·)).card)
    convert this using 1
    rw [sg]
    ring
  · by_cases hc : X.card = p + 2
    · have hw : ∑ v ∈ X, sg v X * y v * wedge y S (X.erase v) = 0 := wedge_wedge_self y S X
      have e : ∑ v ∈ X, (-1) ^ (Y.card + (X.filter (v < ·)).card) * y v * gar (p + 1) (wedge y S) T (X.erase v) Y *
          K = (-1) ^ Y.card * T Y * K * ∑ v ∈ X, sg v X * y v * wedge y S (X.erase v) := by
        rw [mul_sum]
        refine sum_congr rfl fun v hv => ?_
        rw [gar_self (p + 1) (wedge y S) T (by rw [card_erase_of_mem hv]; omega), sg, pow_add]
        ring
      rw [e, hw, mul_zero]
      exact zero_mem _
    · refine sum_mem fun v hv => ?_
      have hc' : (X.erase v).card = X.card - 1 := card_erase_of_mem hv
      have := sign_mul_mem (gs_wl (m := y v) (fun X' Y' h1 h2 a => H X' Y' h1 h2 v a) (X := X.erase v) (Y := Y)
        (by omega) (by omega)) (Y.card + (X.filter (v < ·)).card)
      convert this using 1
      ring

/-- **Contracting the right state** (a covector letter stepping the column `j + 1` only): no special term. -/
theorem gs_cr (hT : IsDeg T (q + 1))
    (H : ∀ X' Y' : Finset (Fin n), p < X'.card → X'.card + Y'.card = p + (q + 1) → ∀ a,
      m * (y a * (gar p S T X' Y' * K)) ∈ L)
    {X Y : Finset (Fin n)} (hX : p < X.card) (hXY : X.card + Y.card = p + q) :
    m * (gar p S (contr y T) X Y * K) ∈ L := by
  rw [gar_contr_right p y S hT hXY, sum_mul, mul_sum]
  refine sum_mem fun a ha => ?_
  have haY : a ∉ Y := mem_compl.1 ha
  have := sign_mul_mem (H X (insert a Y) hX (by rw [card_insert_of_notMem haY]; omega) a) ((Y.filter (a < ·)).card)
  convert this using 1
  rw [sg]
  ring

/-- **Contracting the left state** (a covector letter stepping the column `j` only): up to Garnir sums with something
to shuffle, the Garnir sum of `y ⌟ S` and `T` is, when `|X| = p + 1`, minus the special term `±S(X)·(y ⌟ T)(Y)`. -/
theorem gs_cl (hT : IsDeg T q)
    (H : ∀ X' Y' : Finset (Fin n), p + 1 < X'.card → X'.card + Y'.card = p + 1 + q → ∀ a,
      m * (y a * (gar (p + 1) S T X' Y' * K)) ∈ L)
    {X Y : Finset (Fin n)} (hX : p < X.card) (hXY : X.card + Y.card = p + q) :
    m * (gar p (contr y S) T X Y * K) +
      (if X.card = p + 1 then (-1) ^ (p + X.card + Y.card) * (m * (S X * contr y T Y * K)) else 0) ∈ L := by
  rw [gar_contr_left p y S hT hXY, sub_mul, sum_mul, sum_mul, mul_sub, mul_sum, mul_sum]
  have h1 : ∑ a ∈ Xᶜ, m * ((-1) ^ (p + (X.filter (· < a)).card) * y a * gar (p + 1) S T (insert a X) Y * K) ∈ L :=
    sum_mem fun a ha => by
      have haX : a ∉ X := mem_compl.1 ha
      have := sign_mul_mem (H (insert a X) Y (by rw [card_insert_of_notMem haX]; omega)
        (by rw [card_insert_of_notMem haX]; omega) a) (p + (X.filter (· < a)).card)
      convert this using 1
      ring
  split_ifs with hc
  · have e : ∑ a ∈ Yᶜ, m * ((-1) ^ (p + X.card + (Y.filter (· < a)).card) * y a * gar (p + 1) S T X (insert a Y) *
        K) = (-1) ^ (p + X.card + Y.card) * (m * (S X * contr y T Y * K)) := by
      simp only [contr, mul_sum, sum_mul]
      refine sum_congr rfl fun a ha => ?_
      rw [gar_self (p + 1) S T hc]
      have := card_lt_add_card_gt (mem_compl.1 ha)
      have hs : ((-1 : MvPolynomial (ℕ × Fin n) ℤ) ^ (p + X.card + (Y.filter (· < a)).card)) =
          (-1) ^ (p + X.card + Y.card) * sg a Y := by
        rw [sg, ← pow_add]
        exact neg_one_pow_congr (by omega)
      rw [hs]
      ring
    rw [e, sub_add_cancel]
    exact h1
  · rw [add_zero]
    refine sub_mem h1 (sum_mem fun a ha => ?_)
    have haY : a ∉ Y := mem_compl.1 ha
    have := sign_mul_mem (H X (insert a Y) (by omega) (by rw [card_insert_of_notMem haY]; omega) a)
      (p + X.card + (Y.filter (· < a)).card)
    convert this using 1
    ring

/-- **Contracting both states** (a covector letter stepping both columns): the special terms add up to
`±S(X)·(y ⌟ y ⌟ T)(Y) = 0`. -/
theorem gs_cb (hT : IsDeg T (q + 1))
    (H : ∀ X' Y' : Finset (Fin n), p + 1 < X'.card → X'.card + Y'.card = p + 1 + (q + 1) → ∀ a b,
      y a * (y b * (gar (p + 1) S T X' Y' * K)) ∈ L)
    {X Y : Finset (Fin n)} (hX : p < X.card) (hXY : X.card + Y.card = p + q) :
    gar p (contr y S) (contr y T) X Y * K ∈ L := by
  rw [gar_contr_right p y (contr y S) hT hXY, sum_mul]
  have hC : ∀ a ∈ Yᶜ, y a * (gar p (contr y S) T X (insert a Y) * K) +
      (if X.card = p + 1 then (-1) ^ (p + X.card + (insert a Y).card) * (y a * (S X * contr y T (insert a Y) * K))
        else 0) ∈ L := fun a ha =>
    gs_cl (m := y a) hT (fun X' Y' h1 h2 b => H X' Y' h1 h2 a b) hX
      (by rw [card_insert_of_notMem (mem_compl.1 ha)]; omega)
  by_cases hc : X.card = p + 1
  · simp only [hc, ↓reduceIte] at hC
    have h0 : ∑ a ∈ Yᶜ, sg a Y * y a * contr y T (insert a Y) = 0 := contr_contr_self y T Y
    have hz : ∑ a ∈ Yᶜ, sg a Y * ((-1) ^ (p + (p + 1) + (insert a Y).card) *
        (y a * (S X * contr y T (insert a Y) * K))) = 0 := by
      calc _ = ∑ a ∈ Yᶜ, (-1) ^ (p + (p + 1) + (Y.card + 1)) * S X * K * (sg a Y * y a * contr y T (insert a Y)) :=
            sum_congr rfl fun a ha => by rw [card_insert_of_notMem (mem_compl.1 ha)]; ring
        _ = 0 := by rw [← mul_sum, h0, mul_zero]
    have e : ∑ a ∈ Yᶜ, sg a Y * y a * gar p (contr y S) T X (insert a Y) * K =
        ∑ a ∈ Yᶜ, sg a Y * (y a * (gar p (contr y S) T X (insert a Y) * K) + (-1) ^ (p + (p + 1) + (insert a Y).card) *
          (y a * (S X * contr y T (insert a Y) * K))) -
        ∑ a ∈ Yᶜ, sg a Y * ((-1) ^ (p + (p + 1) + (insert a Y).card) *
          (y a * (S X * contr y T (insert a Y) * K))) := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun a _ => by ring
    rw [e, hz, sub_zero]
    refine sum_mem fun a ha => ?_
    exact sign_mul_mem (hC a ha) ((Y.filter (a < ·)).card)
  · simp only [hc, ↓reduceIte, add_zero] at hC
    refine sum_mem fun a ha => ?_
    have := sign_mul_mem (hC a ha) ((Y.filter (a < ·)).card)
    convert this using 1
    rw [sg]
    ring

end GarStep


/-! ## The Garnir relations of all paths, by induction on the letters -/

section Garnir

variable {n N T : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **The Garnir relations propagate along one more letter**: if the truncation satisfies them, so does the path.
The four state lemmas reduce a Garnir sum of the path to `X_{N,a}` times Garnir sums of the truncation (in the lower
part by `stepProd_mem` and `mono_mul_lower`), except for one special term when a single column is stepped and nothing
else is left to shuffle: the step moved to the other column (`special_vec`, `special_cov`); when both columns are
stepped the special terms cancel (`wedge_wedge_self`, `contr_contr_self`). -/
theorem garnir_step (hn : 0 < n) (P : HPath n (N + 1) T vec B) (hT : ∑ s ∈ range (N + 1), B s < T)
    (hR : GarStmt P.trunc) : GarStmt P := by
  intro j hj X Y C hX hXY
  set D := P.chg N with hDdef
  set D2 := (D.erase (j + 1)).erase j with hD2def
  have hjw : j ∈ win T := by rw [mem_Ico] at hj; exact mem_Icc.2 ⟨by omega, by omega⟩
  have hj1w : j + 1 ∈ win T := by rw [mem_Ico] at hj; exact mem_Icc.2 ⟨by omega, by omega⟩
  have hD2w : D2 ⊆ win2 T j := fun c hc => by
    simp only [hD2def, mem_erase] at hc
    simp only [win2, mem_erase]
    exact ⟨hc.1, hc.2.1, Ioo_subset_Icc_self (P.chg_sub hc.2.2)⟩
  have hcardD : D.card = B N := P.card N (by omega)
  have hD2c : D2.card + (if j ∈ D then 1 else 0) + (if j + 1 ∈ D then 1 else 0) = B N := by
    have hjne : j ≠ j + 1 := by omega
    rw [← hcardD, hD2def]
    by_cases h1 : j + 1 ∈ D <;> by_cases h2 : j ∈ D
    · rw [card_erase_of_mem (mem_erase.2 ⟨hjne, h2⟩), card_erase_of_mem h1, ite_eq_left h2, ite_eq_left h1]
      have := card_pos.2 ⟨_, mem_erase.2 ⟨hjne, h2⟩⟩
      rw [card_erase_of_mem h1] at this; omega
    · rw [erase_eq_of_notMem (fun h => h2 (mem_of_mem_erase h)), card_erase_of_mem h1, ite_eq_right h2,
        ite_eq_left h1]
      have := card_pos.2 ⟨_, h1⟩; omega
    · rw [erase_eq_of_notMem h1, card_erase_of_mem h2, ite_eq_left h2, ite_eq_right h1]
      have := card_pos.2 ⟨_, h2⟩; omega
    · rw [erase_eq_of_notMem h1, erase_eq_of_notMem h2, ite_eq_right h2, ite_eq_right h1, add_zero, add_zero]
  have hSj1 : IsDeg (colS P.h (j + 1) N) (P.h N (j + 1)) := P.isDeg (j + 1) (by omega)
  obtain ⟨K, hK⟩ : ∃ K, K = stepProd P.trunc (win2 T j) D2 C := ⟨_, rfl⟩
  -- the other columns
  have hprod : ∏ c ∈ win2 T j, colS P.h c (N + 1) (C c) = K := by
    rw [hK]
    refine prod_congr rfl fun c hc => ?_
    simp only [win2, mem_erase] at hc
    rw [P.colS_succ_eq hc.2.2]
    simp only [hD2def, mem_erase, hc.1, hc.2.1, ne_eq, not_false_eq_true, true_and]
    rfl
  -- the core: Garnir sums of the truncation
  have hcore : ∀ X' Y' : Finset (Fin n), P.h N j < X'.card → X'.card + Y'.card = P.h N j + P.h N (j + 1) →
      gar (P.h N j) (colS P.h j N) (colS P.h (j + 1) N) X' Y' * K ∈ lmon N D2.card (lower P.trunc) := by
    intro X' Y' h1 h2
    rw [hK]
    refine stepProd_mem hn P.trunc (win2 T j) _ (fun C'' => ?_) D2 hD2w C
    have := hR j hj X' Y' C'' h1 h2
    simpa [garP, stepProd, HPath.trunc] using this
  have hle : lmon N (B N) (lower P.trunc) ≤ lower P := lmon_le_lower hn P hT
  have H1 : D2.card + 1 = B N → ∀ X' Y' : Finset (Fin n), P.h N j < X'.card →
      X'.card + Y'.card = P.h N j + P.h N (j + 1) → ∀ a,
        MvPolynomial.X (N, a) * (gar (P.h N j) (colS P.h j N) (colS P.h (j + 1) N) X' Y' * K) ∈ lower P :=
    fun h3 X' Y' h1 h2 a => hle (h3 ▸ X_mul_mem_lmon (hcore X' Y' h1 h2) a)
  have H2 : D2.card + 1 + 1 = B N → ∀ X' Y' : Finset (Fin n), P.h N j < X'.card →
      X'.card + Y'.card = P.h N j + P.h N (j + 1) → ∀ a b,
        MvPolynomial.X (N, a) * (MvPolynomial.X (N, b) *
          (gar (P.h N j) (colS P.h j N) (colS P.h (j + 1) N) X' Y' * K)) ∈ lower P :=
    fun h3 X' Y' h1 h2 a b => hle (h3 ▸ X_mul_mem_lmon (X_mul_mem_lmon (hcore X' Y' h1 h2) b) a)
  have hconf : ∀ D' : Finset ℤ, (∀ c ∈ win2 T j, c ∈ D' ↔ c ∈ D2) →
      conf P.trunc D' (Function.update (Function.update C j X) (j + 1) Y) =
        (if j ∈ D' then lstep (vec N) N (colS P.h j N) else colS P.h j N) X *
          (if j + 1 ∈ D' then lstep (vec N) N (colS P.h (j + 1) N) else colS P.h (j + 1) N) Y * K := by
    intro D' hD'
    rw [conf_two P.trunc hj, hK]
    simp only [Function.update_self, ne_eq, show j ≠ j + 1 by omega, not_false_eq_true, Function.update_of_ne]
    congr 1
    rw [stepProd_congr_set P.trunc _ hD']
    refine prod_congr rfl fun c hc => ?_
    simp only [win2, mem_erase] at hc
    rw [Function.update_of_ne hc.2.1, Function.update_of_ne hc.1]
  have hstep : ∀ c ∈ win T, (colS P.h c (N + 1) : Finset (Fin n) → _) =
      if c ∈ D then lstep (vec N) N (colS P.h c N) else colS P.h c N := fun c hc => P.colS_succ_eq hc
  rw [garP, hprod, hstep j hjw, hstep (j + 1) hj1w]
  have hXn : X.card ≤ n := card_le_univ X |>.trans (by simp)
  cases hv : vec N
  · -- a covector letter
    have hhj : P.h (N + 1) j + (if j ∈ D then 1 else 0) = P.h N j := P.h_succ_cov hv j
    have hhj1 : P.h (N + 1) (j + 1) + (if j + 1 ∈ D then 1 else 0) = P.h N (j + 1) := P.h_succ_cov hv (j + 1)
    simp only [lstep, Bool.false_eq_true, ↓reduceIte] at hX hXY hD2c ⊢
    by_cases h0 : j ∈ D <;> by_cases h1 : j + 1 ∈ D <;>
      simp only [h0, h1, ↓reduceIte, add_zero] at hX hXY hD2c hhj hhj1 ⊢
    · -- both removed
      obtain ⟨p', hp'⟩ : ∃ p', P.h N j = p' + 1 := ⟨P.h (N + 1) j, hhj.symm⟩
      obtain ⟨q', hq'⟩ : ∃ q', P.h N (j + 1) = q' + 1 := ⟨P.h (N + 1) (j + 1), hhj1.symm⟩
      have e1 : P.h (N + 1) j = p' := by omega
      rw [e1] at hX hXY ⊢
      rw [hp', hq'] at H2
      rw [hq'] at hSj1
      exact gs_cb hSj1 (H2 (by omega)) hX (by omega)
    · -- `j` removed, `j + 1` kept: the special term is `special_cov`
      obtain ⟨p', hp'⟩ : ∃ p', P.h N j = p' + 1 := ⟨P.h (N + 1) j, hhj.symm⟩
      have e1 : P.h (N + 1) j = p' := by omega
      have e2 : P.h (N + 1) (j + 1) = P.h N (j + 1) := hhj1
      rw [e1] at hX hXY ⊢
      rw [e2] at hXY
      rw [hp'] at H1
      have h := gs_cl (m := 1) hSj1 (fun X' Y' h1 h2 a => by rw [one_mul]; exact H1 (by omega) X' Y' h1 h2 a) hX hXY
      rw [one_mul] at h
      split_ifs at h with hc
      · rw [one_mul] at h
        have hge : 1 ≤ P.h N (j + 1) := by omega
        have hsp := special_cov hn P hT hR hv hj h0 h1 hge (Function.update (Function.update C j X) (j + 1) Y)
        rw [hconf _ (fun c hc => by
          simp only [win2, mem_erase] at hc
          simp [hD2def, hDdef, hc.1, hc.2.1])] at hsp
        simp only [mem_insert, mem_erase, show j ≠ j + 1 by omega, false_or, true_or, ne_eq, not_true_eq_false,
          false_and, ↓reduceIte, lstep, hv, Bool.false_eq_true] at hsp
        have := sub_mem h (sign_mul_mem hsp (p' + X.card + Y.card))
        rwa [add_sub_cancel_right] at this
      · rwa [add_zero] at h
    · -- `j` kept, `j + 1` removed
      obtain ⟨q', hq'⟩ : ∃ q', P.h N (j + 1) = q' + 1 := ⟨P.h (N + 1) (j + 1), hhj1.symm⟩
      rw [hhj] at hX hXY ⊢
      rw [hq'] at H1 hSj1
      have h := gs_cr (m := 1) hSj1 (fun X' Y' h1 h2 a => by rw [one_mul]; exact H1 (by omega) X' Y' h1 h2 a)
        (Y := Y) hX (by omega)
      rwa [one_mul] at h
    · rw [hhj, hhj1] at hXY
      rw [hhj] at hX ⊢
      exact hle (by rw [← hD2c]; exact hcore X Y hX hXY)
  · -- a vector letter
    have hhj : P.h (N + 1) j = P.h N j + if j ∈ D then 1 else 0 := P.h_succ_vec hv j
    have hhj1 : P.h (N + 1) (j + 1) = P.h N (j + 1) + if j + 1 ∈ D then 1 else 0 := P.h_succ_vec hv (j + 1)
    simp only [lstep, ↓reduceIte] at hX hXY hD2c ⊢
    rw [hhj, hhj1] at hXY
    rw [hhj] at hX ⊢
    by_cases h0 : j ∈ D <;> by_cases h1 : j + 1 ∈ D <;>
      simp only [h0, h1, ↓reduceIte, add_zero] at hX hXY hD2c ⊢
    · -- both stepped
      exact gs_wb hSj1 (H2 (by omega)) hX (by omega)
    · -- only `j` stepped
      have h := gs_wl (m := 1) (fun X' Y' h1 h2 a => by rw [one_mul]; exact H1 (by omega) X' Y' h1 h2 a)
        (Y := Y) hX (by omega)
      rwa [one_mul] at h
    · -- only `j + 1` stepped: the special term is `special_vec`
      have h := gs_wr hSj1 (H1 (by omega)) (Y := Y) hX (by omega)
      split_ifs at h with hc
      · have hlt : P.h N j < n := by omega
        have hsp := special_vec hn P hT hR hv hj h0 h1 hlt (Function.update (Function.update C j X) (j + 1) Y)
        rw [hconf _ (fun c hc => by
          simp only [win2, mem_erase] at hc
          simp [hD2def, hDdef, hc.1, hc.2.1])] at hsp
        simp only [mem_insert, mem_erase, show j + 1 ≠ j by omega, true_or, ↓reduceIte, ne_eq,
          not_true_eq_false, false_and, or_false, lstep, hv] at hsp
        have := add_mem h (sign_mul_mem hsp Y.card)
        rwa [sub_add_cancel] at this
      · rwa [sub_zero] at h
    · exact hle (by rw [← hD2c]; exact hcore X Y hX hXY)

/-- **The Garnir relations of a path without letters** hold vacuously: the initial heights leave nothing to
shuffle. -/
theorem garStmt_zero (P : HPath n 0 T vec B) : GarStmt P := by
  intro j hj X Y C hX hXY
  rw [P.zero j] at hX
  rw [P.zero j, P.zero (j + 1)] at hXY
  have hXn : X.card ≤ n := card_le_univ X |>.trans (by simp)
  unfold h0 at hX hXY
  split_ifs at hX hXY <;> omega

/-- **(Garnir) Every path satisfies the Garnir relations**: every Garnir sum with something to shuffle lies in the
lower part. -/
theorem garnir_all (hn : 0 < n) : ∀ {N : ℕ} (P : HPath n N T vec B), ∑ s ∈ range N, B s < T → GarStmt P
  | 0, P, _ => garStmt_zero P
  | N + 1, P, hT => garnir_step hn P hT (garnir_all hn P.trunc (by
      rw [sum_range_succ] at hT; omega))

end Garnir

/-! ## The straightening law -/

section Straighten

variable {n N T : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **The binary code of a set of coordinates**: `Σ_{x ∈ S} 2^x`; it orders the sets colexicographically. -/
def enc (S : Finset (Fin n)) : ℕ := ∑ x ∈ S, 2 ^ x.val

/-- **A set below `t` has code below `2^t`.** -/
theorem enc_lt_pow {S : Finset (Fin n)} {t : ℕ} (h : ∀ x ∈ S, x.val < t) : enc S < 2 ^ t := by
  have e : enc S = ∑ k ∈ S.map Fin.valEmbedding, 2 ^ k := by rw [sum_map]; rfl
  rw [e]
  exact Nat.geomSum_lt le_rfl (by simpa using h)

/-- **Every code is below `2^n`.** -/
theorem enc_lt (S : Finset (Fin n)) : enc S < 2 ^ n := enc_lt_pow fun x _ => x.isLt

/-- **A set and its complement have complementary codes.** -/
theorem enc_add_enc_compl (S : Finset (Fin n)) : enc S + enc Sᶜ = enc (univ : Finset (Fin n)) := by
  rw [enc, enc, enc, add_comm, sum_compl_add_sum]

/-- **The exchange raises the code** (colex): replacing the part `D = V_{<t} ∖ U` of `V` by a part `A₁ ⊆ U` outside
`V` of the same size, where `#U_{<t} < #V_{<t}`, raises the code of `V`, since `A₁` must reach beyond `t`. -/
theorem enc_lt_exch {U V A1 : Finset (Fin n)} {t : ℕ} (hA1U : A1 ⊆ U) (hA1V : Disjoint A1 V)
    (hcard : A1.card = ((V.filter fun x => x.val < t) \ U).card)
    (hviol : (U.filter fun x => x.val < t).card < (V.filter fun x => x.val < t).card) :
    enc V < enc (A1 ∪ (V \ ((V.filter fun x => x.val < t) \ U))) := by
  set D := (V.filter fun x => x.val < t) \ U with hD
  have hDV : D ⊆ V := fun x hx => (mem_filter.1 (mem_sdiff.1 hx).1).1
  obtain ⟨a, ha, hat⟩ : ∃ a ∈ A1, t ≤ a.val := by
    by_contra h
    push Not at h
    have hsub : A1 ⊆ (U.filter fun x => x.val < t) \ V := fun x hx =>
      mem_sdiff.2 ⟨mem_filter.2 ⟨hA1U hx, h x hx⟩, disjoint_left.1 hA1V hx⟩
    have h1 := card_le_card hsub
    have h2 := card_sdiff_add_card_inter (U.filter fun x => x.val < t) V
    have h3 : D.card + ((V.filter fun x => x.val < t) ∩ U).card = (V.filter fun x => x.val < t).card :=
      card_sdiff_add_card_inter _ _
    have e : (U.filter fun x => x.val < t) ∩ V = (V.filter fun x => x.val < t) ∩ U := by
      ext x; simp only [mem_inter, mem_filter]; tauto
    rw [e] at h2
    omega
  have hdisj : Disjoint A1 (V \ D) := disjoint_of_subset_right sdiff_subset hA1V
  have e1 : enc (A1 ∪ (V \ D)) = enc A1 + enc (V \ D) := by rw [enc, sum_union hdisj]; rfl
  have e2 : enc V = enc (V \ D) + enc D := by rw [enc, ← sum_sdiff hDV]; rfl
  have h3 : enc D < 2 ^ t := enc_lt_pow fun x hx => (mem_filter.1 (mem_sdiff.1 hx).1).2
  have h4 : 2 ^ t ≤ 2 ^ a.val := Nat.pow_le_pow_right (by norm_num) hat
  have h5 : 2 ^ a.val ≤ ∑ x ∈ A1, 2 ^ x.val := single_le_sum (fun x _ => Nat.zero_le (2 ^ x.val)) ha
  have h6 : enc A1 = ∑ x ∈ A1, 2 ^ x.val := rfl
  omega

/-- **A sum over the window splits off two adjacent columns.** -/
theorem sum_win_two {j : ℤ} (hj : j ∈ Ico (-(T : ℤ)) T) (f : ℤ → ℕ) :
    ∑ c ∈ win T, f c = f j + f (j + 1) + ∑ c ∈ win2 T j, f c := by
  rw [mem_Ico] at hj
  have h1 : j + 1 ∈ win T := mem_Icc.2 ⟨by omega, by omega⟩
  have h2 : j ∈ (win T).erase (j + 1) := mem_erase.2 ⟨by omega, mem_Icc.2 ⟨by omega, by omega⟩⟩
  rw [← add_sum_erase _ _ h1, ← add_sum_erase _ _ h2, win2]
  ring

/-- **The straightening measure** of a filling: `Σ_c enc(col(c)ᶜ)·(2^n)^{c + T}`; an exchange at the columns
`c, c + 1` lowers it. -/
def smeas (T : ℕ) (C : ℤ → Finset (Fin n)) : ℕ := ∑ c ∈ win T, enc (C c)ᶜ * (2 ^ n) ^ (c + T).toNat

/-- **An exchange lowers the measure**: refilling the columns `c, c + 1` so that the code of `col(c + 1)` grows. -/
theorem smeas_lt {C : ℤ → Finset (Fin n)} {c : ℤ} (hc : c ∈ Ico (-(T : ℤ)) T) {U' V' : Finset (Fin n)}
    (h : enc (C (c + 1)) < enc V') :
    smeas T (Function.update (Function.update C c U') (c + 1) V') < smeas T C := by
  have hne : c ≠ c + 1 := by omega
  unfold smeas
  rw [sum_win_two hc, sum_win_two hc]
  simp only [Function.update_self, ne_eq, hne, not_false_eq_true, Function.update_of_ne]
  have hrest : ∑ x ∈ win2 T c, enc (Function.update (Function.update C c U') (c + 1) V' x)ᶜ *
      (2 ^ n) ^ (x + T).toNat = ∑ x ∈ win2 T c, enc (C x)ᶜ * (2 ^ n) ^ (x + T).toNat := by
    refine sum_congr rfl fun x hx => ?_
    simp only [win2, mem_erase] at hx
    rw [Function.update_of_ne hx.2.1, Function.update_of_ne hx.1]
  rw [hrest]
  have hw : (c + 1 + T).toNat = (c + T).toNat + 1 := by rw [mem_Ico] at hc; omega
  rw [hw, pow_succ]
  have h1 := enc_add_enc_compl (C (c + 1))
  have h2 := enc_add_enc_compl V'
  have h3 := enc_lt U'ᶜ
  have hpos : 0 < (2 ^ n) ^ (c + T).toNat := by positivity
  set w := (2 ^ n) ^ (c + T).toNat
  have h4 : enc V'ᶜ + 1 ≤ enc (C (c + 1))ᶜ := by omega
  have h5 : enc U'ᶜ * w < 2 ^ n * w := Nat.mul_lt_mul_of_pos_right h3 hpos
  have h6 : (enc V'ᶜ + 1) * (w * 2 ^ n) ≤ enc (C (c + 1))ᶜ * (w * 2 ^ n) := Nat.mul_le_mul_right _ h4
  nlinarith

/-- **A standard filling in column coordinates**: on the window, `col(c)` has the height of the column `c` after
`N` letters, and the rows weakly increase, `#{x ∈ col(c + 1) : x < t} ≤ #{x ∈ col(c) : x < t}`. -/
def HPath.IsStd (P : HPath n N T vec B) (C : ℤ → Finset (Fin n)) : Prop :=
  (∀ c ∈ win T, (C c).card = P.h N c) ∧ ∀ c ∈ Ico (-(T : ℤ)) T, ∀ t : ℕ,
    ((C (c + 1)).filter fun x => x.val < t).card ≤ ((C c).filter fun x => x.val < t).card

/-- **The straightening of one path**: if a submodule contains the lower part of `P` and the standard path
polynomials of `P`, it contains every path polynomial of `P` (by the exchange relations `HPath.exch_mem` with
`D = col(c + 1)_{<t} ∖ col(c)` at a violation, each exchanged term lowering `smeas`). -/
theorem HPath.psi_mem_of_std (P : HPath n N T vec B) (hG : GarStmt P)
    {M : Submodule ℤ (MvPolynomial (ℕ × Fin n) ℤ)} (hlow : lower P ≤ M)
    (hstd : ∀ C, P.IsStd C → psi P C ∈ M) :
    ∀ C, psi P C ∈ M := by
  intro C
  induction hk : smeas T C using Nat.strong_induction_on generalizing C with
  | _ k ih =>
  by_cases hdeg : ∀ c ∈ win T, (C c).card = P.h N c
  · by_cases hs : ∀ c ∈ Ico (-(T : ℤ)) T, ∀ t : ℕ,
        ((C (c + 1)).filter fun x => x.val < t).card ≤ ((C c).filter fun x => x.val < t).card
    · exact hstd C ⟨hdeg, hs⟩
    push Not at hs
    obtain ⟨c, hc, t, hviol⟩ := hs
    have hcw : c ∈ win T := by rw [mem_Ico] at hc; exact mem_Icc.2 ⟨by omega, by omega⟩
    have hc1w : c + 1 ∈ win T := by rw [mem_Ico] at hc; exact mem_Icc.2 ⟨by omega, by omega⟩
    set U := C c with hUdef
    set V := C (c + 1) with hVdef
    set D := (V.filter fun x => x.val < t) \ U with hDdef
    have hDV : D ⊆ V := fun x hx => (mem_filter.1 (mem_sdiff.1 hx).1).1
    have hUD : Disjoint U D := disjoint_left.2 fun x hxU hxD => (mem_sdiff.1 hxD).2 hxU
    have hU : U.card = P.h N c := hdeg c hcw
    have hV : V.card = P.h N (c + 1) := hdeg (c + 1) hc1w
    have hx := P.exch_mem hG hc C hU hV hDV hUD
    have hpsi : psi P C = psi2 P c C U V := by
      rw [psi2_eq P hc, hUdef, hVdef, Function.update_eq_self, Function.update_eq_self]
    have hex : exch (psi2 P c C) U V D ∈ M := by
      refine sum_mem fun A1 hA1 => ?_
      rw [mem_powersetCard] at hA1
      by_cases hV' : (A1 ∪ (V \ D)).card = P.h N (c + 1)
      · have hint : (A1 ∩ (V \ D)).card = 0 := by
          have h1 := card_union_add_card_inter A1 (V \ D)
          have h2 := card_sdiff_add_card_inter V D
          rw [inter_eq_right.2 hDV] at h2
          omega
        have hA1V : Disjoint A1 V := disjoint_left.2 fun x hxA hxV => by
          by_cases hxD : x ∈ D
          · exact (mem_sdiff.1 hxD).2 (hA1.1 hxA)
          · exact (card_eq_zero.1 hint ▸ (mem_inter.2 ⟨hxA, mem_sdiff.2 ⟨hxV, hxD⟩⟩) : x ∈ (∅ : Finset (Fin n)))
              |> (notMem_empty x)
        have hlt := enc_lt_exch hA1.1 hA1V hA1.2 hviol
        rw [psi2_eq P hc]
        exact sign_mul_mem (ih _ (hk ▸ smeas_lt hc hlt) _ rfl) _
      · rw [psi2, P.isDeg (c + 1) le_rfl _ hV', mul_zero, zero_mul, mul_zero]
        exact zero_mem _
    have h1 : (-1) ^ D.card * sgn U V * psi2 P c C U V ∈ M := by
      have := sub_mem hex (hlow hx)
      rwa [sub_sub_cancel] at this
    have h2 : psi2 P c C U V = ((-1) ^ (D.card + inv U V)) * ((-1) ^ D.card * sgn U V * psi2 P c C U V) := by
      rw [sgn, ← pow_add]
      have hsq : ((-1 : MvPolynomial (ℕ × Fin n) ℤ) ^ (D.card + inv U V)) * (-1) ^ (D.card + inv U V) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; simp
      rw [← mul_assoc, hsq, one_mul]
    rw [hpsi, h2]
    exact sign_mul_mem h1 _
  · push Not at hdeg
    obtain ⟨c, hc, hne⟩ := hdeg
    rw [psi, prod_eq_zero hc (P.isDeg c le_rfl _ hne)]
    exact zero_mem _

/-- **The order on paths is the lexicographic order of the potentials.** -/
theorem HPath.lt_iff {Q P : HPath n N T vec B} : Q.lt P ↔ phiLex Q < phiLex P := by
  refine ⟨HPath.lt_phiLex, fun h => ?_⟩
  obtain ⟨i, hi1, hi2⟩ := h
  exact ⟨i.val, by omega, fun s hs => hi1 ⟨s, by omega⟩ hs, hi2⟩

/-- **The order on paths is transitive.** -/
theorem HPath.lt_trans {R Q P : HPath n N T vec B} (h1 : R.lt Q) (h2 : Q.lt P) : R.lt P :=
  HPath.lt_iff.2 ((HPath.lt_iff.1 h1).trans (HPath.lt_iff.1 h2))

/-- **The standard span below `P`**: the `ℤ`-span of the standard path polynomials `Ψ(Q, I)` of the paths `Q ⪯ P`
(`Q = P` or `Q ≺ P`). -/
def stdSpan (P : HPath n N T vec B) : Submodule ℤ (MvPolynomial (ℕ × Fin n) ℤ) :=
  Submodule.span ℤ {f | ∃ Q : HPath n N T vec B, (Q = P ∨ Q.lt P) ∧ ∃ C, Q.IsStd C ∧ f = psi Q C}

/-- **The standard span grows with the path.** -/
theorem stdSpan_mono {Q P : HPath n N T vec B} (h : Q.lt P) : stdSpan Q ≤ stdSpan P :=
  Submodule.span_mono fun _ ⟨R, hR, C, hC, hf⟩ =>
    ⟨R, Or.inr (hR.elim (fun e => e ▸ h) fun h' => HPath.lt_trans h' h), C, hC, hf⟩

/-- **(Straightening) The straightening law**: every path polynomial `Ψ(P, C)` lies in the `ℤ`-span of the standard
path polynomials `Ψ(Q, I)` with `Q = P` or `Q ≺ P` in the lexicographic order of the potentials (`HPath.lt`). By
well-founded induction on `P`: the lower part lies in the standard span by induction, and the Garnir relations of `P`
(`garnir_all`) straighten the rest (`HPath.psi_mem_of_std`). -/
theorem straighten (hn : 0 < n) (hT : ∑ s ∈ range N, B s < T) (P : HPath n N T vec B) (C : ℤ → Finset (Fin n)) :
    psi P C ∈ stdSpan P := by
  induction P using HPath.lt_wf.induction generalizing C with
  | _ P ih =>
  refine P.psi_mem_of_std (M := stdSpan P) (garnir_all hn P hT) ?_
    (fun C hC => Submodule.subset_span ⟨P, Or.inl rfl, C, hC, rfl⟩) C
  refine Submodule.span_le.2 ?_
  rintro f ⟨Q, hQ, C', rfl⟩
  exact stdSpan_mono hQ (ih Q hQ C')

end Straighten

/-! ## Spanning: the monomials are combinations of path polynomials -/

section Span

variable {n N T : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

variable (n N T vec B) in
/-- **The span of all path polynomials** (all paths, all fillings). -/
def allSpan : Submodule ℤ (MvPolynomial (ℕ × Fin n) ℤ) :=
  Submodule.span ℤ {f | ∃ Q : HPath n N T vec B, ∃ C, f = psi Q C}

variable (n N T vec B) in
/-- **The span of the standard path polynomials.** -/
def stdAll : Submodule ℤ (MvPolynomial (ℕ × Fin n) ℤ) :=
  Submodule.span ℤ {f | ∃ Q : HPath n N T vec B, ∃ C, Q.IsStd C ∧ f = psi Q C}

/-- **The standard path polynomials span all path polynomials** (straightening). -/
theorem allSpan_le_stdAll (hn : 0 < n) (hT : ∑ s ∈ range N, B s < T) : allSpan n N T vec B ≤ stdAll n N T vec B := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨P, C, rfl⟩
  refine (Submodule.span_le.2 ?_ : stdSpan P ≤ stdAll n N T vec B) (straighten hn hT P C)
  rintro g ⟨Q, -, C', hC', rfl⟩
  exact Submodule.subset_span ⟨Q, C', hC', rfl⟩

/-- **Monomials of the new letter carry all path polynomials into all path polynomials** (the first-row trick, as in
`mono_mul_lower`). -/
theorem mono_mul_allSpan (hn : 0 < n) (hT : ∑ s ∈ range (N + 1), B s < T) {f : MvPolynomial (ℕ × Fin n) ℤ}
    (hf : f ∈ allSpan n N T vec B) (g : ℕ → Fin n) :
    (∏ i ∈ range (B N), X (N, g i)) * f ∈ allSpan n (N + 1) T vec B := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨Q, C, rfl⟩ := hf
    cases hv : vec N
    · by_cases hC : ∀ c ∈ Q.stripC, C c = univ
      · have e := Q.psi_extC hn hv hT g hC
        obtain ⟨k, hk⟩ := prod_sg_eq Q.stripC (fun c => g (c - (Q.bot - B N) - 1).toNat)
          (fun c => univ.erase (g (c - (Q.bot - B N) - 1).toNat))
        rw [hk] at e
        have e' : (∏ i ∈ range (B N), X (N, g i)) * psi Q C =
            (-1) ^ k * psi (Q.extC hn hv hT)
              (fun c => if c ∈ Q.stripC then univ.erase (g (c - (Q.bot - B N) - 1).toNat) else C c) := by
          rw [e, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
        rw [e']
        refine sign_mul_mem ?_ k
        exact Submodule.subset_span ⟨_, _, rfl⟩
      · simp only [not_forall, exists_prop] at hC
        obtain ⟨c, hc, hCc⟩ := hC
        have hz : psi Q C = 0 := by
          refine prod_eq_zero (Ioo_subset_Icc_self (Q.stripC_sub hn hT hc)) ?_
          refine Q.isDeg c le_rfl _ ?_
          have := (Q.bot_spec hn).2.2.1 c (mem_Ioc.1 hc).2
          rw [this]
          intro h'
          exact hCc (eq_univ_of_card _ (by simpa using h'))
        rw [hz, mul_zero]; exact zero_mem _
    · by_cases hC : ∀ c ∈ Q.stripV hn, C c = ∅
      · rw [← Q.psi_extV hn hv hT g hC]
        exact Submodule.subset_span ⟨_, _, rfl⟩
      · simp only [not_forall, exists_prop] at hC
        obtain ⟨c, hc, hCc⟩ := hC
        have hz : psi Q C = 0 := by
          refine prod_eq_zero (Ioo_subset_Icc_self (Q.stripV_sub hn hT hc)) ?_
          refine Q.isDeg c le_rfl _ ?_
          rw [(Q.top_spec hn).2.2.2 c (mem_Ioc.1 hc).1]
          exact fun h' => hCc (card_eq_zero.1 h')
        rw [hz, mul_zero]; exact zero_mem _
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hx

variable (n T vec B) in
/-- **The path without letters**: the initial heights. -/
def HPath.init : HPath n 0 T vec B where
  h _ := h0 n
  zero _ := rfl
  anti _ _ c c' hcc' := by unfold h0; split_ifs <;> omega
  le _ _ c := by unfold h0; split_ifs <;> omega
  out _ _ _ _ := rfl
  up _ ht := absurd ht (Nat.not_lt_zero _)
  down _ ht := absurd ht (Nat.not_lt_zero _)
  card _ ht := absurd ht (Nat.not_lt_zero _)

/-- **The constant `1` is a path polynomial** of the path without letters, with the initial filling. -/
theorem one_mem_allSpan : (1 : MvPolynomial (ℕ × Fin n) ℤ) ∈ allSpan n 0 T vec B := by
  refine Submodule.subset_span ⟨HPath.init n T vec B, fun c => if c ≤ 0 then univ else ∅, ?_⟩
  symm
  refine prod_eq_one fun c _ => ?_
  simp only [colS, ust, ust0, h0]
  split_ifs <;> simp_all

/-- **A monomial of one letter** is a product of `k` variables of that letter. -/
theorem exists_monomial_eq_prod (hn : 0 < n) (N : ℕ) : ∀ (k : ℕ) (e : (ℕ × Fin n) →₀ ℕ), (∀ v ∈ e.support, v.1 = N) →
    ∑ a, e (N, a) = k → ∃ g : ℕ → Fin n, (monomial e 1 : MvPolynomial (ℕ × Fin n) ℤ) = ∏ i ∈ range k, X (N, g i)
  | 0, e, he, hk => by
    refine ⟨fun _ => ⟨0, hn⟩, ?_⟩
    have h0 : e = 0 := by
      ext v
      by_contra hv
      have hv' := he v (Finsupp.mem_support_iff.2 hv)
      have := (sum_eq_zero_iff.1 hk) v.2 (mem_univ _)
      rw [← hv'] at this
      exact hv this
    rw [h0, prod_range_zero]
    rfl
  | k + 1, e, he, hk => by
    obtain ⟨a, ha⟩ : ∃ a, 0 < e (N, a) := by
      by_contra h
      push Not at h
      rw [sum_eq_zero fun a _ => Nat.le_zero.1 (h a)] at hk
      omega
    set e' := e - Finsupp.single (N, a) 1 with he'def
    have he' : e' + Finsupp.single (N, a) 1 = e := tsub_add_cancel_of_le (Finsupp.single_le_iff.2 ha)
    have hsupp : ∀ v ∈ e'.support, v.1 = N := fun v hv => by
      refine he v (Finsupp.mem_support_iff.2 fun h0 => ?_)
      have : e' v ≤ e v := by rw [← he']; exact le_self_add
      exact (Finsupp.mem_support_iff.1 hv) (by omega)
    have hsum : ∑ b, e' (N, b) = k := by
      have : ∑ b, e (N, b) = ∑ b, e' (N, b) + 1 := by
        rw [← he']
        simp only [Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq, true_and, sum_add_distrib]
        rw [sum_ite_eq]
        simp
      omega
    obtain ⟨g', hg'⟩ := exists_monomial_eq_prod hn N k e' hsupp hsum
    refine ⟨fun i => if i < k then g' i else a, ?_⟩
    rw [← he', monomial_add_single, pow_one, hg', prod_range_succ]
    simp only [lt_irrefl, ↓reduceIte]
    exact congrArg (· * X (N, a)) (prod_congr rfl fun i hi => by simp [mem_range.1 hi])

/-- **(Spanning) Every monomial of multidegree `B` is a `ℤ`-combination of path polynomials**: by induction on the
letters, splitting off the monomial of the last letter (`mono_mul_allSpan`). -/
theorem monomial_mem_allSpan (hn : 0 < n) : ∀ {N : ℕ}, ∑ s ∈ range N, B s < T → ∀ d : (ℕ × Fin n) →₀ ℕ,
    (∀ l, ∑ a, d (l, a) = if l < N then B l else 0) → (monomial d 1 : MvPolynomial (ℕ × Fin n) ℤ) ∈
      allSpan n N T vec B
  | 0, _, d, hd => by
    have h0 : d = 0 := by
      ext v
      have h1 := hd v.1
      simp only [Nat.not_lt_zero, ↓reduceIte, sum_eq_zero_iff, mem_univ, true_implies] at h1
      simpa using h1 v.2
    rw [h0]
    exact one_mem_allSpan
  | N + 1, hT, d, hd => by
    set e := d.filter fun v => v.1 = N
    set d' := d.filter fun v => ¬ v.1 = N
    have hsplit : e + d' = d := Finsupp.filter_add_filter_not _ _
    have hd' : ∀ l, ∑ a, d' (l, a) = if l < N then B l else 0 := fun l => by
      by_cases hl : l = N
      · subst hl
        simp [d']
      · have := hd l
        simp only [d', Finsupp.filter_apply, hl, not_false_eq_true, ↓reduceIte]
        rw [this]
        by_cases h1 : l < N
        · simp [h1, show l < N + 1 by omega]
        · simp [h1, show ¬ l < N + 1 by omega]
    have he : ∀ v ∈ e.support, v.1 = N := fun v hv => by
      by_contra h
      exact (Finsupp.mem_support_iff.1 hv) (by simp [e, h])
    have hes : ∑ a, e (N, a) = B N := by
      simp only [e, Finsupp.filter_apply, ↓reduceIte]
      rw [hd N]
      simp
    obtain ⟨g, hg⟩ := exists_monomial_eq_prod hn N (B N) e he hes
    have ih := monomial_mem_allSpan hn (by rw [sum_range_succ] at hT; omega) d' hd'
    rw [← hsplit, ← mul_one (1 : ℤ), ← monomial_mul_monomial, hg]
    exact mono_mul_allSpan hn hT ih g

end Span

/-! ## From column coordinates to the path family: the Hodge star of the columns `c ≤ 0` -/

section Hodge

variable {n : ℕ}

/-- **The exponent of the Hodge sign** of a set: `Σ_{x ∈ J} (n − 1 − x)`. -/
def hexp (J : Finset (Fin n)) : ℕ := ∑ x ∈ J, (n - 1 - x.val)

/-- **The Hodge sign** `σ(J) = (−1)^{Σ_{x ∈ J} (n − 1 − x)}`. -/
def hsg (J : Finset (Fin n)) : MvPolynomial (ℕ × Fin n) ℤ := (-1) ^ hexp J

/-- **The Hodge sign squares to one.** -/
theorem hsg_mul_self (J : Finset (Fin n)) : hsg J * hsg J = 1 := by
  rw [hsg, ← pow_add, ← two_mul, pow_mul]; simp

/-- **The coordinates above `a`**, inside and outside a set: `#J_{>a} + #Jᶜ_{>a} = n − 1 − a`. -/
theorem card_gt_add_card_gt_compl (J : Finset (Fin n)) (a : Fin n) :
    (J.filter (a < ·)).card + (Jᶜ.filter (a < ·)).card = n - 1 - a.val := by
  rw [← card_union_of_disjoint (disjoint_filter_filter disjoint_compl_right), ← filter_union, union_compl,
    ← Fin.card_Ioi]
  congr 1
  ext x; simp

/-- **The Hodge sign with one more element.** -/
theorem hsg_insert {a : Fin n} {J : Finset (Fin n)} (ha : a ∉ J) :
    hsg (insert a J) = hsg J * (-1) ^ (n - 1 - a.val) := by
  rw [hsg, hsg, hexp, hexp, sum_insert ha, ← pow_add, add_comm]

/-- **The sign of `a` in `J` and in `Jᶜ`** differ by `(−1)^{n − 1 − a}`. -/
theorem sg_mul_pow (J : Finset (Fin n)) (a : Fin n) :
    (sg a J : MvPolynomial (ℕ × Fin n) ℤ) * (-1) ^ (n - 1 - a.val) = sg a Jᶜ := by
  rw [sg, sg, ← pow_add]
  have := card_gt_add_card_gt_compl J a
  exact neg_one_pow_congr (by omega)

/-- **Contracting the Hodge dual is the dual of wedging**: `y ⌟ ⋆K = ⋆(y ∧ K)`, with `⋆K(J) = σ(J)·K(Jᶜ)`. -/
theorem contr_hodge (y : Fin n → MvPolynomial (ℕ × Fin n) ℤ) (K : Finset (Fin n) → MvPolynomial (ℕ × Fin n) ℤ)
    (J : Finset (Fin n)) : contr y (fun J => hsg J * K Jᶜ) J = hsg J * wedge y K Jᶜ := by
  rw [contr, wedge, mul_sum]
  refine sum_congr rfl fun a ha => ?_
  have ha' : a ∉ J := mem_compl.1 ha
  rw [hsg_insert ha', compl_insert, ← sg_mul_pow J a]
  ring

/-- **Wedging the Hodge dual is the dual of contracting**: `y ∧ ⋆K = ⋆(y ⌟ K)`. -/
theorem wedge_hodge (y : Fin n → MvPolynomial (ℕ × Fin n) ℤ) (K : Finset (Fin n) → MvPolynomial (ℕ × Fin n) ℤ)
    (J : Finset (Fin n)) : wedge y (fun J => hsg J * K Jᶜ) J = hsg J * contr y K Jᶜ := by
  rw [contr, wedge, mul_sum, compl_compl]
  refine sum_congr rfl fun a ha => ?_
  have h1 : hsg J = hsg (J.erase a) * (-1) ^ (n - 1 - a.val) := by
    rw [← hsg_insert (notMem_erase a J), insert_erase ha]
  have h2 : (sg a J : MvPolynomial (ℕ × Fin n) ℤ) = sg a (J.erase a) := (sg_erase_self a J).symm
  have h4 : (sg a Jᶜ : MvPolynomial (ℕ × Fin n) ℤ) = sg a (J.erase a) * (-1) ^ (n - 1 - a.val) := by
    rw [sg_mul_pow, compl_erase, sg_insert_self]
  rw [compl_erase, h1, h2, h4]
  have h3 : ((-1 : MvPolynomial (ℕ × Fin n) ℤ) ^ (n - 1 - a.val)) * (-1) ^ (n - 1 - a.val) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination (-(sg a (J.erase a) * y a * hsg (J.erase a) * K (insert a Jᶜ))) * h3

/-- **Wedging commutes with scalars.** -/
theorem wedge_mul_left (y : Fin n → MvPolynomial (ℕ × Fin n) ℤ) (s : MvPolynomial (ℕ × Fin n) ℤ)
    (S : Finset (Fin n) → MvPolynomial (ℕ × Fin n) ℤ) (J : Finset (Fin n)) :
    wedge y (fun J => s * S J) J = s * wedge y S J := by
  rw [wedge, wedge, mul_sum]; exact sum_congr rfl fun _ _ => by ring

/-- **Contracting commutes with scalars.** -/
theorem contr_mul_left (y : Fin n → MvPolynomial (ℕ × Fin n) ℤ) (s : MvPolynomial (ℕ × Fin n) ℤ)
    (S : Finset (Fin n) → MvPolynomial (ℕ × Fin n) ℤ) (J : Finset (Fin n)) :
    contr y (fun J => s * S J) J = s * contr y S J := by
  rw [contr, contr, mul_sum]; exact sum_congr rfl fun _ _ => by ring

/-- **The columns `c ≥ 1` in both coordinates agree**: `K_c = S_c` when the heights are those of the weights. -/
theorem colK_eq_colS_pos {mu : ℕ → Fin n → ℤ} {h : ℕ → ℤ → ℕ} {N : ℕ} (hh : ∀ t ≤ N, ∀ c, colH (mu t) c = h t c)
    {c : ℤ} (hc : 1 ≤ c) : colK ℤ mu c N = colS h c N := by
  suffices ∀ t ≤ N, colSt (fun t a => (X (t, a) : MvPolynomial (ℕ × Fin n) ℤ)) (colStep mu c) (fun _ => 1) t =
      colS h c t from this N le_rfl
  intro t ht
  induction t with
  | zero =>
    funext J
    simp only [colSt, st0, colS, ust, ust0, h0, show ¬ c ≤ 0 by omega, ↓reduceIte, card_eq_zero]
  | succ t ih =>
    rw [colSt_succ, colS_succ, ← ih (by omega)]
    have hs : colStep mu c t = ustep h c t := by
      unfold colStep ustep
      rw [hh t (by omega), hh (t + 1) ht]
      simp only [hc, ↓reduceIte]
    funext J
    rw [hs]
    simp [pw]

/-- **The columns `c ≤ 0` are Hodge duals**: `K_c(Jᶜ) = σ(J)·σ(univ)·S_c(J)` when the heights are those of the
weights (`K_c` starts at `[J = ∅]` and contracts where `S_c`, starting at `[J = univ]`, wedges). -/
theorem colK_compl {mu : ℕ → Fin n → ℤ} {h : ℕ → ℤ → ℕ} {N : ℕ} (hh : ∀ t ≤ N, ∀ c, colH (mu t) c = h t c)
    {c : ℤ} (hc : c ≤ 0) (J : Finset (Fin n)) : colK ℤ mu c N Jᶜ = hsg J * hsg univ * colS h c N J := by
  suffices H : ∀ t ≤ N, ∀ J, hsg J * colSt (fun t a => (X (t, a) : MvPolynomial (ℕ × Fin n) ℤ)) (colStep mu c)
      (fun _ => 1) t Jᶜ = hsg univ * colS h c t J by
    have := H N le_rfl J
    unfold colK
    linear_combination hsg J * this - (colSt (fun t a => (X (t, a) : MvPolynomial (ℕ × Fin n) ℤ)) (colStep mu c)
      (fun _ => 1) N Jᶜ) * hsg_mul_self J
  intro t ht
  induction t with
  | zero =>
    intro J
    simp only [colSt, st0, colS, ust, ust0, h0, hc, ↓reduceIte, compl_eq_empty_iff]
    by_cases hJ : J = univ
    · subst hJ; simp
    · have : J.card ≠ n := fun h' => hJ (eq_univ_of_card J (by simpa using h'))
      simp [hJ, this]
  | succ t ih =>
    have hS : (fun J => hsg J * colSt (fun t a => (X (t, a) : MvPolynomial (ℕ × Fin n) ℤ)) (colStep mu c)
        (fun _ => 1) t Jᶜ) = fun J => hsg univ * colS h c t J := funext (ih (by omega))
    intro J
    have hst : colStep mu c t = if h t c < h (t + 1) c then .con else if h (t + 1) c < h t c then .wed else .keep := by
      unfold colStep
      rw [hh t (by omega), hh (t + 1) ht]
      simp only [show ¬ (1 ≤ c) by omega, ↓reduceIte]
    rw [colSt_succ, colS_succ, hst]
    unfold ustep
    split_ifs with h1 h2
    · simp only [pw, pow_one, Step.app]
      rw [← wedge_hodge, hS, wedge_mul_left]
    · simp only [pw, pow_one, Step.app]
      rw [← contr_hodge, hS, contr_mul_left]
    · simp only [pw, pow_one, Step.app]
      exact ih (by omega) J

end Hodge

/-! ## Pieri paths from column paths: weights from heights -/

section ToPieri

variable {n N T : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **The weight of a height function** on the window: `μ_a = −T + #{c ∈ (−T, T] : a < h(c)}`, the last column
reached by the row `a`. -/
def wOf (T : ℕ) (h : ℤ → ℕ) (a : Fin n) : ℤ := -(T : ℤ) + (((Ioc (-(T : ℤ)) T).filter fun c => a.val < h c).card : ℤ)

/-- **The row `a` reaches the column `c`** iff `c ≤ μ_a`, for antitone heights full before the window and empty
after it. -/
theorem le_wOf_iff {h : ℤ → ℕ} (hanti : Antitone h) (hlo : ∀ c ≤ -(T : ℤ), h c = n)
    (hhi : ∀ c, (T : ℤ) < c → h c = 0) (a : Fin n) (c : ℤ) : c ≤ wOf T h a ↔ a.val < h c := by
  by_cases hc : c ∈ Ioc (-(T : ℤ)) T
  · exact (mem_filter_Ioc_iff (P := fun c => a.val < h c) (fun x y hxy hy => lt_of_lt_of_le hy (hanti hxy)) hc).symm
  · rw [mem_Ioc, not_and_or, not_lt, not_le] at hc
    rcases hc with hc | hc
    · rw [hlo c hc]
      simp only [a.isLt, iff_true]
      unfold wOf
      omega
    · rw [hhi c hc]
      simp only [Nat.not_lt_zero, iff_false, not_le]
      unfold wOf
      have := card_le_card (filter_subset (fun c => a.val < h c) (Ioc (-(T : ℤ)) T))
      rw [Int.card_Ioc] at this
      omega

/-- **The weights have the given column heights.** -/
theorem colH_wOf {h : ℤ → ℕ} (hanti : Antitone h) (hlo : ∀ c ≤ -(T : ℤ), h c = n)
    (hhi : ∀ c, (T : ℤ) < c → h c = 0) (hle : ∀ c, h c ≤ n) (c : ℤ) : colH (wOf (n := n) T h) c = h c := by
  unfold colH
  rw [filter_congr fun a _ => le_wOf_iff hanti hlo hhi a c, Fin.card_filter_val_lt]
  have := hle c
  omega

/-- **The weights of heights growing by at most one form a horizontal strip** of the size the number of grown
columns. -/
theorem isStrip_wOf {h' h : ℤ → ℕ} (ha' : Antitone h') (hlo' : ∀ c ≤ -(T : ℤ), h' c = n)
    (hhi' : ∀ c, (T : ℤ) < c → h' c = 0) (hle' : ∀ c, h' c ≤ n) (ha : Antitone h)
    (hlo : ∀ c ≤ -(T : ℤ), h c = n) (hhi : ∀ c, (T : ℤ) < c → h c = 0) (hle : ∀ c, h c ≤ n)
    (h1 : ∀ c, h' c ≤ h c) (h2 : ∀ c, h c ≤ h' c + 1) :
    IsStrip (wOf (n := n) T h') (wOf T h) ((win T).filter fun c => h' c ≠ h c).card := by
  have hc1 := le_wOf_iff ha' hlo' hhi'
  have hc2 := le_wOf_iff ha hlo hhi
  have hνμ : ∀ a, wOf T h' a ≤ wOf T h a := fun a => (hc2 a _).2 (lt_of_lt_of_le ((hc1 a _).1 le_rfl) (h1 _))
  have hlow : ∀ (g : ℤ → ℕ) (a : Fin n), -(T : ℤ) ≤ wOf T g a := fun g a => by unfold wOf; omega
  have hup : ∀ (g : ℤ → ℕ) (a : Fin n), wOf T g a ≤ T := fun g a => by
    unfold wOf
    have := card_le_card (filter_subset (fun c => a.val < g c) (Ioc (-(T : ℤ)) T))
    rw [Int.card_Ioc] at this
    omega
  refine ⟨hνμ, fun a a' haa' => (hc1 a _).2 ?_, ?_⟩
  · have := (hc2 a' _).1 le_rfl
    have := h2 (wOf T h a')
    omega
  · have hs := sum_colH_sub hνμ (L := -(T : ℤ)) (U := T) (hlow h') (hup h)
    have e : ∀ c, ((colH (wOf (n := n) T h) c : ℤ) - colH (wOf (n := n) T h') c) = if h' c ≠ h c then 1 else 0 := by
      intro c
      rw [colH_wOf ha hlo hhi hle, colH_wOf ha' hlo' hhi' hle']
      have := h1 c
      have := h2 c
      split_ifs <;> omega
    simp_rw [e] at hs
    rw [sum_boole] at hs
    have hf : (win T).filter (fun c => h' c ≠ h c) = (Ioc (-(T : ℤ)) T).filter (fun c => h' c ≠ h c) := by
      ext c
      simp only [mem_filter, mem_Icc, mem_Ioc]
      constructor
      · rintro ⟨⟨hc1, hc2⟩, hc3⟩
        refine ⟨⟨?_, hc2⟩, hc3⟩
        by_contra hc
        exact hc3 (by rw [hlo' c (by omega), hlo c (by omega)])
      · rintro ⟨⟨hc1, hc2⟩, hc3⟩
        exact ⟨⟨by omega, hc2⟩, hc3⟩
    rw [hf]
    linarith

/-- **The heights of a path are full before the window.** -/
theorem HPath.h_lo (P : HPath n N T vec B) {t : ℕ} (ht : t ≤ N) : ∀ c ≤ -(T : ℤ), P.h t c = n := fun c hc => by
  rw [P.out t ht c (by simp only [mem_Ioo]; omega), h0, ite_eq_left (by omega)]

/-- **The heights of a path are empty after the window.** -/
theorem HPath.h_hi (P : HPath n N T vec B) {t : ℕ} (ht : t ≤ N) : ∀ c, (T : ℤ) < c → P.h t c = 0 := fun c hc => by
  rw [P.out t ht c (by simp only [mem_Ioo]; omega), h0, ite_eq_right (by omega)]

/-- **The weights of the initial heights vanish.** -/
theorem wOf_h0 : wOf (n := n) T (h0 n) = 0 := by
  have hanti : Antitone (h0 n) := fun c c' h => by unfold h0; split_ifs <;> omega
  have hc := le_wOf_iff hanti (T := T) (fun c hc => by rw [h0, ite_eq_left (by omega)])
    (fun c hc => by rw [h0, ite_eq_right (by omega)])
  funext a
  have h1 := (hc a (wOf T (h0 n) a)).1 le_rfl
  have h2 := (hc a 0).2 (by rw [h0, ite_eq_left le_rfl]; exact a.isLt)
  unfold h0 at h1
  split_ifs at h1 with h3
  · exact le_antisymm h3 h2
  · omega

/-- **The Pieri path of a column path**: its weights read from its heights (`wOf`). -/
def HPath.toPieri (P : HPath n N T vec B) : PieriPath n N vec B where
  mu t := wOf T (P.h (min t N))
  zero := by
    rw [Nat.zero_min]
    have : P.h 0 = h0 n := funext P.zero
    rw [this, wOf_h0]
  step t ht := by
    rw [min_eq_left ht.le, min_eq_left (Nat.succ_le_of_lt ht)]
    have hcard := P.card t ht
    unfold IsStep
    cases hv : vec t
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have := isStrip_wOf (P.anti (t + 1) ht) (P.h_lo ht) (P.h_hi ht) (P.le (t + 1) ht) (P.anti t ht.le)
        (P.h_lo ht.le) (P.h_hi ht.le) (P.le t ht.le) (fun c => (P.down t ht hv c).1) (fun c => (P.down t ht hv c).2)
      simp only [ne_comm (a := P.h (t + 1) _)] at this
      rwa [hcard] at this
    · simp only [↓reduceIte]
      have := isStrip_wOf (P.anti t ht.le) (P.h_lo ht.le) (P.h_hi ht.le) (P.le t ht.le) (P.anti (t + 1) ht)
        (P.h_lo ht) (P.h_hi ht) (P.le (t + 1) ht) (fun c => (P.up t ht hv c).1) (fun c => (P.up t ht hv c).2)
      rwa [hcard] at this
  stop t ht := by rw [min_eq_right ht, min_self]

/-- **The Pieri path of a column path has its heights.** -/
theorem HPath.colH_toPieri (P : HPath n N T vec B) {t : ℕ} (ht : t ≤ N) (c : ℤ) :
    colH (P.toPieri.mu t) c = P.h t c := by
  show colH (wOf T (P.h (min t N))) c = P.h t c
  rw [min_eq_left ht]
  exact colH_wOf (P.anti t ht) (P.h_lo ht) (P.h_hi ht) (P.le t ht) c

end ToPieri

/-! ## Standard path polynomials are path family members, up to sign -/

section ToFam

variable {n N T : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **The column system of a window filling**: `C` on the window, full before it and empty after it. -/
def winFill (T : ℕ) (C : ℤ → Finset (Fin n)) (c : ℤ) : Finset (Fin n) :=
  if c ∈ win T then C c else if c < 0 then univ else ∅

/-- **A standard window filling is a standard filling** of the end weight of the Pieri path, through `colSet`. -/
theorem HPath.isStdFilling_ext (P : HPath n N T vec B) {C : ℤ → Finset (Fin n)} (hC : P.IsStd C) :
    IsStdFilling (P.toPieri.mu N) (colSet (winFill T C)) := by
  unfold IsStdFilling
  rw [colSet_colSet]
  refine ⟨fun c => ?_, fun c t => ?_⟩
  · rw [P.colH_toPieri le_rfl]
    unfold winFill
    split_ifs with h1 h2
    · exact hC.1 c h1
    · rw [card_univ, Fintype.card_fin, P.h_lo le_rfl c (by rw [mem_Icc] at h1; omega)]
    · rw [card_empty, P.h_hi le_rfl c (by rw [mem_Icc] at h1; omega)]
  · by_cases hc : c ∈ Ico (-(T : ℤ)) T
    · have h1 : c ∈ win T := by rw [mem_Ico] at hc; exact mem_Icc.2 ⟨by omega, by omega⟩
      have h2 : c + 1 ∈ win T := by rw [mem_Ico] at hc; exact mem_Icc.2 ⟨by omega, by omega⟩
      simp only [winFill, h1, h2, ↓reduceIte]
      exact hC.2 c hc t
    · rw [mem_Ico, not_and_or, not_le, not_lt] at hc
      rcases hc with hc | hc
      · have e : winFill T C c = univ := by
          simp only [winFill, mem_Icc, show ¬ (-(T : ℤ) ≤ c) by omega, false_and, ↓reduceIte,
            show c < 0 by omega]
        rw [e]
        exact card_le_card (filter_subset_filter _ (subset_univ _))
      · have e : winFill T C (c + 1) = ∅ := by
          simp only [winFill, mem_Icc, show ¬ (c + 1 ≤ (T : ℤ)) by omega, and_false, ↓reduceIte,
            show ¬ (c + 1 < 0) by omega]
        rw [e, filter_empty, card_empty]
        exact Nat.zero_le _

/-- **Standard path polynomials lie in the span of the path family**: `Ψ(P, C) = ±Ψ(P.toPieri, I)` for the filling
`I` with columns `winFill C` (the columns `c ≥ 1` agree, the columns `c ≤ 0` are Hodge duals, `colK_compl`). -/
theorem HPath.psi_mem_span (P : HPath n N T vec B) {C : ℤ → Finset (Fin n)} (hC : P.IsStd C) :
    psi P C ∈ Submodule.span ℤ (Set.range (pathFam ℤ (n := n) (N := N) (vec := vec) (B := B))) := by
  set x : PathIdx n N vec B := ⟨P.toPieri, colSet (winFill T C), P.isStdFilling_ext hC⟩
  have hh : ∀ t ≤ N, ∀ c, colH (P.toPieri.mu t) c = P.h t c := fun t ht c => P.colH_toPieri ht c
  set e : ℤ → ℕ := fun c => if 1 ≤ c then 0 else hexp (C c) + hexp (univ : Finset (Fin n))
  have key : pathFam ℤ x = (-1) ^ (∑ c ∈ win T, e c) * psi P C := by
    show pathPoly ℤ P.toPieri.mu N (colSet (winFill T C)) = _
    rw [pathPoly_eq_prod P.toPieri.zero (P.isStdFilling_ext hC) (subset_union_left (s₂ := win T))]
    rw [← prod_subset (subset_union_right (s₁ := colRange P.toPieri.mu N)) ?_]
    · rw [psi, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
      refine prod_congr rfl fun c hc => ?_
      by_cases h1 : 1 ≤ c
      · simp only [e, h1, ↓reduceIte, pow_zero, one_mul, colSet, winFill, hc]
        rw [colK_eq_colS_pos hh h1]
      · simp only [e, h1, ↓reduceIte, colSet, winFill, hc]
        rw [colK_compl hh (by omega), hsg, hsg, ← pow_add]
    · intro c _ hc
      have hconst : ∀ t ≤ N, colH (P.toPieri.mu t) c = colH (P.toPieri.mu 0) c := fun t ht => by
        rw [hh t ht, hh 0 (Nat.zero_le _), P.out t ht c (fun h => hc (Ioo_subset_Icc_self h)), P.zero]
      rw [colK_of_const hconst]
      have hI : colSet (winFill T C) c = ∅ := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hc
        unfold colSet winFill
        simp only [mem_Icc]
        rcases hc with hc | hc
        · simp only [show ¬ (1 ≤ c) by omega, show ¬ (-(T : ℤ) ≤ c) by omega, false_and, ↓reduceIte,
            show c < 0 by omega, compl_univ]
        · simp only [show 1 ≤ c by omega, show ¬ (c ≤ (T : ℤ)) by omega, and_false, ↓reduceIte,
            show ¬ (c < 0) by omega]
      rw [hI]
      simp [st0]
  have hsq : ((-1 : MvPolynomial (ℕ × Fin n) ℤ) ^ (∑ c ∈ win T, e c)) * (-1) ^ (∑ c ∈ win T, e c) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  have hpx : psi P C = (-1) ^ (∑ c ∈ win T, e c) * pathFam ℤ x := by rw [key, ← mul_assoc, hsq, one_mul]
  rw [hpx]
  refine sign_mul_mem ?_ _
  exact Submodule.subset_span ⟨x, rfl⟩

end ToFam

/-! ## The monomials of multidegree `B` and their number -/

section Count

variable {n : ℕ}

/-- **The multidegree** `B` on the letters `0, …, N − 1`. -/
abbrev mdeg (N : ℕ) (B : ℕ → ℕ) : ℕ → ℕ := fun u => if u < N then B u else 0

/-- **The row weight of an exponent is its degree in the letter.** -/
theorem weight_rowW_nat (d : (ℕ × Fin n) →₀ ℕ) (l : ℕ) : Finsupp.weight (LetterFock.rowW ℕ n) d l = ∑ a, d (l, a) := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  simp only [LetterFock.rowW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  have e : ∑ a, d (l, a) = ∑ x ∈ ({l} : Finset ℕ) ×ˢ (univ : Finset (Fin n)), d x := by
    rw [sum_product, sum_singleton]
  rw [e]
  refine sum_subset (fun x hx => ?_) (fun x hx hx' => ?_)
  · rw [mem_filter] at hx
    rw [mem_product, mem_singleton]
    exact ⟨hx.2.symm, mem_univ _⟩
  · rw [mem_product, mem_singleton] at hx
    by_contra h
    exact hx' (mem_filter.2 ⟨Finsupp.mem_support_iff.2 h, hx.1.symm⟩)

/-- **The exponents of multidegree `B`** are the tuples, one per letter `t < N`, of `n` exponents adding up to
`B_t`. -/
def monoEquiv (n N : ℕ) (B : ℕ → ℕ) :
    {d : (ℕ × Fin n) →₀ ℕ | Finsupp.weight (LetterFock.rowW ℕ n) d = mdeg N B} ≃
      ∀ t : Fin N, {f : Fin n → ℕ // ∑ a, f a = B t} where
  toFun d t := ⟨fun a => d.1 (t.val, a), by
    have := congrFun d.2 t.val
    rw [weight_rowW_nat] at this
    simpa [mdeg, t.isLt] using this⟩
  invFun g := ⟨Finsupp.onFinset (range N ×ˢ univ) (fun v => if h : v.1 < N then (g ⟨v.1, h⟩).1 v.2 else 0)
    (fun v hv => by
      rw [mem_product, mem_range]
      by_contra h
      simp only [not_and_or, mem_univ, not_true_eq_false, or_false] at h
      exact hv (dite_eq_right h)), by
    show Finsupp.weight (LetterFock.rowW ℕ n) _ = mdeg N B
    funext l
    rw [weight_rowW_nat]
    simp only [Finsupp.onFinset_apply, mdeg]
    split_ifs with hl
    · exact (g ⟨l, hl⟩).2
    · simp⟩
  left_inv d := by
    apply Subtype.ext
    ext v
    simp only [Finsupp.onFinset_apply]
    split_ifs with hv
    · rfl
    · have := congrFun d.2 v.1
      rw [weight_rowW_nat] at this
      simp only [mdeg, hv, ↓reduceIte, sum_eq_zero_iff, mem_univ, true_implies] at this
      exact (this v.2).symm
  right_inv g := by
    funext t
    apply Subtype.ext
    funext a
    simp

/-- **The number of monomials of multidegree `B`** in `m + 1` coordinates: `∏_{t < N} C(B_t + m, m)`. -/
theorem card_monomials (m N : ℕ) (B : ℕ → ℕ) :
    Nat.card {d : (ℕ × Fin (m + 1)) →₀ ℕ | Finsupp.weight (LetterFock.rowW ℕ (m + 1)) d = mdeg N B} =
      ∏ t ∈ range N, (B t + m).choose m := by
  rw [Nat.card_congr (monoEquiv (m + 1) N B), Nat.card_pi, ← Fin.prod_univ_eq_prod_range (fun t => (B t + m).choose m)]
  refine prod_congr rfl fun t _ => ?_
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype (Fin (m + 1)) (B t)), Nat.card_eq_fintype_card,
    Sym.card_sym_eq_choose, Fintype.card_fin, show m + 1 + B t - 1 = B t + m by omega, Nat.choose_symm_add]

end Count

/-! ## The path family spans the multidegree-`B` polynomials -/

section SpanFam

variable {n N : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **Every monomial of multidegree `B` is a `ℤ`-combination of the path family** (spanning by all path polynomials,
straightening, and the standard ones in the family up to sign). -/
theorem monomial_mem_span_int (hn : 0 < n) {d : (ℕ × Fin n) →₀ ℕ} (hd : ∀ l, ∑ a, d (l, a) = mdeg N B l) :
    (monomial d 1 : MvPolynomial (ℕ × Fin n) ℤ) ∈
      Submodule.span ℤ (Set.range (pathFam ℤ (n := n) (N := N) (vec := vec) (B := B))) := by
  have hT : ∑ s ∈ range N, B s < ∑ s ∈ range N, B s + 1 := Nat.lt_succ_self _
  have h1 := monomial_mem_allSpan (T := ∑ s ∈ range N, B s + 1) (vec := vec) hn hT d hd
  refine (Submodule.span_le.2 ?_ : stdAll n N _ vec B ≤ _) (allSpan_le_stdAll hn hT h1)
  rintro f ⟨Q, C, hC, rfl⟩
  exact Q.psi_mem_span hC

variable (R : Type*) [CommRing R]

/-- **Every monomial of multidegree `B` is an `R`-combination of the path family**, over every commutative ring
(the `ℤ`-combinations mapped by `ℤ → R`, `pathPoly_map`). -/
theorem monomial_mem_span_pathFam (hn : 0 < n) {d : (ℕ × Fin n) →₀ ℕ} (hd : ∀ l, ∑ a, d (l, a) = mdeg N B l) :
    (monomial d 1 : MvPolynomial (ℕ × Fin n) R) ∈
      Submodule.span R (Set.range (pathFam R (n := n) (N := N) (vec := vec) (B := B))) := by
  set f := (MvPolynomial.map (Int.castRingHom R) : MvPolynomial (ℕ × Fin n) ℤ →+* _).toAddMonoidHom.toIntLinearMap
  have h1 := Submodule.mem_map_of_mem (f := f) (monomial_mem_span_int (vec := vec) hn hd)
  rw [Submodule.map_span] at h1
  have himg : f '' Set.range (pathFam ℤ (n := n) (N := N) (vec := vec) (B := B)) =
      Set.range (pathFam R (n := n) (N := N) (vec := vec) (B := B)) := by
    rw [← Set.range_comp]
    congr 1
    funext x
    exact pathPoly_map _ _ _
  have hf : f (monomial d 1) = monomial d 1 := by simp [f, map_monomial]
  rw [himg, hf] at h1
  exact Submodule.span_le_restrictScalars ℤ R _ h1

/-- **The path family spans the multidegree-`B` polynomials** over every commutative ring. -/
theorem mem_span_pathFam (hn : 0 < n) {p : MvPolynomial (ℕ × Fin n) R}
    (hp : p ∈ weightedHomogeneousSubmodule R (LetterFock.rowW ℕ n) (mdeg N B)) :
    p ∈ Submodule.span R (Set.range (pathFam R (n := n) (N := N) (vec := vec) (B := B))) := by
  rw [p.as_sum]
  refine sum_mem fun d hd => ?_
  have hw := hp (mem_support_iff.1 hd)
  have hd' : ∀ l, ∑ a, d (l, a) = mdeg N B l := fun l => by rw [← weight_rowW_nat, hw]
  have e : monomial d (p.coeff d) = p.coeff d • (monomial d 1 : MvPolynomial (ℕ × Fin n) R) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e]
  exact Submodule.smul_mem _ _ (monomial_mem_span_pathFam R hn hd')

end SpanFam

end

end PathSpan

namespace PathBasis

open MvPolynomial Finset PathSpan

noncomputable section

variable (R : Type*) [CommRing R] (m N : ℕ) (vec : ℕ → Bool) (B : ℕ → ℕ)

/-- **The path family in the multidegree-`B` polynomials.** -/
def pathVec (x : PathIdx (m + 1) N vec B) :
    weightedHomogeneousSubmodule R (LetterFock.rowW ℕ (m + 1)) (mdeg N B) :=
  ⟨pathFam R x, x.1.pathPoly_isWH x.2.1⟩

/-- **The path family spans** the multidegree-`B` polynomials (T2 (iii), spanning). -/
theorem pathVec_span : ⊤ ≤ Submodule.span R (Set.range (pathVec R m N vec B)) := by
  intro p _
  have h := mem_span_pathFam R (vec := vec) (Nat.succ_pos m) p.2
  have e : Set.range (pathFam R (n := m + 1) (N := N) (vec := vec) (B := B)) =
      (weightedHomogeneousSubmodule R (LetterFock.rowW ℕ (m + 1)) (mdeg N B)).subtype ''
        Set.range (pathVec R m N vec B) := by
    rw [← Set.range_comp]
    rfl
  rw [e, Submodule.span_image, Submodule.mem_map] at h
  obtain ⟨q, hq, hqp⟩ := h
  rwa [show q = p from Subtype.ext hqp] at hq

/-- **The family is finite.** -/
instance instFinitePathIdx : Finite (PathIdx (m + 1) N vec B) :=
  have : ∀ P : PieriPath (m + 1) N vec B, Finite {I // IsStdFilling (P.mu N) I} :=
    fun P => (card_stdFilling (P.antitone N)).1
  inferInstance

/-- **The path family is linearly independent** (T2 (i)): it spans a free module whose rank is its number of
members (`card_pathIdx`, `card_monomials`), and a surjective linear map between free modules of the same finite rank
over a commutative ring is injective (Orzech). -/
theorem pathVec_linearIndependent : LinearIndependent R (pathVec R m N vec B) := by
  set M := weightedHomogeneousSubmodule R (LetterFock.rowW ℕ (m + 1)) (mdeg N B)
  set s := {d : (ℕ × Fin (m + 1)) →₀ ℕ | Finsupp.weight (LetterFock.rowW ℕ (m + 1)) d = mdeg N B}
  have hM : M = restrictSupport R s := weightedHomogeneousSubmodule_eq_finsupp_supported R _ _
  let b : Module.Basis s R M := (basisRestrictSupport R s).map (LinearEquiv.ofEq _ _ hM.symm)
  have : ∀ t : Fin N, Finite {f : Fin (m + 1) → ℕ // ∑ a, f a = B t} :=
    fun t => Finite.of_equiv _ (Sym.equivNatSumOfFintype (Fin (m + 1)) (B t))
  have : Finite s := Finite.of_equiv _ (monoEquiv (m + 1) N B).symm
  have hcard : Nat.card s = Nat.card (PathIdx (m + 1) N vec B) := by
    rw [card_monomials, card_pathIdx]
  have : Fintype s := Fintype.ofFinite s
  have : Fintype (PathIdx (m + 1) N vec B) := Fintype.ofFinite _
  obtain ⟨σ⟩ : Nonempty (PathIdx (m + 1) N vec B ≃ s) :=
    Fintype.card_eq.1 (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact hcard.symm)
  let i : (PathIdx (m + 1) N vec B →₀ R) →ₗ[R] M := b.repr.symm.toLinearMap ∘ₗ (Finsupp.domLCongr σ).toLinearMap
  have hi : Function.Injective i := b.repr.symm.injective.comp (Finsupp.domLCongr σ).injective
  have : Module.Finite R M := Module.Finite.of_basis b
  have hf : Function.Surjective (Finsupp.linearCombination R (pathVec R m N vec B)) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact eq_top_iff.2 (pathVec_span R m N vec B)
  exact OrzechProperty.injective_of_surjective_of_injective i _ hi hf

/-- **(T2) The path basis**: over every commutative ring `R`, the path polynomials `Ψ(P, I)` (`pathFam`, a Pieri
path and a standard filling of its end weight) form an `R`-basis of the polynomials of multidegree `B` in `m + 1`
coordinates. -/
def pathFam_basis : Module.Basis (PathIdx (m + 1) N vec B) R
    (weightedHomogeneousSubmodule R (LetterFock.rowW ℕ (m + 1)) (mdeg N B)) :=
  Module.Basis.mk (pathVec_linearIndependent R m N vec B) (pathVec_span R m N vec B)

/-- **The vectors of the path basis are the path polynomials.** -/
theorem pathFam_basis_apply (x : PathIdx (m + 1) N vec B) :
    (pathFam_basis R m N vec B x : MvPolynomial (ℕ × Fin (m + 1)) R) = pathFam R x := by
  rw [pathFam_basis, Module.Basis.mk_apply]
  rfl

end

end PathBasis
