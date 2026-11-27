import SourceCore

/-!
# The one-sided side of the second local theorem: interfaces, budgets, labels, other rows (L6 N8, C5)

The pieces of N8's one-sided realisation (C5, C6) that do not need the twisted-degree calculus: the gap-0 pairs and
the two toolkit interfaces through which the one-sided realisation reaches the unwritten toolkit, the budget
determinants a one-sided factor carries, the key presentation of digit labels, and the other-row degree bound.

**Conventions** (those of `SourceKeys`, `SourceCore` and `SymbolData`): the segment ring has letters `ℤ` (lifted
positions) with flags `vecZ`, plane polynomials in `r` columns, normal ones in `K` columns; `val_S`, `top_S` are
`SymbolData`'s; `segPush j` the Frobenius push of the segment `j`; `Q = p^{G′}`.

**Definitions.**
* `GapZero R F TT j A G`: `A` plane on `seg j`, `G` normal on `late j`, and `M` with `top_{≤x}G ≤ M_x ≤ val_{<x}A`
  (`x` even), `top_{<x}G ≤ M_x ≤ val_{≤x}A` (`x` odd) at every late `x` (gap `0`, no threshold, no degree bound).
* **Interface** `GapZeroKeyed W ι σ ϖ F TT Q` (toolkit): the push of every letter-bihomogeneous gap-0 pair is
  key-presentable (the hard capacity span of gap-0 pairs by plane-dominant pair-path bideterminants over `O`, and the
  rank-`r` twisted column states as keys).
* **Interface** `DetDiv R` (toolkit, over a field `R`): `θ ≤ val_S G` and `Σ_{even y ∈ S, y ∉ A} deg_y G < θ` give
  `det(rows A)^{θ − degOther} ∣ G`; and `G = det^m·H ⇒ val_{S′}G ≤ val_{S′}H + m`.
* `rowDet(j, x)` (the rows of `x`), `prevFrameDet(j)` (the frame `j − 1`), `budgetDet_j = ∏_{x ∈ late j}
  rowDet(j, x)^{m₁}·prevFrameDet(j)^{m₂}`.

**Main results.**
* *Labels* (`label_keyPres`, 5.5): a digit label times `labelBudget = budgetProd^{kQ}` is key-presentable: per top at
  most `k` scaled columns, each of exponent `≤ Q` (`label_lt`: every top is the position of a late letter,
  `exists_late`, whose push is `< G′`, `push_lt`), so `SourceCore.monomial_conversion` applies with `ν = kQ`.
* *Other rows* (`otherDeg_le`, 5.2): for `13 ≤ p`, `a ≤ deg ≤ 2a` on the tops and `dd ≤ 1.01·pdeg` before `f(j, 0)`,
  the even letters of `seg j` before the anchor of a late `x` carry `Σ dd_y ≤ B(j, x)/80`: each has
  `dd_y ≤ 2.02·B·p^{−(anchor − y)}`, the `anchor − y` are distinct positive even numbers, and the geometric series
  gives `2.02/(p² − 1) ≤ 1/80`.

**Not here** (left open, see below). The budget extraction (5.3), the pushed budgets (5.4) and the one-sided
realisation (5.6). The extraction and the realisation read `val_S`/`top_S` through the injective coefficient map
`O → Kf` (to apply `DetDiv Kf`) and through letter-degree components (to split good products into bihomogeneous
ones): both are the toolkit's `val_S` calculus (`SymbolData`: "the calculus of `val_S` and `top_S` … is the
toolkit's"), not yet written.

**Readings of the planning statements.** `otherDeg_le` does not need `n′` even (the spec's statement lists it).
-/

namespace SourceOneSided

open MvPolynomial Finset LetterFock LocalOrbit SymbolData InertModel SourceKeys SourceCore

open scoped Matrix

noncomputable section

variable {W Qq O Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {jW : W →+* O} {ϖ : O} {p n' r K : ℕ}

/-! ## Gap-0 pairs and the two toolkit interfaces -/

section Interfaces

variable [NeZero n'] [NeZero r] [NeZero K]

/-- **A gap-0 pair** of the segment `j`: `A` plane on `seg j`, `G` normal on `late j`, with a witness `M` of
`top(G) ≤ M ≤ val(A)` at every late letter (no threshold, no degree bound). -/
def GapZero (R : Type*) [CommRing R] (F : FrameSys n' r) (TT : Finset (Fin n')) (j : ℤ)
    (A : MvPolynomial (ℤ × Fin r) R) (G : MvPolynomial (ℤ × Fin K) R) : Prop :=
  A ∈ supported R {v | v.1 ∈ F.seg TT j} ∧ G ∈ supported R {v | v.1 ∈ F.late TT j} ∧
    ∃ M : ℤ → ℤ, ∀ x ∈ F.late TT j,
      (Even x → topS vecZ (Set.Iic x) G ≤ (M x : WithBot ℤ) ∧ ((M x : ℤ) : WithTop ℤ) ≤ valS vecZ (Set.Iio x) A) ∧
      (¬ Even x → topS vecZ (Set.Iio x) G ≤ (M x : WithBot ℤ) ∧ ((M x : ℤ) : WithTop ℤ) ≤ valS vecZ (Set.Iic x) A)

variable (W ι σ ϖ) in
/-- **Interface `GapZeroKeyed`** (toolkit: the span of gap-0 pairs by plane-dominant pair-path bideterminants over
`O`, and the rank-`r` twisted column states as keys): the push of a letter-bihomogeneous gap-0 pair is
key-presentable. Content: a gap-0 pair is an `O`-combination of plane-dominant pair-path bideterminants (the hard
capacity span over `O`, mixed letters), and the push of such a bideterminant is `ϖ^{−o}` times a product of leading
forms of the rank-`r` twisted column states (order `≥` cost at every `g′`, congruence at `g = 1`, cost
`≤ 2p^{z_j − (first letter)} ≤ 2Q`) — the rank-`r` version of `TwistedDegree`'s `twCol_ord`/`twCol_cong`. -/
def GapZeroKeyed (F : FrameSys n' r) (TT : Finset (Fin n')) (Q : ℕ) : Prop :=
  ∀ (j : ℤ) (A : MvPolynomial (ℤ × Fin r) O) (G : MvPolynomial (ℤ × Fin K) O) (d' d'' : ℤ → ℕ),
    GapZero O F TT j A G → IsWeightedHomogeneous (LetterFock.rowW ℤ r) A d' →
      IsWeightedHomogeneous (LetterFock.rowW ℤ K) G d'' →
      ∃ o, KeyPres W ι σ ϖ TT Q o (MvPolynomial.map (algebraMap O Kf) (F.segPush O p j (planeEmb O A * normalEmb O G)))

end Interfaces

/-- **Interface `DetDiv`** (toolkit, C5 over a field): if `θ ≤ val_S G` and the degree of `G` in the even letters of
`S` outside `A` is `< θ`, the `(θ − degOther)`-th power of the determinant of the rows `A` divides `G`; dividing by a
determinant power lowers every `val_{S′}` by at most the exponent. -/
def DetDiv (R : Type*) [Field R] : Prop :=
  ∀ (r : ℕ) [NeZero r] (S : Set ℤ) (A : Fin r → ℤ), Function.Injective A → (∀ l, A l ∈ S ∧ Even (A l)) →
    (∀ (d : ℤ → ℕ) (G : MvPolynomial (ℤ × Fin r) R), IsWeightedHomogeneous (LetterFock.rowW ℤ r) G d →
      ∀ θ : ℤ, (θ : WithTop ℤ) ≤ valS vecZ S G →
        ((∑ᶠ y ∈ {y | y ∈ S ∧ Even y ∧ y ∉ Set.range A}, d y : ℕ) : ℤ) < θ →
        (Matrix.of fun l c : Fin r => (X (A l, c) : MvPolynomial (ℤ × Fin r) R)).det ^
          (θ - ∑ᶠ y ∈ {y | y ∈ S ∧ Even y ∧ y ∉ Set.range A}, (d y : ℤ)).toNat ∣ G) ∧
    ∀ (G H : MvPolynomial (ℤ × Fin r) R) (m : ℕ),
      G = (Matrix.of fun l c : Fin r => (X (A l, c) : MvPolynomial (ℤ × Fin r) R)).det ^ m * H →
      ∀ S' : Set ℤ, valS vecZ S' G ≤ valS vecZ S' H + ((m : ℤ) : WithTop ℤ)

/-! ## The budget determinants -/

section Budget

variable [NeZero n'] [NeZero r]

/-- **The row determinant** `rowDet(j, x)`: the plane determinant of the rows of `x`, in the segment ring. -/
def rowDet (R : Type*) [CommRing R] (F : FrameSys n' r) (TT : Finset (Fin n')) (j x : ℤ) :
    MvPolynomial (ℤ × Fin r) R :=
  (Matrix.of fun l c : Fin r => X (F.rows TT j x l, c)).det

/-- **`prevFrameDet(j)`**: the plane determinant of the frame `j − 1`, in the segment ring. -/
def prevFrameDet (R : Type*) [CommRing R] (F : FrameSys n' r) (j : ℤ) : MvPolynomial (ℤ × Fin r) R :=
  (Matrix.of fun l c : Fin r => X (F.f (j - 1) l, c)).det

/-- **`Dv_j = ∏_{x ∈ late j} rowDet(j, x)^{m₁}·prevFrameDet(j)^{m₂}`**, the budget a one-sided factor carries. -/
def budgetDet (R : Type*) [CommRing R] (F : FrameSys n' r) (TT : Finset (Fin n')) (j : ℤ) (m₁ m₂ : ℕ) :
    MvPolynomial (ℤ × Fin r) R :=
  (∏ x ∈ F.late TT j, rowDet R F TT j x ^ m₁) * prevFrameDet R F j ^ m₂

end Budget

/-! ## Labels (N8 C5) -/

section Labels

variable [NeZero n'] [NeZero r]

/-- **Every top is the position of a late letter** of a segment `j < J` (the late letters tile `TT`). -/
theorem exists_late {TT : Finset (Fin n')} {F : FrameSys n' r} {L₁ : ℕ} (hF : F.Proper TT L₁) {s : Fin n'}
    (hs : s ∈ TT) : ∃ j < F.J, ∃ x ∈ F.late TT j, posOf n' x = s := by
  classical
  have h := hF.sum_late (M := ℕ) (fun t => if t = s then 1 else 0)
  rw [sum_ite_eq' TT s (fun _ => 1), ite_eq_left hs] at h
  obtain ⟨j, hj, hj'⟩ := exists_ne_zero_of_sum_ne_zero (h.symm ▸ one_ne_zero)
  obtain ⟨x, hx, hx'⟩ := exists_ne_zero_of_sum_ne_zero hj'
  exact ⟨j, mem_range.1 hj, x, hx, by simpa using hx'⟩

/-- **Pushes in a bounded segment are below `G′`.** -/
theorem push_lt {TT : Finset (Fin n')} {F : FrameSys n' r} {G' N₁ : ℕ} (hb : F.Bounded TT G' N₁) {j x : ℤ}
    (hx : x ∈ F.seg TT j) : F.push j x < G' := by
  have h1 := mem_Icc.1 (mem_filter.1 hx).1
  have h2 := hb.span j
  rw [FrameSys.push]
  omega

/-- **Digit labels are bounded by `Q = p^{G′}`** at every position and column. -/
theorem label_lt {TT : Finset (Fin n')} {F : FrameSys n' r} {L₁ G' N₁ : ℕ} (hF : F.Proper TT L₁)
    (hb : F.Bounded TT G' N₁) (hp : 1 ≤ p) {k : ℕ} {μ : Fin n' × Fin k →₀ ℕ} (hμ : F.IsDigitLabel TT p μ)
    (s : Fin n') (c : Fin k) : μ (s, c) ≤ p ^ G' := by
  by_cases hs : s ∈ TT
  · obtain ⟨j, -, x, hx, rfl⟩ := exists_late hF hs
    have h1 := hμ.2 j x hx c
    have h2 : p ^ F.push j x ≤ p ^ G' := Nat.pow_le_pow_right hp (push_lt hb (mem_filter.1 hx).1).le
    omega
  · by_contra h
    exact hs (hμ.1 (s, c) (Finsupp.mem_support_iff.2 (by omega)))

variable [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O]

/-- **Labels**: a digit label times the label budget is key-presentable (per top at most `k` scaled columns, each of
exponent `≤ Q`, so the conversion with `ν = kQ` applies). -/
theorem label_keyPres (hU : Unram p n' W Qq O Kf ι σ jW ϖ) (hn : Even n') (hp : 2 ≤ p) {TT : Finset (Fin n')}
    {F : FrameSys n' r} {L₁ G' N₁ : ℕ} (hF : F.Proper TT L₁) (hb : F.Bounded TT G' N₁)
    (μ : Fin n' × Fin (r + K) →₀ ℕ) (hμ : F.IsDigitLabel TT p μ) :
    KeyPres W ι σ ϖ TT (p ^ G') (nd r (vecF n') μ) (monomial μ (1 : Kf) * labelBudget F TT Kf p K (p ^ G')) := by
  obtain ⟨-, -, ⟨-, -, hBnd⟩, -⟩ := explicit_int (Kf := Kf) (ϖ := ϖ) (p := p) (K := K) hn hF
  refine ⟨hom_iff.2 ?_, ?_⟩
  · have h := (isWeightedHomogeneous_monomial (R := Kf) (scW r) μ 1 rfl).mul ((hom_iff.1 hBnd).pow ((r + K) * p ^ G'))
    rw [smul_zero, add_zero] at h
    exact h
  · rw [labelBudget, ← smul_mul_assoc]
    refine monomial_conversion hU hn hp hF (Nat.one_le_pow _ _ (by omega)) μ hμ.1 _ fun s => ?_
    calc piDeg r (vecF n') μ s ≤ ∑ c : Fin (r + K), p ^ G' :=
          sum_le_sum fun c _ => by
            split_ifs
            · exact label_lt hF hb (by omega) hμ s c
            · exact Nat.zero_le _
      _ = (r + K) * p ^ G' := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

end Labels

/-! ## The other-row bound (N8 C5) -/

section OtherRows

variable [NeZero n'] [NeZero r]

/-- **Other-row degree bound**: for letter degrees `dd ≤ 1.01·pdeg` at the W- and loose letters, the even letters of
`seg j` before the anchor of a late `x` (the even letters before `x` other than its rows) carry total degree
`≤ B(j, x)/80`: each has `dd_y ≤ 2.02·B·p^{−(anchor − y)}`, the `anchor − y` are distinct positive even numbers, and
`2.02/(p² − 1) ≤ 1/80` for `p ≥ 13`. -/
theorem otherDeg_le {TT : Finset (Fin n')} {F : FrameSys n' r} {L₁ : ℕ} (hF : F.Proper TT L₁) (hp : 13 ≤ p)
    {deg : Fin n' → ℕ} {a : ℝ} (ha : ∀ t ∈ TT, a ≤ deg t ∧ (deg t : ℝ) ≤ 2 * a) {j : ℤ}
    (dd : ℤ → ℕ) (hdd : ∀ x ∈ F.seg TT j, x < F.f j 0 → (dd x : ℝ) ≤ F.pdeg p deg j x + F.pdeg p deg j x / 100)
    {x : ℤ} (hx : x ∈ F.late TT j) :
    (∑ y ∈ (F.seg TT j).filter (fun y => Even y ∧ y < F.anchor TT j x), (dd y : ℝ)) ≤ F.B TT p deg j x / 80 := by
  classical
  set A := F.anchor TT j x with hA
  have hAseg := hF.anchor_mem_seg hx
  obtain ⟨mA, hmA⟩ : Even A := (mem_filter.1 (hF.anchor_mem_evBefore hx)).2.1
  have hAf := hF.anchor_lt_f hx
  have hAz : A ≤ F.z j := (mem_Icc.1 (mem_filter.1 hAseg).1).2
  have hAtop : posOf n' A ∈ TT := (mem_filter.1 hAseg).2
  set S := (F.seg TT j).filter (fun y => Even y ∧ y < A) with hS
  have hpR : (13 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  set q : ℝ := 1 / (p : ℝ) ^ 2 with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one (by positivity)]; nlinarith
  set B := F.B TT p deg j x with hBdef
  have hB : B = deg (posOf n' A) / (p : ℝ) ^ F.push j A := rfl
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  set kf : ℤ → ℕ := fun y => ((A - y) / 2).toNat with hkf
  have hmem : ∀ y ∈ S, y ∈ F.seg TT j ∧ (∃ m, y = m + m) ∧ y < A := fun y hy => by
    obtain ⟨h1, ⟨m, hm⟩, h3⟩ := mem_filter.1 hy
    exact ⟨h1, ⟨m, hm⟩, h3⟩
  have hbound : ∀ y ∈ S, (dd y : ℝ) ≤ (202 / 100) * B * q ^ kf y := by
    intro y hy
    obtain ⟨hyseg, ⟨m, hm⟩, hyA⟩ := hmem y hy
    have h1 := hdd y hyseg (by linarith)
    have hytop : posOf n' y ∈ TT := (mem_filter.1 hyseg).2
    have hdeg : (deg (posOf n' y) : ℝ) ≤ 2 * deg (posOf n' A) := by
      linarith [(ha _ hytop).2, (ha _ hAtop).1]
    have hpush : F.push j y = F.push j A + 2 * kf y := by
      simp only [FrameSys.push, hkf]
      omega
    have hpd : F.pdeg p deg j y ≤ 2 * B * q ^ kf y := by
      rw [FrameSys.pdeg, hpush, pow_add, pow_mul, hB, hq, one_div_pow]
      rw [show 2 * ((deg (posOf n' A) : ℝ) / (p : ℝ) ^ F.push j A) * (1 / ((p : ℝ) ^ 2) ^ kf y) =
          2 * deg (posOf n' A) / ((p : ℝ) ^ F.push j A * ((p : ℝ) ^ 2) ^ kf y) by field_simp]
      exact div_le_div_of_nonneg_right hdeg (by positivity)
    nlinarith
  have hinj : Set.InjOn kf S := fun y hy y' hy' h => by
    obtain ⟨-, ⟨m, hm⟩, hyA⟩ := hmem y hy
    obtain ⟨-, ⟨m', hm'⟩, hyA'⟩ := hmem y' hy'
    simp only [hkf] at h
    omega
  have hpos : ∀ y ∈ S, 1 ≤ kf y := fun y hy => by
    obtain ⟨-, ⟨m, hm⟩, hyA⟩ := hmem y hy
    simp only [hkf]
    omega
  set N := (S.image kf).sup id with hN
  have hsub : S.image kf ⊆ Ico 1 (N + 1) := fun k hk => by
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hk
    have := le_sup (f := id) hk
    exact mem_Ico.2 ⟨hpos y hy, by simp only [id] at this; omega⟩
  have hgeom : ∑ y ∈ S, q ^ kf y ≤ q / (1 - q) := by
    rw [← sum_image hinj]
    calc ∑ k ∈ S.image kf, q ^ k ≤ ∑ k ∈ Ico 1 (N + 1), q ^ k :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => pow_nonneg hq0 _
      _ ≤ q ^ 1 / (1 - q) := geom_sum_Ico_le_of_lt_one hq0 hq1
      _ = q / (1 - q) := by rw [pow_one]
  have hqq : q / (1 - q) ≤ 1 / 168 := by
    have hp2 : (169 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    have hq' : q ≤ 1 / 169 := by rw [hq]; exact one_div_le_one_div_of_le (by norm_num) hp2
    rw [div_le_div_iff₀ (sub_pos.2 hq1) (by norm_num)]
    linarith
  calc ∑ y ∈ S, (dd y : ℝ) ≤ ∑ y ∈ S, (202 / 100) * B * q ^ kf y := sum_le_sum hbound
    _ = (202 / 100) * B * ∑ y ∈ S, q ^ kf y := by rw [mul_sum]
    _ ≤ (202 / 100) * B * (q / (1 - q)) := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ ≤ (202 / 100) * B * (1 / 168) := mul_le_mul_of_nonneg_left hqq (by positivity)
    _ ≤ B / 80 := by nlinarith

end OtherRows

end

end SourceOneSided
