import TwistedDegree
import WeylCount

/-!
# Pieri paths, standard fillings and the path polynomials (T2: objects, columns, count)

The objects of the path basis T2 of the L5/L6 toolkit, with their columns exposed and their count: Pieri paths of
dominant weights, standard fillings of the end weight, and the path polynomials `Ψ(P, I) = ∏_c K_c(I(c))` built from
the column states `K_c = colK` of `TwistedDegree` (reused, not redefined).

**Conventions** (those of `LetterFock` and `TwistedDegree`). Letters are indexed by `ℕ` (the letters `0, …, N − 1`
are used), each with `n` coordinates; `vec t` says whether the letter `t` is a vector letter, `B t` is its degree, and
the polynomials live in `MvPolynomial (ℕ × Fin n) R`, the variable `(t, a)` being the coordinate `a` of the letter `t`.
A weight is `μ : Fin n → ℤ`, dominant when antitone; the height of the column `c ∈ ℤ` is `colH μ c = #{a : c ≤ μ_a}`.
`μ/ν` is a *horizontal `b`-strip* (`IsStrip ν μ b`) when `ν ≤ μ`, `μ_{a+1} ≤ ν_a` and `|μ| = |ν| + b`; then both are
dominant and every column height grows by at most one, exactly `b` of them by one (`IsStrip.colH_le`,
`IsStrip.card_change`). A *Pieri path* of type `(vec, B)` (`PieriPath n N vec B`) is `mu : ℕ → Fin n → ℤ` with
`mu 0 = 0`, `mu (t + 1)/mu t` a horizontal `B_t`-strip at a vector letter and `mu t/mu (t + 1)` one at a covector letter
(`IsStep`), constant after `N`. A *standard filling* of `λ` (`IsStdFilling`) is `I : ℤ → Finset (Fin n)` whose columns
`col(c) = I(c)` (`c ≥ 1`), `I(c)ᶜ` (`c ≤ 0`) (`colSet`) have `colH λ c` elements and weakly increasing rows,
`#{x ∈ col(c + 1) : x < t} ≤ #{x ∈ col(c) : x < t}` for all `c` and `t ∈ ℕ` (`IsStdCol`; the spec's `x ≤ t` is
`x < t + 1`). So `|I(c)| = colH λ c` for `c ≥ 1` and `n − colH λ c` for `c ≤ 0`, and `I(c) = ∅` outside the column range
(`eq_empty_of_notMem`). The path polynomial (`pathPoly`) is `∏_{c ∈ colRange} colK R μ c N (I c)`, the column range
being `[−T, T]`, `T = Σ_{t ≤ N} Σ_a |μ_t(a)|`; the path family is `pathFam`, indexed by `PathIdx` (a path and a standard
filling of its end weight).

**Main results.**
* *The columns* (L5's C3, L6's R-4): `K_c(J)` is multilinear, of degree `1` in the letters changing the height of the
  column `c` and `0` in the others (`colK_isWH`, T9f's (deg) at `p = 1`); each letter `t` changes exactly `B_t` columns
  (`PieriPath.card_change`), so `Ψ(P, I)` has multidegree `B` (`PieriPath.pathPoly_isWH`); the heights move by at most
  one per letter, up at vector letters, down at covector letters (`PieriPath.colH_step`), so the columns `c ≥ 1` satisfy
  T9f's `ColCond` (`PieriPath.colCond`); `Ψ(P, I)` is the product over any window containing the column range
  (`pathPoly_eq_prod`) and is defined over `ℤ` (`pathPoly_map`). The canonical filling (`canFill`) is standard
  (`isStdFilling_canFill`).
* *The count* (T2 (ii)): the standard fillings of a dominant `λ` number `dimW n λ` (`card_stdFilling`), and in `m + 1`
  coordinates `Σ_P dimW(μ_N) = ∏_{t < N} C(B_t + m, m)` (`sum_dimW_paths`), so the pairs (path, standard filling)
  number `∏_{t < N} C(B_t + m, m)` (`card_pathIdx`), the number of monomials of multidegree `B`.

**The routes.** The paths are enumerated letter by letter (`pathSet`, `nextW`, `mem_pathSet`, `sum_pathSet_succ`), and
Pieri's count `dimW_mul_choose` of `WeylCount` sums the next weights: at a vector letter they are `WeylCount.strip`
(`nextW_true`); at a covector letter the duality `ν ↦ −ν ∘ rev` (`dualW`) exchanges the two kinds of strips
(`isStrip_dualW`) and preserves `dimW` (`dimW_dual`). The fillings are counted by the Gelfand–Tsetlin recursion
`dimW_{n+1}(λ) = Σ_{κ ≺ λ} dimW_n(κ)` (the definition of `dimW`): removing the largest entry `n` (`trunc`) leaves a
standard system of the shape `κ` with `κ_i = λ_{i+1} + #{c ∈ (λ_{i+1}, λ_i] : i + 1 ≤ |col(c) ∖ n|}` (`tshape`), whose
heights are the truncated column sizes (`colH_tshape`: the tall truncated columns form an initial segment of each
interval, `mem_filter_Ioc_iff`), and `κ ≺ λ`; conversely `n` is added where `λ` is taller than `κ` (`grow`), and
dominant weights are determined by their heights (`eq_of_colH_eq`), so the two are inverse (`gtEquiv`).

**Not here: the basis statement** (T2 (i), (iii): `{Ψ(P, I)}` is an `R`-basis of the multidegree-`B` polynomials over
every commutative ring). It is true on every case tested (unimodular coefficient matrices, mixed letters, `n ≤ 3`), but
it is not a leading-term statement: for three vector letters of degree one in two coordinates no monomial order gives
distinct leading terms (the four single-monomial elements force `X₀₀X₁₁ > X₀₁X₁₀` and `X₀₁X₁₀ > X₀₀X₁₁` after
cancelling a common factor). The straightening of a non-standard `Ψ(P, J)` produces the same path with standard
fillings and paths dominated by `P` prefix by prefix with strictly lower end weight, so a proof needs a straightening
law for mixed column states (a Cauchy-type filtration), which is not done.
-/

namespace PathBasis

open MvPolynomial Finset TwistedDegree LetterFock WeylCount

noncomputable section

/-! ## Horizontal strips -/

section Strip

variable {n : ℕ}

/-- **A horizontal strip** `μ/ν` of size `b`: `ν ≤ μ`, `μ_{a+1} ≤ ν_a` and `|μ| = |ν| + b`. -/
def IsStrip (ν μ : Fin n → ℤ) (b : ℕ) : Prop :=
  (∀ a, ν a ≤ μ a) ∧ (∀ a a' : Fin n, a.val + 1 = a'.val → μ a' ≤ ν a) ∧ ∑ a, μ a = ∑ a, ν a + b

/-- **Both ends of a strip are dominant**: `ν_{a+1} ≤ μ_{a+1} ≤ ν_a ≤ μ_a`. -/
theorem IsStrip.antitone {ν μ : Fin n → ℤ} {b : ℕ} (h : IsStrip ν μ b) : Antitone ν ∧ Antitone μ := by
  cases n with
  | zero => exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  | succ n =>
    have hs : ∀ i : Fin n, μ i.succ ≤ ν i.castSucc := fun i => h.2.1 _ _ (by simp)
    exact ⟨Fin.antitone_iff_succ_le.2 fun i => (h.1 _).trans (hs i),
      Fin.antitone_iff_succ_le.2 fun i => (hs i).trans (h.1 _)⟩

/-- **A strip changes a column height by at most one.** -/
theorem IsStrip.colH_le {ν μ : Fin n → ℤ} {b : ℕ} (h : IsStrip ν μ b) (c : ℤ) :
    colH ν c ≤ colH μ c ∧ colH μ c ≤ colH ν c + 1 := by
  refine ⟨colH_mono h.1 c, ?_⟩
  set D := univ.filter fun a => c ≤ μ a ∧ ν a < c
  have hD : D.card ≤ 1 := by
    refine Finset.card_le_one.2 fun a ha a' ha' => ?_
    simp only [D, mem_filter, mem_univ, true_and] at ha ha'
    by_contra hne
    have key : ∀ a a' : Fin n, a < a' → c ≤ μ a' → ν a < c → False := by
      intro a a' hlt h1 h2
      have hpos : 1 ≤ a'.val := by have := Fin.lt_def.1 hlt; omega
      have h3 := h.2.1 ⟨a'.val - 1, by omega⟩ a' (by simp; omega)
      have h4 := h.antitone.1 (show a ≤ ⟨a'.val - 1, by omega⟩ from Fin.le_def.2 (by
        have := Fin.lt_def.1 hlt; simp; omega))
      linarith
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key a a' hlt ha'.1 ha.2
    · exact key a' a hlt ha.1 ha'.2
  have hsub : univ.filter (fun a => c ≤ μ a) ⊆ univ.filter (fun a => c ≤ ν a) ∪ D := by
    intro a ha
    simp only [D, mem_filter, mem_univ, true_and, mem_union] at ha ⊢
    by_cases hν : c ≤ ν a
    · exact Or.inl hν
    · exact Or.inr ⟨ha, by omega⟩
  calc colH μ c ≤ (univ.filter (fun a => c ≤ ν a) ∪ D).card := card_le_card hsub
    _ ≤ colH ν c + D.card := card_union_le _ _
    _ ≤ colH ν c + 1 := by omega

/-- **The number of `c ∈ (L, U]` with `c ≤ x`** is `x − L` for `L ≤ x ≤ U`. -/
theorem card_filter_Ioc_le {L U x : ℤ} (hU : x ≤ U) :
    ((Ioc L U).filter fun c => c ≤ x).card = (x - L).toNat := by
  have e : (Ioc L U).filter (fun c => c ≤ x) = Ioc L x := by
    ext c
    simp only [mem_filter, mem_Ioc]
    omega
  rw [e, Int.card_Ioc]

/-- **The heights of a strip** `μ/ν` inside a window `(L, U]` containing both: they grow by `|μ| − |ν|` in total. -/
theorem sum_colH_sub {ν μ : Fin n → ℤ} (hνμ : ∀ a, ν a ≤ μ a) {L U : ℤ} (hL : ∀ a, L ≤ ν a)
    (hU : ∀ a, μ a ≤ U) : ∑ c ∈ Ioc L U, ((colH μ c : ℤ) - colH ν c) = ∑ a, μ a - ∑ a, ν a := by
  have e : ∀ (w : Fin n → ℤ) (c : ℤ), (colH w c : ℤ) = ∑ a, if c ≤ w a then 1 else 0 := fun w c => by
    rw [colH, Finset.card_filter]
    push_cast
    rfl
  simp_rw [e, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ c ∈ Ioc L U, (if c ≤ μ a then (1 : ℤ) else 0) = μ a - L := by
    rw [Finset.sum_boole, card_filter_Ioc_le (hU a)]
    have := (hL a).trans (hνμ a)
    omega
  have h2 : ∑ c ∈ Ioc L U, (if c ≤ ν a then (1 : ℤ) else 0) = ν a - L := by
    rw [Finset.sum_boole, card_filter_Ioc_le ((hνμ a).trans (hU a))]
    have := hL a
    omega
  rw [h1, h2]
  ring

/-- **A strip of size `b` changes exactly `b` column heights**, all inside any window `(L, U]` containing both
weights. -/
theorem IsStrip.card_change {ν μ : Fin n → ℤ} {b : ℕ} (h : IsStrip ν μ b) {L U : ℤ} (hL : ∀ a, L ≤ ν a)
    (hU : ∀ a, μ a ≤ U) : ((Ioc L U).filter fun c => colH ν c ≠ colH μ c).card = b := by
  have hs := sum_colH_sub h.1 hL hU
  rw [h.2.2] at hs
  have e : ∀ c, ((colH μ c : ℤ) - colH ν c) = if colH ν c ≠ colH μ c then 1 else 0 := fun c => by
    have := h.colH_le c
    split_ifs with hc <;> omega
  simp_rw [e] at hs
  rw [Finset.sum_boole] at hs
  omega

end Strip

/-! ## Pieri paths -/

section Path

variable {n : ℕ}

/-- **One letter of a Pieri path**: a vector letter (`v = true`) adds a horizontal `b`-strip, a covector letter
removes one. -/
def IsStep (v : Bool) (b : ℕ) (ν μ : Fin n → ℤ) : Prop := if v then IsStrip ν μ b else IsStrip μ ν b

/-- **The column heights along a step**: they grow by at most one at a vector letter and drop by at most one at a
covector letter. -/
theorem IsStep.colH {v : Bool} {b : ℕ} {ν μ : Fin n → ℤ} (h : IsStep v b ν μ) (c : ℤ) :
    (v = true → TwistedDegree.colH ν c ≤ TwistedDegree.colH μ c ∧
      TwistedDegree.colH μ c ≤ TwistedDegree.colH ν c + 1) ∧
    (v = false → TwistedDegree.colH μ c ≤ TwistedDegree.colH ν c ∧
      TwistedDegree.colH ν c ≤ TwistedDegree.colH μ c + 1) := by
  cases v
  · exact ⟨fun h' => absurd h' (by simp), fun _ => (show IsStrip μ ν b from h).colH_le c⟩
  · exact ⟨fun _ => (show IsStrip ν μ b from h).colH_le c, fun h' => absurd h' (by simp)⟩

/-- **The weights after a step stay dominant.** -/
theorem IsStep.antitone {v : Bool} {b : ℕ} {ν μ : Fin n → ℤ} (h : IsStep v b ν μ) : Antitone μ := by
  cases v
  · exact (show IsStrip μ ν b from h).antitone.1
  · exact (show IsStrip ν μ b from h).antitone.2

/-- **A Pieri path** of type `(vec, B)` with `N` letters in `n` coordinates: weights `μ_0 = 0, μ_1, …, μ_N`
(`mu t` after `t` letters), one step per letter, constant after `N`. -/
structure PieriPath (n N : ℕ) (vec : ℕ → Bool) (B : ℕ → ℕ) where
  /-- **The weights**: `mu t` after `t` letters. -/
  mu : ℕ → Fin n → ℤ
  zero : mu 0 = 0
  step : ∀ t < N, IsStep (vec t) (B t) (mu t) (mu (t + 1))
  stop : ∀ t, N ≤ t → mu t = mu N

variable {N : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **The weights of a Pieri path are dominant.** -/
theorem PieriPath.antitone (P : PieriPath n N vec B) (t : ℕ) : Antitone (P.mu t) := by
  induction t with
  | zero => rw [P.zero]; exact fun _ _ _ => le_rfl
  | succ t ih =>
    by_cases ht : t < N
    · exact (P.step t ht).antitone
    · rw [P.stop (t + 1) (by omega), ← P.stop t (by omega)]
      exact ih

/-- **The possible next weights**: the `μ` with `IsStep v b ν μ` (they lie in the box `ν ± b`). -/
def nextW (v : Bool) (b : ℕ) (ν : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  open scoped Classical in (Fintype.piFinset fun a => Icc (ν a - b) (ν a + b)).filter (IsStep v b ν)

/-- **Membership in the next weights.** -/
theorem mem_nextW {v : Bool} {b : ℕ} {ν μ : Fin n → ℤ} : μ ∈ nextW v b ν ↔ IsStep v b ν μ := by
  classical
  simp only [nextW, mem_filter, Fintype.mem_piFinset, mem_Icc, and_iff_right_iff_imp]
  intro h a
  have key : ∀ (x y : Fin n → ℤ), IsStrip x y b → ∀ a, x a ≤ y a ∧ y a ≤ x a + b := by
    intro x y hxy a
    refine ⟨hxy.1 a, ?_⟩
    have h1 : y a - x a ≤ ∑ a, (y a - x a) :=
      Finset.single_le_sum (f := fun a => y a - x a) (fun a _ => by linarith [hxy.1 a]) (mem_univ a)
    rw [Finset.sum_sub_distrib, hxy.2.2] at h1
    linarith
  cases v
  · have := key μ ν h a; omega
  · have := key ν μ h a; omega

/-- **Extending a path** stopped at `N` by the weight `ν` at `N + 1`. -/
def extend (μ : ℕ → Fin n → ℤ) (N : ℕ) (ν : Fin n → ℤ) : ℕ → Fin n → ℤ := fun t => if t ≤ N then μ t else ν

open scoped Classical in
/-- **The weight functions of the Pieri paths**, stopped at `N`. -/
def pathSet (vec : ℕ → Bool) (B : ℕ → ℕ) : ℕ → Finset (ℕ → Fin n → ℤ)
  | 0 => {fun _ => 0}
  | N + 1 => (pathSet vec B N).biUnion fun μ => (nextW (vec N) (B N) (μ N)).image (extend μ N)

/-- **The path conditions** on a weight function. -/
def IsPath (vec : ℕ → Bool) (B : ℕ → ℕ) (N : ℕ) (μ : ℕ → Fin n → ℤ) : Prop :=
  μ 0 = 0 ∧ (∀ t < N, IsStep (vec t) (B t) (μ t) (μ (t + 1))) ∧ ∀ t, N ≤ t → μ t = μ N

/-- **Membership in `pathSet`** is the path conditions. -/
theorem mem_pathSet {μ : ℕ → Fin n → ℤ} : μ ∈ pathSet vec B N ↔ IsPath vec B N μ := by
  induction N generalizing μ with
  | zero =>
    simp only [pathSet, mem_singleton, IsPath, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true, true_and,
      zero_le, forall_const]
    constructor
    · rintro rfl
      simp
    · rintro ⟨h0, h⟩
      funext t
      rw [h t, h0]
  | succ N ih =>
    simp only [pathSet, mem_biUnion, mem_image, mem_nextW]
    constructor
    · rintro ⟨μ', hμ', ν, hν, rfl⟩
      obtain ⟨h0, hs, hst⟩ := ih.1 hμ'
      refine ⟨by simp [extend, h0], fun t ht => ?_, fun t ht => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
        · simpa [extend, show t ≤ N by omega, show t + 1 ≤ N by omega] using hs t ht
        · simpa [extend] using hν
      · simp [extend, show ¬ t ≤ N by omega]
    · rintro ⟨h0, hs, hst⟩
      refine ⟨extend μ N (μ N), ih.2 ⟨by simp [extend, h0], fun t ht => ?_, fun t ht => ?_⟩, μ (N + 1), ?_, ?_⟩
      · simpa [extend, show t ≤ N by omega, show t + 1 ≤ N by omega] using hs t (by omega)
      · by_cases h : t ≤ N
        · simp [extend, show t = N by omega]
        · simp [extend, h]
      · simpa [extend] using hs N (by omega)
      · funext t
        by_cases h : t ≤ N
        · simp [extend, h]
        · simp only [extend, h, ite_false]
          exact (hst t (by omega)).symm

/-- **The sum over the paths with one more letter.** -/
theorem sum_pathSet_succ {M : Type*} [AddCommMonoid M] (f : (Fin n → ℤ) → M) :
    ∑ μ ∈ pathSet vec B (N + 1), f (μ (N + 1)) =
      ∑ μ ∈ pathSet vec B N, ∑ ν ∈ nextW (vec N) (B N) (μ N), f ν := by
  classical
  rw [pathSet, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_image]
    · simp [extend]
    · intro ν _ ν' _ h
      simpa [extend] using congrFun h (N + 1)
  · intro μ hμ μ' hμ' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro F hF hF'
    simp only [mem_image] at hF hF'
    obtain ⟨ν, -, rfl⟩ := hF
    obtain ⟨ν', -, h⟩ := hF'
    have s1 := (mem_pathSet.1 (Finset.mem_coe.1 hμ)).2.2
    have s2 := (mem_pathSet.1 (Finset.mem_coe.1 hμ')).2.2
    refine hne (funext fun t => ?_)
    have key : ∀ t ≤ N, μ t = μ' t := fun t ht => by simpa [extend, ht] using (congrFun h t).symm
    by_cases ht : t ≤ N
    · exact key t ht
    · rw [s1 t (by omega), s2 t (by omega), key N le_rfl]

/-- **The weights of a path are dominant.** -/
theorem IsPath.antitone {μ : ℕ → Fin n → ℤ} (h : IsPath vec B N μ) (t : ℕ) : Antitone (μ t) := by
  induction t with
  | zero => rw [h.1]; exact fun _ _ _ => le_rfl
  | succ t ih =>
    by_cases ht : t < N
    · exact (h.2.1 t ht).antitone
    · rw [h.2.2 (t + 1) (by omega), ← h.2.2 t (by omega)]
      exact ih

/-- **A Pieri path satisfies the path conditions.** -/
theorem PieriPath.isPath (P : PieriPath n N vec B) : IsPath vec B N P.mu := ⟨P.zero, P.step, P.stop⟩

/-- **The Pieri paths are their weight functions.** -/
def PieriPath.equiv : PieriPath n N vec B ≃ {μ : ℕ → Fin n → ℤ // μ ∈ pathSet vec B N} where
  toFun P := ⟨P.mu, mem_pathSet.2 P.isPath⟩
  invFun μ := ⟨μ.1, (mem_pathSet.1 μ.2).1, (mem_pathSet.1 μ.2).2.1, (mem_pathSet.1 μ.2).2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (PieriPath n N vec B) := Fintype.ofEquiv _ PieriPath.equiv.symm

end Path

/-! ## Pieri's count along the paths -/

section Count

variable {m : ℕ}

/-- **The next weights at a vector letter are the horizontal strips** of `WeylCount`. -/
theorem nextW_true (lam : Fin (m + 1) → ℤ) (b : ℕ) : nextW true b lam = strip lam b := by
  ext μ
  rw [mem_nextW, mem_strip]
  simp only [IsStep, ite_true]
  constructor
  · intro h
    have hb := (mem_nextW.2 (show IsStep true b lam μ from h))
    simp only [nextW, mem_filter, Fintype.mem_piFinset, mem_Icc] at hb
    refine ⟨⟨h.1 0, (hb.1 0).2⟩, fun i => ⟨h.1 _, h.2.1 i.castSucc i.succ (by simp)⟩, h.2.2⟩
  · rintro ⟨⟨h0, -⟩, hs, hsum⟩
    refine ⟨fun a => ?_, fun a a' haa => ?_, hsum⟩
    · refine Fin.cases h0 (fun i => (hs i).1) a
    · obtain ⟨i, rfl⟩ : ∃ i : Fin m, a' = i.succ :=
        ⟨⟨a'.val - 1, by omega⟩, Fin.ext (by simp; omega)⟩
      have : a = i.castSucc := Fin.ext (by simp at haa ⊢; omega)
      subst this
      exact (hs i).2

/-- **The dual weight** `−ν ∘ rev`. -/
def dualW (ν : Fin m → ℤ) : Fin m → ℤ := fun i => -ν i.rev

/-- **Strips under duality**: `μ/ν` is a strip iff `ν*/μ*` is one. -/
theorem isStrip_dualW {ν μ : Fin m → ℤ} {b : ℕ} : IsStrip ν μ b ↔ IsStrip (dualW μ) (dualW ν) b := by
  have hs : ∀ w : Fin m → ℤ, ∑ a, dualW w a = -∑ a, w a := fun w => by
    simp only [dualW, Finset.sum_neg_distrib]
    exact congrArg _ (Fintype.sum_equiv Fin.revPerm _ _ fun _ => rfl)
  simp only [IsStrip, hs]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun a => neg_le_neg (h1 _), fun a a' haa => neg_le_neg (h2 a'.rev a.rev (by simp; omega)), by
      rw [h3]; ring⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun a => by simpa [dualW] using h1 a.rev, fun a a' haa => ?_, by linarith⟩
    simpa [dualW] using h2 a'.rev a.rev (by simp; omega)

/-- **The dual weight is involutive.** -/
theorem dualW_dualW (ν : Fin m → ℤ) : dualW (dualW ν) = ν := funext fun i => by simp [dualW]

/-- **Pieri at a vector letter**: `Σ_{μ/ν a b-strip} dimW(μ) = dimW(ν)·C(b + m, m)`. -/
theorem sum_nextW_true (lam : Fin (m + 1) → ℤ) (b : ℕ) :
    ∑ ν ∈ nextW true b lam, dimW (m + 1) ν = dimW (m + 1) lam * (b + m).choose m := by
  rw [nextW_true, dimW_mul_choose]

/-- **Pieri at a covector letter**: `Σ_{ν/μ a b-strip} dimW(μ) = dimW(ν)·C(b + m, m)`, by duality. -/
theorem sum_nextW_false {lam : Fin (m + 1) → ℤ} (hlam : Antitone lam) (b : ℕ) :
    ∑ ν ∈ nextW false b lam, dimW (m + 1) ν = dimW (m + 1) lam * (b + m).choose m := by
  have e : ∑ ν ∈ nextW false b lam, dimW (m + 1) ν = ∑ ν ∈ nextW true b (dualW lam), dimW (m + 1) ν := by
    refine Finset.sum_nbij' dualW dualW (fun ν hν => ?_) (fun ν hν => ?_) (fun ν _ => dualW_dualW ν)
      (fun ν _ => dualW_dualW ν) (fun ν hν => ?_)
    · rw [mem_nextW] at hν ⊢
      exact isStrip_dualW.1 hν
    · rw [mem_nextW] at hν ⊢
      have := isStrip_dualW.1 (show IsStrip (dualW lam) ν b from hν)
      rwa [dualW_dualW] at this
    · rw [mem_nextW] at hν
      have hanti := (show IsStrip ν lam b from hν).antitone.1
      exact (dimW_dual hanti).symm
  rw [e, sum_nextW_true]
  exact congrArg (· * _) (dimW_dual hlam)

/-- **Pieri's count along the paths**: `Σ_P dimW(μ_N) = ∏_{t < N} C(B_t + m, m)` in `m + 1` coordinates. -/
theorem sum_dimW_pathSet (vec : ℕ → Bool) (B : ℕ → ℕ) (N : ℕ) :
    ∑ μ ∈ pathSet vec B N, dimW (m + 1) (μ N) = ∏ t ∈ range N, (B t + m).choose m := by
  induction N with
  | zero => simp [pathSet, dimW_zero]
  | succ N ih =>
    rw [sum_pathSet_succ, Finset.prod_range_succ, ← ih, Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    cases h : vec N
    · exact sum_nextW_false ((mem_pathSet.1 hμ).antitone N) _
    · exact sum_nextW_true _ _

/-- **Pieri's count over the Pieri paths.** -/
theorem sum_dimW_paths (vec : ℕ → Bool) (B : ℕ → ℕ) (N : ℕ) :
    ∑ P : PieriPath (m + 1) N vec B, dimW (m + 1) (P.mu N) = ∏ t ∈ range N, (B t + m).choose m := by
  rw [← sum_dimW_pathSet, ← Finset.sum_coe_sort (pathSet vec B N)]
  exact Fintype.sum_equiv PieriPath.equiv _ _ fun _ => rfl

end Count

/-! ## Standard fillings and their count -/

section Filling

variable {n : ℕ}

/-- **The column `col(c)` of a filling**: `I c` for `c ≥ 1`, its complement for `c ≤ 0`. -/
def colSet (I : ℤ → Finset (Fin n)) (c : ℤ) : Finset (Fin n) := if 1 ≤ c then I c else (I c)ᶜ

/-- **Standard column systems** of shape `lam`: `col(c)` has `colH lam c` elements, and the rows weakly increase,
`#{x ∈ col(c + 1) : x < t} ≤ #{x ∈ col(c) : x < t}` for all `c` and `t`. -/
def IsStdCol (lam : Fin n → ℤ) (C : ℤ → Finset (Fin n)) : Prop :=
  (∀ c, (C c).card = colH lam c) ∧
    ∀ c (t : ℕ), ((C (c + 1)).filter fun x => x.val < t).card ≤ ((C c).filter fun x => x.val < t).card

/-- **A standard filling** of the weight `lam`: the sets `I(c)`, of size `colH lam c` for `c ≥ 1` and
`n − colH lam c` for `c ≤ 0`, whose columns `col(c)` (`colSet`) form a standard column system. -/
def IsStdFilling (lam : Fin n → ℤ) (I : ℤ → Finset (Fin n)) : Prop := IsStdCol lam (colSet I)

/-- **Taking columns is involutive.** -/
theorem colSet_colSet (I : ℤ → Finset (Fin n)) : colSet (colSet I) = I := funext fun c => by
  unfold colSet
  split_ifs <;> simp

/-- **Standard fillings are standard column systems.** -/
def fillEquiv (lam : Fin n → ℤ) : {I // IsStdFilling lam I} ≃ {C // IsStdCol lam C} where
  toFun I := ⟨colSet I.1, I.2⟩
  invFun C := ⟨colSet C.1, by unfold IsStdFilling; rw [colSet_colSet]; exact C.2⟩
  left_inv I := Subtype.ext (colSet_colSet I.1)
  right_inv C := Subtype.ext (colSet_colSet C.1)

/-- **Column heights decrease** from left to right. -/
theorem colH_anti (w : Fin n → ℤ) {c c' : ℤ} (h : c ≤ c') : colH w c' ≤ colH w c :=
  card_le_card fun a => by simp only [mem_filter, mem_univ, true_and]; exact fun ha => h.trans ha

/-- **Rows `0, …, i` reach the column `c ≤ w_i`.** -/
theorem le_colH {w : Fin n → ℤ} (hw : Antitone w) {i : Fin n} {c : ℤ} (h : c ≤ w i) : i.val + 1 ≤ colH w c := by
  have hs : (univ.filter fun a : Fin n => (a : ℕ) < i.val + 1) ⊆ univ.filter fun a => c ≤ w a := by
    intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    exact h.trans (hw (Fin.le_def.2 (by omega)))
  have h2 := card_le_card hs
  rw [Fin.card_filter_val_lt] at h2
  have := i.isLt
  unfold colH
  omega

/-- **Only rows `< i` reach a column `c > w_i`.** -/
theorem colH_le_of_lt {w : Fin n → ℤ} (hw : Antitone w) {i : Fin n} {c : ℤ} (h : w i < c) : colH w c ≤ i.val := by
  have hs : (univ.filter fun a => c ≤ w a) ⊆ univ.filter fun a : Fin n => (a : ℕ) < i.val := by
    intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    by_contra hh
    have := hw (Fin.le_def.2 (not_lt.1 hh))
    linarith
  have h2 := card_le_card hs
  rw [Fin.card_filter_val_lt] at h2
  unfold colH
  omega

/-- **Dominant weights are determined by their column heights.** -/
theorem eq_of_colH_eq {w w' : Fin n → ℤ} (hw : Antitone w) (hw' : Antitone w') (h : ∀ c, colH w c = colH w' c) :
    w = w' := by
  funext i
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := le_colH hw' (le_refl (w' i))
    have h2 := colH_le_of_lt hw hlt
    rw [h] at h2
    omega
  · have h1 := le_colH hw (le_refl (w i))
    have h2 := colH_le_of_lt hw' hlt
    rw [← h] at h2
    omega

/-- **The members of a filter of `(a, b]` by a down-closed predicate** form an initial segment: `P c` iff
`c ≤ a + #{c' ∈ (a, b] : P c'}`. -/
theorem mem_filter_Ioc_iff {P : ℤ → Prop} [DecidablePred P] (hP : ∀ x y, x ≤ y → P y → P x) {a b c : ℤ}
    (hc : c ∈ Ioc a b) : P c ↔ c ≤ a + ((Ioc a b).filter P).card := by
  rw [mem_Ioc] at hc
  constructor
  · intro h
    have hsub : Ioc a c ⊆ (Ioc a b).filter P := fun x hx => by
      rw [mem_Ioc] at hx
      exact mem_filter.2 ⟨mem_Ioc.2 ⟨hx.1, hx.2.trans hc.2⟩, hP x c hx.2 h⟩
    have := card_le_card hsub
    rw [Int.card_Ioc] at this
    omega
  · intro h
    by_contra hn
    have hsub : (Ioc a b).filter P ⊆ Ioc a (c - 1) := fun x hx => by
      rw [mem_filter, mem_Ioc] at hx
      rw [mem_Ioc]
      refine ⟨hx.1.1, ?_⟩
      by_contra hxc
      exact hn (hP c x (by omega) hx.2)
    have := card_le_card hsub
    rw [Int.card_Ioc] at this
    omega

/-! ### The Gelfand–Tsetlin recursion: removing the largest entry -/

/-- **Removing the largest entry `n`** from the columns. -/
def trunc (C : ℤ → Finset (Fin (n + 1))) (c : ℤ) : Finset (Fin n) := univ.filter fun a => a.castSucc ∈ C c

/-- **The truncated columns below `t`.** -/
theorem card_trunc_filter (C : ℤ → Finset (Fin (n + 1))) (c : ℤ) (t : ℕ) :
    ((trunc C c).filter fun x => x.val < t).card = ((C c).filter fun x => x.val < min t n).card := by
  rw [← card_map Fin.castSuccEmb]
  congr 1
  ext x
  simp only [mem_map, mem_filter, trunc, mem_univ, true_and, Fin.castSuccEmb_apply]
  constructor
  · rintro ⟨a, ⟨ha, hat⟩, rfl⟩
    exact ⟨ha, by simp only [Fin.val_castSucc]; omega⟩
  · rintro ⟨hx, hxt⟩
    have e : (⟨x.val, by omega⟩ : Fin n).castSucc = x := Fin.ext rfl
    exact ⟨⟨x.val, by omega⟩, ⟨by rw [e]; exact hx, by simp only; omega⟩, e⟩

/-- **The truncated column sizes.** -/
theorem card_trunc (C : ℤ → Finset (Fin (n + 1))) (c : ℤ) :
    (trunc C c).card = ((C c).filter fun x => x.val < n).card := by
  have h := card_trunc_filter C c n
  rwa [min_self, filter_true_of_mem fun x _ => x.isLt] at h

/-- **A column is its truncation plus possibly `n`.** -/
theorem card_eq_trunc (C : ℤ → Finset (Fin (n + 1))) (c : ℤ) :
    (C c).card = (trunc C c).card + if Fin.last n ∈ C c then 1 else 0 := by
  rw [card_trunc, ← card_filter_add_card_filter_not (fun x : Fin (n + 1) => x.val < n)]
  congr 1
  have e : (C c).filter (fun x : Fin (n + 1) => ¬ x.val < n) = if Fin.last n ∈ C c then {Fin.last n} else ∅ := by
    ext x
    have hx : ¬ x.val < n ↔ x = Fin.last n := by
      rw [Fin.ext_iff, Fin.val_last]
      have := x.isLt
      omega
    simp only [mem_filter, hx]
    split_ifs with h
    · simp only [mem_singleton]
      exact ⟨fun h' => h'.2, fun h' => ⟨h' ▸ h, h'⟩⟩
    · simp only [Finset.notMem_empty, iff_false, not_and]
      exact fun h1 h2 => h (h2 ▸ h1)
  rw [e]
  split_ifs <;> simp

variable {lam : Fin (n + 1) → ℤ} {C : ℤ → Finset (Fin (n + 1))}

/-- **The truncated heights decrease** from left to right. -/
theorem IsStdCol.trunc_anti (hC : IsStdCol lam C) {c c' : ℤ} (h : c ≤ c') :
    (trunc C c').card ≤ (trunc C c).card := by
  induction c', h using Int.leInduction with
  | base => exact le_rfl
  | succ c' _ ih =>
    refine le_trans ?_ ih
    rw [card_trunc, card_trunc]
    exact hC.2 c' n

/-- **The shape of the truncated columns**: `κ_i = λ_{i+1} + #{c ∈ (λ_{i+1}, λ_i] : i + 1 ≤ |trunc C c|}`. -/
def tshape (lam : Fin (n + 1) → ℤ) (C : ℤ → Finset (Fin (n + 1))) (i : Fin n) : ℤ :=
  lam i.succ + ((Ioc (lam i.succ) (lam i.castSucc)).filter fun c => i.val + 1 ≤ (trunc C c).card).card

/-- **The rows of the truncated shape** reach exactly the columns whose truncation is tall enough. -/
theorem le_tshape_iff (hlam : Antitone lam) (hC : IsStdCol lam C) (i : Fin n) (c : ℤ) :
    c ≤ tshape lam C i ↔ i.val + 1 ≤ (trunc C c).card := by
  have hanti : ∀ x y, x ≤ y → i.val + 1 ≤ (trunc C y).card → i.val + 1 ≤ (trunc C x).card :=
    fun x y hxy h => h.trans (hC.trunc_anti hxy)
  by_cases h1 : c ≤ lam i.succ
  · have hP : i.val + 1 ≤ (trunc C c).card := by
      have h2 := le_colH hlam (i := i.succ) h1
      rw [← hC.1 c, card_eq_trunc] at h2
      simp only [Fin.val_succ] at h2
      split_ifs at h2 <;> omega
    simp only [hP, iff_true, tshape]
    omega
  · by_cases h2 : lam i.castSucc < c
    · have hP : ¬ i.val + 1 ≤ (trunc C c).card := by
        have h3 := colH_le_of_lt hlam (i := i.castSucc) h2
        rw [← hC.1 c, card_eq_trunc] at h3
        simp only [Fin.val_castSucc] at h3
        split_ifs at h3 <;> omega
      simp only [hP, iff_false, not_le, tshape]
      have := card_le_card (filter_subset (fun c => i.val + 1 ≤ (trunc C c).card)
        (Ioc (lam i.succ) (lam i.castSucc)))
      rw [Int.card_Ioc] at this
      omega
    · exact (mem_filter_Ioc_iff hanti (mem_Ioc.2 ⟨by omega, by omega⟩)).symm

/-- **The heights of the truncated shape** are the truncated column sizes. -/
theorem colH_tshape (hlam : Antitone lam) (hC : IsStdCol lam C) (c : ℤ) :
    colH (tshape lam C) c = (trunc C c).card := by
  unfold colH
  rw [Finset.filter_congr (fun i _ => le_tshape_iff hlam hC i c)]
  have e : (univ.filter fun i : Fin n => i.val + 1 ≤ (trunc C c).card) =
      univ.filter fun i : Fin n => (i : ℕ) < (trunc C c).card := Finset.filter_congr fun i _ => by omega
  rw [e, Fin.card_filter_val_lt]
  have : (trunc C c).card ≤ n := (card_le_univ _).trans (by simp)
  omega

/-- **The truncated shape interlaces.** -/
theorem tshape_mem (hlam : Antitone lam) (C : ℤ → Finset (Fin (n + 1))) : tshape lam C ∈ interlace lam := by
  rw [mem_interlace]
  intro i
  have hle : lam i.succ ≤ lam i.castSucc := hlam (Fin.castSucc_le_succ i)
  have := card_le_card (filter_subset (fun c => i.val + 1 ≤ (trunc C c).card) (Ioc (lam i.succ) (lam i.castSucc)))
  rw [Int.card_Ioc] at this
  simp only [tshape]
  omega

/-- **The truncation is standard** for the truncated shape. -/
theorem isStdCol_trunc (hlam : Antitone lam) (hC : IsStdCol lam C) : IsStdCol (tshape lam C) (trunc C) :=
  ⟨fun c => (colH_tshape hlam hC c).symm, fun c t => by
    rw [card_trunc_filter, card_trunc_filter]
    exact hC.2 c _⟩

/-- **Interlacing in column heights**: the heights of `κ ≺ λ` are those of `λ`, or one less. -/
theorem colH_interlace {κ : Fin n → ℤ} (h : κ ∈ interlace lam) (c : ℤ) :
    colH κ c ≤ colH lam c ∧ colH lam c ≤ colH κ c + 1 := by
  rw [mem_interlace] at h
  constructor
  · calc colH κ c ≤ ((univ.filter fun i : Fin n => c ≤ lam i.castSucc).map Fin.castSuccEmb).card := by
          rw [card_map]
          exact card_le_card fun i => by
            simp only [mem_filter, mem_univ, true_and]
            exact fun hi => hi.trans (h i).2
      _ ≤ colH lam c := card_le_card fun a => by
          simp only [mem_map, mem_filter, mem_univ, true_and, Fin.castSuccEmb_apply]
          rintro ⟨i, hi, rfl⟩
          exact hi
  · unfold colH
    rw [Fin.card_filter_univ_succ']
    have : (univ.filter fun i : Fin n => c ≤ lam i.succ).card ≤ (univ.filter fun i => c ≤ κ i).card :=
      card_le_card fun i => by
        simp only [mem_filter, mem_univ, true_and]
        exact fun hi => hi.trans (h i).1
    split_ifs <;> omega

/-- **Adding the largest entry `n`** to the columns where `λ` is taller than `κ`. -/
def grow (lam : Fin (n + 1) → ℤ) (κ : Fin n → ℤ) (C' : ℤ → Finset (Fin n)) (c : ℤ) : Finset (Fin (n + 1)) :=
  (C' c).map Fin.castSuccEmb ∪ if colH κ c < colH lam c then {Fin.last n} else ∅

/-- **Membership in the grown columns.** -/
theorem mem_grow {κ : Fin n → ℤ} {C' : ℤ → Finset (Fin n)} {c : ℤ} {x : Fin (n + 1)} :
    x ∈ grow lam κ C' c ↔ (∃ a ∈ C' c, a.castSucc = x) ∨ (colH κ c < colH lam c ∧ x = Fin.last n) := by
  simp only [grow, mem_union, mem_map, Fin.castSuccEmb_apply]
  split_ifs with h <;> simp [h]

/-- **The grown columns below `t ≤ n`** are the old ones. -/
theorem card_grow_filter {κ : Fin n → ℤ} (C' : ℤ → Finset (Fin n)) (c : ℤ) {t : ℕ} (ht : t ≤ n) :
    ((grow lam κ C' c).filter fun x => x.val < t).card = ((C' c).filter fun x => x.val < t).card := by
  conv_rhs => rw [← card_map Fin.castSuccEmb]
  congr 1
  ext x
  simp only [mem_filter, mem_grow, mem_map, Fin.castSuccEmb_apply]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩ | ⟨-, rfl⟩, hx⟩
    · exact ⟨a, ⟨ha, by simpa using hx⟩, rfl⟩
    · simp only [Fin.val_last] at hx
      omega
  · rintro ⟨a, ⟨ha, hat⟩, rfl⟩
    exact ⟨Or.inl ⟨a, ha, rfl⟩, by simpa using hat⟩

/-- **The grown column sizes.** -/
theorem card_grow {κ : Fin n → ℤ} (C' : ℤ → Finset (Fin n)) (c : ℤ) :
    (grow lam κ C' c).card = (C' c).card + if colH κ c < colH lam c then 1 else 0 := by
  rw [grow, card_union_of_disjoint, card_map]
  · split_ifs <;> simp
  · rw [disjoint_left]
    intro x hx hx'
    simp only [mem_map, Fin.castSuccEmb_apply] at hx
    obtain ⟨a, -, rfl⟩ := hx
    split_ifs at hx' with h
    · exact Fin.castSucc_ne_last a (mem_singleton.1 hx')
    · simp at hx'

/-- **Growing is standard** for `λ`. -/
theorem isStdCol_grow {κ : Fin n → ℤ} {C' : ℤ → Finset (Fin n)} (h : κ ∈ interlace lam) (hC' : IsStdCol κ C') :
    IsStdCol lam (grow lam κ C') := by
  have hsize : ∀ c, (grow lam κ C' c).card = colH lam c := fun c => by
    rw [card_grow, hC'.1 c]
    have := colH_interlace h c
    split_ifs <;> omega
  refine ⟨hsize, fun c t => ?_⟩
  by_cases ht : t ≤ n
  · rw [card_grow_filter C' _ ht, card_grow_filter C' _ ht]
    exact hC'.2 c t
  · rw [filter_true_of_mem fun x _ => (show x.val < t by have := x.isLt; omega),
      filter_true_of_mem fun x _ => (show x.val < t by have := x.isLt; omega), hsize, hsize]
    exact colH_anti lam (by omega)

/-- **Truncating the grown columns** gives the old ones. -/
theorem trunc_grow (κ : Fin n → ℤ) (C' : ℤ → Finset (Fin n)) : trunc (grow lam κ C') = C' := by
  funext c
  ext a
  simp only [trunc, mem_filter, mem_univ, true_and, mem_grow]
  constructor
  · rintro (⟨b, hb, hba⟩ | ⟨-, h⟩)
    · rwa [← Fin.castSucc_inj.1 hba]
    · exact absurd h (Fin.castSucc_ne_last a)
  · exact fun ha => Or.inl ⟨a, ha, rfl⟩

/-- **Growing the truncation** gives back the columns. -/
theorem grow_trunc (hlam : Antitone lam) (hC : IsStdCol lam C) : grow lam (tshape lam C) (trunc C) = C := by
  funext c
  have hlast : Fin.last n ∈ C c ↔ colH (tshape lam C) c < colH lam c := by
    rw [colH_tshape hlam hC, ← hC.1 c, card_eq_trunc]
    split_ifs with h <;> simp [h]
  ext x
  rw [mem_grow]
  constructor
  · rintro (⟨a, ha, rfl⟩ | ⟨h, rfl⟩)
    · simpa [trunc] using ha
    · exact hlast.2 h
  · intro hx
    by_cases hxl : x = Fin.last n
    · exact Or.inr ⟨hlast.1 (hxl ▸ hx), hxl⟩
    · obtain ⟨a, rfl⟩ := Fin.exists_castSucc_eq.2 hxl
      exact Or.inl ⟨a, by simpa [trunc] using hx, rfl⟩

/-- **The truncated shape of the grown columns** is the old shape. -/
theorem tshape_grow (hlam : Antitone lam) {κ : Fin n → ℤ} {C' : ℤ → Finset (Fin n)} (h : κ ∈ interlace lam)
    (hC' : IsStdCol κ C') : tshape lam (grow lam κ C') = κ := by
  have hG := isStdCol_grow h hC'
  refine eq_of_colH_eq (antitone_of_mem_interlace (tshape_mem hlam _)) (antitone_of_mem_interlace h)
    fun c => ?_
  rw [colH_tshape hlam hG, trunc_grow, hC'.1 c]

/-- **The Gelfand–Tsetlin recursion for standard columns**: removing the entry `n`. -/
def gtEquiv (hlam : Antitone lam) :
    {C // IsStdCol lam C} ≃ Σ κ : {κ // κ ∈ interlace lam}, {C' // IsStdCol κ.1 C'} where
  toFun C := ⟨⟨tshape lam C.1, tshape_mem hlam _⟩, ⟨trunc C.1, isStdCol_trunc hlam C.2⟩⟩
  invFun p := ⟨grow lam p.1.1 p.2.1, isStdCol_grow p.1.2 p.2.2⟩
  left_inv C := Subtype.ext (grow_trunc hlam C.2)
  right_inv p := Sigma.subtype_ext (Subtype.ext (tshape_grow hlam p.1.2 p.2.2)) (trunc_grow _ _)

end Filling

/-- **The number of standard column systems** of a dominant weight is its Weyl dimension (the number of
Gelfand–Tsetlin patterns). -/
theorem card_stdCol : ∀ {n : ℕ} {lam : Fin n → ℤ}, Antitone lam →
    Finite {C // IsStdCol lam C} ∧ Nat.card {C // IsStdCol lam C} = dimW n lam
  | 0, lam, _ => by
    have hu : ∀ C : ℤ → Finset (Fin 0), C = fun _ => ∅ := fun C => funext fun c => Finset.eq_empty_of_isEmpty _
    have hstd : IsStdCol lam (fun _ => (∅ : Finset (Fin 0))) :=
      ⟨fun c => by simp [colH], fun c t => le_rfl⟩
    have : Unique {C // IsStdCol lam C} :=
      ⟨⟨⟨_, hstd⟩⟩, fun C => Subtype.ext ((hu C.1).trans rfl)⟩
    exact ⟨inferInstance, by rw [Nat.card_unique]; rfl⟩
  | n + 1, lam, hlam => by
    have ih : ∀ κ : {κ // κ ∈ interlace lam}, Finite {C' // IsStdCol κ.1 C'} ∧
        Nat.card {C' // IsStdCol κ.1 C'} = dimW n κ.1 :=
      fun κ => card_stdCol (antitone_of_mem_interlace κ.2)
    have : ∀ κ : {κ // κ ∈ interlace lam}, Finite {C' // IsStdCol κ.1 C'} := fun κ => (ih κ).1
    refine ⟨Finite.of_equiv _ (gtEquiv hlam).symm, ?_⟩
    rw [Nat.card_congr (gtEquiv hlam), Nat.card_sigma, dimW_succ]
    rw [← Finset.sum_coe_sort (interlace lam)]
    exact Finset.sum_congr rfl fun κ _ => (ih κ).2

/-- **The number of standard fillings** of a dominant weight is its Weyl dimension. -/
theorem card_stdFilling {n : ℕ} {lam : Fin n → ℤ} (hlam : Antitone lam) :
    Finite {I // IsStdFilling lam I} ∧ Nat.card {I // IsStdFilling lam I} = dimW n lam := by
  have h := card_stdCol hlam
  have : Finite {C // IsStdCol lam C} := h.1
  exact ⟨Finite.of_equiv _ (fillEquiv lam).symm, by rw [Nat.card_congr (fillEquiv lam), h.2]⟩

/-! ## The path polynomials and their columns -/

section Poly

variable (R : Type*) [CommRing R] {n : ℕ}

/-- **The column range** of a weight function up to `N`: `[−M, M]` with `M = Σ_{t ≤ N} Σ_a |μ_t(a)|`. -/
def colRange (μ : ℕ → Fin n → ℤ) (N : ℕ) : Finset ℤ :=
  Icc (-∑ t ∈ range (N + 1), ∑ a, |μ t a|) (∑ t ∈ range (N + 1), ∑ a, |μ t a|)

/-- **The path polynomial** `Ψ(μ, I) = ∏_c K_c(I(c))`: the product over the column range of the column states
`K_c = colK` of `TwistedDegree`, read at `I(c)`. -/
def pathPoly (μ : ℕ → Fin n → ℤ) (N : ℕ) (I : ℤ → Finset (Fin n)) : MvPolynomial (ℕ × Fin n) R :=
  ∏ c ∈ colRange μ N, colK R μ c N (I c)

variable {R}

/-- **The entries up to `N` are bounded** by the column range. -/
theorem abs_le_colRange (μ : ℕ → Fin n → ℤ) {N t : ℕ} (ht : t ≤ N) (a : Fin n) :
    |μ t a| ≤ ∑ t ∈ range (N + 1), ∑ a, |μ t a| := by
  have h1 : |μ t a| ≤ ∑ a, |μ t a| := Finset.single_le_sum (f := fun a => |μ t a|) (fun a _ => abs_nonneg _)
    (mem_univ a)
  have h2 : ∑ a, |μ t a| ≤ ∑ t ∈ range (N + 1), ∑ a, |μ t a| :=
    Finset.single_le_sum (f := fun t => ∑ a, |μ t a|) (fun t _ => Finset.sum_nonneg fun a _ => abs_nonneg _)
      (mem_range.2 (by omega))
  exact h1.trans h2

/-- **Outside the column range the heights do not move.** -/
theorem colH_of_notMem {μ : ℕ → Fin n → ℤ} {N : ℕ} {c : ℤ} (hc : c ∉ colRange μ N) {t : ℕ} (ht : t ≤ N) :
    colH (μ t) c = colH (μ 0) c := by
  simp only [colRange, mem_Icc, not_and_or, not_le] at hc
  have hb : ∀ s ≤ N, ∀ a, |μ s a| ≤ ∑ t ∈ range (N + 1), ∑ a, |μ t a| := fun s hs a => abs_le_colRange μ hs a
  rcases hc with hc | hc
  · have e : ∀ s ≤ N, colH (μ s) c = n := fun s hs => by
      unfold colH
      rw [filter_true_of_mem fun a _ => by have := abs_le.1 (hb s hs a); linarith, card_univ, Fintype.card_fin]
    rw [e t ht, e 0 (Nat.zero_le _)]
  · have e : ∀ s ≤ N, colH (μ s) c = 0 := fun s hs => by
      unfold colH
      rw [filter_false_of_mem fun a _ => by have := abs_le.1 (hb s hs a); linarith, card_empty]
    rw [e t ht, e 0 (Nat.zero_le _)]

/-- **A column whose height never moves** keeps the initial state `[J = ∅]`. -/
theorem colK_of_const {μ : ℕ → Fin n → ℤ} {c : ℤ} {N : ℕ} (h : ∀ t ≤ N, colH (μ t) c = colH (μ 0) c) :
    colK R μ c N = st0 := by
  suffices ∀ t ≤ N, colSt (fun t a => (X (t, a) : MvPolynomial (ℕ × Fin n) R)) (colStep μ c) (fun _ => 1) t = st0
    from this N le_rfl
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [colSt_succ, colStep_keep (by rw [h t (by omega), h (t + 1) ht]), ih (by omega)]
    funext J
    simp [pw, Step.app]

/-- **The heights at the start of a path**: `n` for `c ≤ 0`, `0` for `c ≥ 1`. -/
theorem colH_zero (c : ℤ) : colH (0 : Fin n → ℤ) c = if 1 ≤ c then 0 else n := by
  unfold colH
  split_ifs with h
  · rw [filter_false_of_mem fun a _ => by simp; omega, card_empty]
  · rw [filter_true_of_mem fun a _ => by simp; omega, card_univ, Fintype.card_fin]

/-- **A standard filling is empty outside the column range** of a path. -/
theorem eq_empty_of_notMem {μ : ℕ → Fin n → ℤ} {N : ℕ} (h0 : μ 0 = 0) {I : ℤ → Finset (Fin n)}
    (hI : IsStdFilling (μ N) I) {c : ℤ} (hc : c ∉ colRange μ N) : I c = ∅ := by
  have h := hI.1 c
  rw [colH_of_notMem hc le_rfl, h0, colH_zero] at h
  unfold colSet at h
  split_ifs at h with h1
  · exact card_eq_zero.1 h
  · rw [card_compl, Fintype.card_fin] at h
    have : (I c).card ≤ n := (card_le_univ _).trans (by simp)
    exact card_eq_zero.1 (by omega)

/-- **The path polynomial over any window** containing the column range. -/
theorem pathPoly_eq_prod {μ : ℕ → Fin n → ℤ} {N : ℕ} (h0 : μ 0 = 0) {I : ℤ → Finset (Fin n)}
    (hI : IsStdFilling (μ N) I) {s : Finset ℤ} (hs : colRange μ N ⊆ s) :
    pathPoly R μ N I = ∏ c ∈ s, colK R μ c N (I c) := by
  refine Finset.prod_subset hs fun c _ hc => ?_
  rw [colK_of_const (μ := μ) (N := N) fun t ht => colH_of_notMem hc ht, eq_empty_of_notMem h0 hI hc]
  simp [st0]

/-- **The path polynomial is defined over `ℤ`.** -/
theorem pathPoly_map (μ : ℕ → Fin n → ℤ) (N : ℕ) (I : ℤ → Finset (Fin n)) :
    MvPolynomial.map (Int.castRingHom R) (pathPoly ℤ μ N I) = pathPoly R μ N I := by
  rw [pathPoly, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [colK, map_colSt]
  simp only [map_X]
  rfl

/-- **The column states are multilinear**: `K_c(J)` has degree `1` in the letters changing the height of the column
`c` and `0` in the others (T9f's (deg) at `p = 1`). -/
theorem colK_isWH (μ : ℕ → Fin n → ℤ) (c : ℤ) (N : ℕ) (J : Finset (Fin n)) :
    IsWeightedHomogeneous (rowW ℕ n) (colK R μ c N J)
      (fun u => if u < N ∧ colH (μ u) c ≠ colH (μ (u + 1)) c then 1 else 0) := by
  have h := twCol_deg R (p := 1) (pos := fun _ => 0) (N := N) (fun _ _ => le_rfl) μ c J
  have e : twCol R 1 (fun _ => 0) μ c N = colK R μ c N := by
    unfold twCol colK
    congr 1
  rw [e] at h
  simpa using h

variable {N : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **The column heights of a Pieri path move by at most one per letter**: up at vector letters, down at covector
letters. -/
theorem PieriPath.colH_step (P : PieriPath n N vec B) {t : ℕ} (ht : t < N) (c : ℤ) :
    (vec t = true → colH (P.mu t) c ≤ colH (P.mu (t + 1)) c ∧ colH (P.mu (t + 1)) c ≤ colH (P.mu t) c + 1) ∧
    (vec t = false → colH (P.mu (t + 1)) c ≤ colH (P.mu t) c ∧ colH (P.mu t) c ≤ colH (P.mu (t + 1)) c + 1) :=
  (P.step t ht).colH c

/-- **The columns `c ≥ 1` of a Pieri path satisfy T9f's column conditions** `ColCond`. -/
theorem PieriPath.colCond (P : PieriPath n N vec B) {c : ℤ} (hc : 1 ≤ c) : ColCond vec P.mu c N where
  step t ht := by
    have h := P.colH_step ht c
    cases hv : vec t
    · have := h.2 hv; omega
    · have := h.1 hv; omega
  grow t ht hlt := by
    have h := P.colH_step ht c
    cases hv : vec t
    · have := h.2 hv; omega
    · rfl
  drop t ht hlt := by
    have h := P.colH_step ht c
    cases hv : vec t
    · rfl
    · have := h.1 hv; omega
  start _ := by
    rw [P.zero, colH_zero]
    simp [hc]
  dual h := absurd h (by omega)

/-- **Each letter changes exactly `B_t` column heights**: the letter `t` occurs in exactly `B_t` column states. -/
theorem PieriPath.card_change (P : PieriPath n N vec B) {t : ℕ} (ht : t < N) :
    ((colRange P.mu N).filter fun c => colH (P.mu t) c ≠ colH (P.mu (t + 1)) c).card = B t := by
  set M := ∑ t ∈ range (N + 1), ∑ a, |P.mu t a|
  have hR : colRange P.mu N = Ioc (-M - 1) M := by
    ext c
    simp only [colRange, mem_Icc, mem_Ioc]
    omega
  have hb : ∀ s ≤ N, ∀ a, -M - 1 ≤ P.mu s a ∧ P.mu s a ≤ M := fun s hs a => by
    have := abs_le.1 (abs_le_colRange P.mu hs a)
    constructor <;> linarith
  rw [hR]
  have hs := P.step t ht
  cases hv : vec t
  · rw [hv] at hs
    have h := (show IsStrip (P.mu (t + 1)) (P.mu t) (B t) from hs).card_change
      (L := -M - 1) (U := M) (fun a => (hb (t + 1) ht a).1) (fun a => (hb t ht.le a).2)
    simpa only [ne_comm] using h
  · rw [hv] at hs
    exact (show IsStrip (P.mu t) (P.mu (t + 1)) (B t) from hs).card_change
      (fun a => (hb t ht.le a).1) (fun a => (hb (t + 1) ht a).2)

/-- **The path polynomial has multidegree `B`**: degree `B_t` in the letter `t < N`, `0` in the others. -/
theorem PieriPath.pathPoly_isWH (P : PieriPath n N vec B) (I : ℤ → Finset (Fin n)) :
    IsWeightedHomogeneous (rowW ℕ n) (pathPoly R P.mu N I) (fun u => if u < N then B u else 0) := by
  have h := IsWeightedHomogeneous.prod (colRange P.mu N) (fun c => colK R P.mu c N (I c)) _
    fun c _ => colK_isWH P.mu c N (I c)
  show IsWeightedHomogeneous _ (∏ c ∈ colRange P.mu N, colK R P.mu c N (I c)) _
  convert h using 1
  funext u
  rw [Finset.sum_apply]
  split_ifs with hu
  · simp only [hu, true_and]
    rw [Finset.sum_boole, P.card_change hu, Nat.cast_id]
  · simp [hu]

end Poly

/-! ## The canonical filling and the index set of the path family -/

section Index

variable {n N : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **The canonical filling** of `lam`: `col(c)` the first `colH lam c` indices, i.e. `I(c)` the first `colH lam c`
indices for `c ≥ 1` and the indices `≥ colH lam c` for `c ≤ 0`. -/
def canFill (lam : Fin n → ℤ) : ℤ → Finset (Fin n) := colSet fun c => univ.filter fun a : Fin n => a.val < colH lam c

/-- **The canonical filling is standard.** -/
theorem isStdFilling_canFill (lam : Fin n → ℤ) : IsStdFilling lam (canFill lam) := by
  unfold IsStdFilling canFill
  rw [colSet_colSet]
  have hle : ∀ c, colH lam c ≤ n := fun c => (card_le_univ _).trans (by simp)
  refine ⟨fun c => by rw [Fin.card_filter_val_lt]; have := hle c; omega, fun c t => ?_⟩
  rw [filter_filter, filter_filter]
  have e : ∀ h : ℕ, (univ.filter fun a : Fin n => (a : ℕ) < h ∧ (a : ℕ) < t) =
      univ.filter fun a : Fin n => (a : ℕ) < min h t := fun h => Finset.filter_congr fun a _ => by
    rw [lt_min_iff]
  rw [e, e, Fin.card_filter_val_lt, Fin.card_filter_val_lt]
  have := colH_anti lam (show c ≤ c + 1 by omega)
  omega

/-- **The index set of the path family**: Pieri paths with a standard filling of their end weight. -/
abbrev PathIdx (n N : ℕ) (vec : ℕ → Bool) (B : ℕ → ℕ) :=
  Σ P : PieriPath n N vec B, {I // IsStdFilling (P.mu N) I}

/-- **The path family** `Ψ(P, I)`. -/
def pathFam (R : Type*) [CommRing R] (x : PathIdx n N vec B) : MvPolynomial (ℕ × Fin n) R :=
  pathPoly R x.1.mu N x.2.1

/-- **The number of pairs (Pieri path, standard filling)** is `∏_{t < N} C(B_t + m, m)` in `m + 1` coordinates, the
number of monomials of multidegree `B` (T2 (ii)). -/
theorem card_pathIdx {m : ℕ} (N : ℕ) (vec : ℕ → Bool) (B : ℕ → ℕ) :
    Nat.card (PathIdx (m + 1) N vec B) = ∏ t ∈ range N, (B t + m).choose m := by
  have : ∀ P : PieriPath (m + 1) N vec B, Finite {I // IsStdFilling (P.mu N) I} :=
    fun P => (card_stdFilling (P.antitone N)).1
  rw [Nat.card_sigma, ← sum_dimW_paths]
  exact Finset.sum_congr rfl fun P _ => (card_stdFilling (P.antitone N)).2

end Index

end

end PathBasis
