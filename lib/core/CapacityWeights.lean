import CapStates

/-!
# Capacity-constrained spans of the path basis (T3)

For letters `0, …, N − 1` (the conventions of `PathBasis`), checkpoints `chk` (prefix lengths `i ≤ N`, prefix
`Set.Iio i`) and integers `θ_i`, `M_i`: the polynomials of multidegree `B` with `θ_i ≤ val_{<i} G` and
`top_{<i} G ≤ M_i` at the checkpoints are exactly the span of the path polynomials `Ψ(P, I)` whose path has
`θ_i ≤ μ_i(n − 1)` and `μ_i(0) ≤ M_i`, over every domain.

**Conventions.** `GenCoeff = SymbolData.GenCoeff ℕ R n`; `gtr`, `gcomp`, `twWt` are those of `TwistWeights`, read
through the prefix `S = Set.Iio i`. Dominance `ν ⊴ μ` (`DomLe`): equal totals and `Σ_{a ≤ k} ν_a ≤ Σ_{a ≤ k} μ_a` for
every `k`. The *top weight* of the column `c` at the weight `λ` is `τ_c(λ) = [a < colH λ c] − [c ≤ 0]` (`tau`); over
the column range they add up to `λ` (`sum_tau`).

**Main results.**
* *(E1)* Every weight of the generic translate through the first `i` letters of `Ψ(P, I)` (any filling) is dominated
  by `μ_i` (`gcomp_pathPoly_domLe`), over every commutative ring. Route: a column state is a run (`CapStates.run`);
  through the first `i` letters its translate is `det(g)^{#con}·Λ_A` of the old state (`CapStates.run_transform`,
  `A = adj g` for the columns `c ≥ 1`, `A = gᵀ` for `c ≤ 0`, `gtr_run`); the coordinate `J` of the stage-`i` state has
  weight `±[J]` and `|J|` is the height (or its complement), so its weights are dominated by `τ_c`; the later letters
  have weight `0`; dominance is additive.
* *(V4)* `val_{<i} Ψ(P, I) ≥ μ_i(n − 1)` and `top_{<i} Ψ(P, I) ≤ μ_i(0)` (`valS_pathPoly`, `topS_pathPoly`): dominance
  bounds the last coordinate below and the first above, then `TwistWeights.le_valS_of`, `topS_le_of`.
-/

namespace CapacitySpan

open MvPolynomial Finset TwistedDegree PathBasis TwistWeights CapStates

noncomputable section

/-! ## Dominance -/

section Dom

variable {n : ℕ}

/-- **Dominance** `ν ⊴ μ`: equal totals, partial sums of `ν` below those of `μ`. -/
def DomLe (ν μ : Fin n → ℤ) : Prop :=
  ∑ a, ν a = ∑ a, μ a ∧ ∀ k : ℕ, ∑ a with a.val ≤ k, ν a ≤ ∑ a with a.val ≤ k, μ a

/-- **Dominance is reflexive.** -/
theorem DomLe.refl (μ : Fin n → ℤ) : DomLe μ μ := ⟨rfl, fun _ => le_rfl⟩

/-- **Dominance is transitive.** -/
theorem DomLe.trans {ν μ κ : Fin n → ℤ} (h1 : DomLe ν μ) (h2 : DomLe μ κ) : DomLe ν κ :=
  ⟨h1.1.trans h2.1, fun k => (h1.2 k).trans (h2.2 k)⟩

/-- **Dominance is additive.** -/
theorem DomLe.add {ν μ ν' μ' : Fin n → ℤ} (h1 : DomLe ν μ) (h2 : DomLe ν' μ') : DomLe (ν + ν') (μ + μ') := by
  refine ⟨by simp only [Pi.add_apply, Finset.sum_add_distrib, h1.1, h2.1], fun k => ?_⟩
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  exact add_le_add (h1.2 k) (h2.2 k)

/-- **The partial sums below `v`** are dominated too. -/
theorem DomLe.lt_sum {ν μ : Fin n → ℤ} (h : DomLe ν μ) (v : ℕ) :
    ∑ a with a.val < v, ν a ≤ ∑ a with a.val < v, μ a := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp
  · have e : ∀ f : Fin n → ℤ, ∑ a with a.val < v, f a = ∑ a with a.val ≤ v - 1, f a := fun f =>
      Finset.sum_congr (by ext a; simp only [mem_filter, mem_univ, true_and]; omega) fun _ _ => rfl
    rw [e, e]
    exact h.2 _

/-- **A coordinate from the partial sums.** -/
theorem sum_le_val_eq (f : Fin n → ℤ) (a : Fin n) :
    ∑ b with b.val ≤ a.val, f b = f a + ∑ b with b.val < a.val, f b := by
  rw [← Finset.sum_insert (by simp)]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext b
  simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
  omega

/-- **Dominance is antisymmetric.** -/
theorem DomLe.antisymm {ν μ : Fin n → ℤ} (h1 : DomLe ν μ) (h2 : DomLe μ ν) : ν = μ := by
  funext a
  have hk := le_antisymm (h1.2 a.val) (h2.2 a.val)
  have hl := le_antisymm (h1.lt_sum a.val) (h2.lt_sum a.val)
  rw [sum_le_val_eq, sum_le_val_eq, hl] at hk
  linarith

/-- **Dominance bounds the first coordinate above.** -/
theorem DomLe.first_le [NeZero n] {ν μ : Fin n → ℤ} (h : DomLe ν μ) : ν 0 ≤ μ 0 := by
  have := h.2 ((0 : Fin n) : ℕ)
  rw [sum_le_val_eq ν 0, sum_le_val_eq μ 0] at this
  simpa using this

/-- **Dominance bounds the last coordinate below.** -/
theorem DomLe.last_ge [NeZero n] {ν μ : Fin n → ℤ} (h : DomLe ν μ) :
    μ (LetterFock.lastC n) ≤ ν (LetterFock.lastC n) := by
  have hu : (univ.filter fun a : Fin n => a.val ≤ (LetterFock.lastC n).val) = univ := by
    ext b
    simp only [mem_filter, mem_univ, true_and, iff_true]
    exact Nat.le_sub_one_of_lt b.isLt
  have e : ∀ f : Fin n → ℤ, ∑ a, f a = f (LetterFock.lastC n) + ∑ a with a.val < (LetterFock.lastC n).val, f a :=
    fun f => by rw [← sum_le_val_eq, hu]
  have h1 := h.1
  rw [e ν, e μ] at h1
  have := h.lt_sum (LetterFock.lastC n).val
  linarith

/-- **The indicator of a set is dominated by the initial segment of its size.** -/
theorem ind_domLe (J : Finset (Fin n)) : DomLe (ind J) (ind (univ.filter fun a : Fin n => a.val < J.card)) := by
  have hJ : J.card ≤ n := (card_le_univ J).trans (by simp)
  have hs : ∀ (T : Finset (Fin n)) (p : Fin n → Prop) [DecidablePred p],
      ∑ a with p a, ind T a = ((univ.filter p).filter (· ∈ T)).card := fun T p _ => by
    simp only [ind]; rw [Finset.sum_boole]
  refine ⟨?_, fun k => ?_⟩
  · have e : ∀ T : Finset (Fin n), ∑ a, ind T a = T.card := fun T => by
      simp only [ind]; rw [Finset.sum_boole]; simp
    rw [e, e, Fin.card_filter_val_lt]
    omega
  · rw [hs, hs]
    have h1 : ((univ.filter fun a : Fin n => a.val ≤ k).filter (· ∈ J)).card ≤ min J.card (k + 1) := by
      refine le_min (card_le_card (filter_subset_filter _ (subset_univ _) |>.trans ?_)) ?_
      · intro a; simp
      · calc _ ≤ (univ.filter fun a : Fin n => a.val ≤ k).card := card_filter_le _ _
          _ = min n (k + 1) := by
              rw [show (univ.filter fun a : Fin n => a.val ≤ k) = univ.filter fun a : Fin n => a.val < k + 1 by
                ext a; simp only [mem_filter, mem_univ, true_and]; omega, Fin.card_filter_val_lt]
          _ ≤ k + 1 := min_le_right _ _
    have h2 : ((univ.filter fun a : Fin n => a.val ≤ k).filter (· ∈ univ.filter fun a : Fin n => a.val < J.card)).card
        = min J.card (k + 1) := by
      rw [show ((univ.filter fun a : Fin n => a.val ≤ k).filter (· ∈ univ.filter fun a : Fin n => a.val < J.card)) =
        univ.filter fun a : Fin n => a.val < min J.card (k + 1) by
          ext a; simp only [mem_filter, mem_univ, true_and]; omega, Fin.card_filter_val_lt]
      omega
    rw [h2]
    exact_mod_cast h1

/-- **The negative indicator** is the indicator of the complement, shifted. -/
theorem neg_ind (J : Finset (Fin n)) : -ind J = ind Jᶜ - fun _ => 1 := by
  funext a
  simp only [ind, Pi.neg_apply, Pi.sub_apply, mem_compl]
  split_ifs <;> simp

/-- **The height** of a weight: the sum of its partial sums; strictly monotone for dominance. -/
def hgt (ν : Fin n → ℤ) : ℤ := ∑ k ∈ range n, ∑ a with a.val ≤ k, ν a

/-- **The height is additive.** -/
theorem hgt_add (ν ν' : Fin n → ℤ) : hgt (ν + ν') = hgt ν + hgt ν' := by
  simp only [hgt, Pi.add_apply, Finset.sum_add_distrib]

/-- **Dominance raises the height.** -/
theorem DomLe.hgt_le {ν μ : Fin n → ℤ} (h : DomLe ν μ) : hgt ν ≤ hgt μ := Finset.sum_le_sum fun k _ => h.2 k

/-- **Dominance with equal heights is equality.** -/
theorem DomLe.eq_of_hgt_le {ν μ : Fin n → ℤ} (h : DomLe ν μ) (h' : hgt μ ≤ hgt ν) : ν = μ := by
  have hk : ∀ k ∈ range n, ∑ a with a.val ≤ k, ν a = ∑ a with a.val ≤ k, μ a := by
    have hsum : ∑ k ∈ range n, (∑ a with a.val ≤ k, μ a - ∑ a with a.val ≤ k, ν a) = 0 := by
      rw [Finset.sum_sub_distrib]
      have := h.hgt_le
      unfold hgt at this h'
      linarith
    intro k hk
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sub_nonneg.2 (h.2 k))).1 hsum k hk
    linarith
  refine h.antisymm ⟨h.1.symm, fun k => ?_⟩
  by_cases hkn : k < n
  · exact (hk k (mem_range.2 hkn)).ge
  · have e : ∀ f : Fin n → ℤ, ∑ a with a.val ≤ k, f a = ∑ a, f a := fun f => by
      rw [Finset.filter_true_of_mem fun a _ => by have := a.isLt; omega]
    rw [e, e, h.1]

end Dom

/-! ## The top weights of the columns -/

section Tau

variable {n : ℕ}

/-- **The top weight of the column `c`** at the weight `λ`: `[a < colH λ c] − [c ≤ 0]`. -/
def tau (lam : Fin n → ℤ) (c : ℤ) : Fin n → ℤ :=
  fun a => (if a.val < colH lam c then 1 else 0) - (if c ≤ 0 then 1 else 0)

/-- **The top weights add up to the weight** over any window `[−T, T]` containing the entries. -/
theorem sum_tau_win (lam : Fin n → ℤ) (hanti : Antitone lam) {T : ℤ} (hT : ∀ a, |lam a| ≤ T) :
    ∑ c ∈ Icc (-T) T, tau lam c = lam := by
  funext a
  have hM := abs_le.1 (hT a)
  rw [Finset.sum_apply]
  simp only [tau, Finset.sum_sub_distrib, Finset.sum_boole]
  have e1 : (Icc (-T) T).filter (fun c => a.val < colH lam c) = Icc (-T) (lam a) := by
    ext c
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      refine ⟨h1, not_lt.1 fun h => ?_⟩
      have := colH_le_of_lt hanti h
      omega
    · rintro ⟨h1, h2⟩
      have := le_colH hanti h2
      exact ⟨⟨h1, by linarith⟩, by omega⟩
  have e2 : (Icc (-T) T).filter (fun c => c ≤ 0) = Icc (-T) 0 := by
    ext c
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      have : 0 ≤ T := by linarith
      exact ⟨⟨h1, by linarith⟩, h2⟩
  rw [e1, e2, Int.card_Icc, Int.card_Icc]
  have : 0 ≤ T := by linarith
  omega

/-- **The top weights add up to the weight** over the column range. -/
theorem sum_tau (μ : ℕ → Fin n → ℤ) {N i : ℕ} (hi : i ≤ N) (hanti : Antitone (μ i)) :
    ∑ c ∈ colRange μ N, tau (μ i) c = μ i :=
  sum_tau_win (μ i) hanti fun a => abs_le_colRange μ hi a

end Tau

/-! ## The generic translate of a column state -/

section Translate

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **The letter vectors** in `GenCoeff`. -/
abbrev Yv : ℕ → Fin n → SymbolData.GenCoeff ℕ R n := fun u a => X (u, a)

/-- **The matrix of the wedge steps**: `adj g` (`pol`, wedges at vector letters) or `gᵀ` (wedges at covector
letters). -/
def Aw (pol : Bool) : Matrix (Fin n) (Fin n) (SymbolData.GenCoeff ℕ R n) :=
  if pol then Matrix.of fun b d => MvPolynomial.C ((genMat R n).adjugate b d)
  else Matrix.of fun b d => MvPolynomial.C (genMat R n d b)

/-- **The matrix of the contraction steps**: `g` (`pol`) or `adj(g)ᵀ`. -/
def Ac (pol : Bool) : Matrix (Fin n) (Fin n) (SymbolData.GenCoeff ℕ R n) :=
  if pol then Matrix.of fun d e => MvPolynomial.C (genMat R n d e)
  else Matrix.of fun d e => MvPolynomial.C ((genMat R n).adjugate e d)

/-- **`Aw·Ac = det(g)·1`.** -/
theorem Aw_mul_Ac (pol : Bool) :
    Aw (R := R) (n := n) pol * Ac pol =
      (MvPolynomial.C (genMat R n).det : SymbolData.GenCoeff ℕ R n) •
        (1 : Matrix (Fin n) (Fin n) (SymbolData.GenCoeff ℕ R n)) := by
  have hadj : ∀ b e, ∑ d, (genMat R n).adjugate b d * genMat R n d e = if b = e then (genMat R n).det else 0 :=
    fun b e => by
      rw [← Matrix.mul_apply, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply]
      split_ifs <;> simp
  ext b e
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
  cases pol
  · simp only [Aw, Ac, Bool.false_eq_true, ite_false, Matrix.of_apply, ← map_mul]
    rw [← map_sum, show (∑ d, genMat R n d b * (genMat R n).adjugate e d) =
      ∑ d, (genMat R n).adjugate e d * genMat R n d b from Finset.sum_congr rfl fun _ _ => mul_comm _ _, hadj]
    by_cases h : b = e
    · subst h; simp
    · simp [h, Ne.symm h]
  · simp only [Aw, Ac, ite_true, Matrix.of_apply, ← map_mul]
    rw [← map_sum, hadj]
    split_ifs <;> simp

/-- **The translate of a letter variable** through the prefix `Set.Iio i`. -/
theorem gtr_X_lt (vec : ℕ → Bool) {i u : ℕ} (hu : u < i) (a : Fin n) :
    gtr (R := R) vec (Set.Iio i) (X (u, a)) =
      if vec u then ∑ b, X (u, b) * MvPolynomial.C ((genMat R n).adjugate b a)
      else ∑ b, MvPolynomial.C (genMat R n a b) * X (u, b) := by
  simp [gtr, hu]

/-- **The later letters are fixed** by the translate. -/
theorem gtr_X_ge (vec : ℕ → Bool) {i u : ℕ} (hu : i ≤ u) (a : Fin n) :
    gtr (R := R) vec (Set.Iio i) (X (u, a)) = X (u, a) := by
  simp [gtr, show ¬ u < i by omega]

/-- **The later letter vectors are fixed** by the translate. -/
theorem gtr_ge_eq (vec : ℕ → Bool) {i u : ℕ} (hu : i ≤ u) :
    (fun a => gtr (R := R) (n := n) vec (Set.Iio i) (X (u, a))) = Yv u := by
  funext a
  rw [gtr_X_ge vec hu a]

/-- **Constants are fixed** by the translate. -/
theorem gtr_C (vec : ℕ → Bool) (S : Set ℕ) (r : R) :
    gtr (n := n) vec S (MvPolynomial.C r) = MvPolynomial.C (MvPolynomial.C r) := by
  simp [gtr]

/-- **Constants are fixed** by the translate (any letters). -/
theorem gtr_C' {ι : Type*} (vec : ι → Bool) (S : Set ι) (r : R) :
    gtr (n := n) vec S (MvPolynomial.C r) = MvPolynomial.C (MvPolynomial.C r) := by
  simp [gtr]

/-- **(CE for the translate)** If the wedge steps before `i` sit at letters of type `pol` and the contraction steps at
letters of the other type, then through the prefix `Set.Iio i`, `κ·gtr(run) = det(g)^{#con}·Λ_{Aw}(run)`. -/
theorem gtr_run (vec : ℕ → Bool) (pol : Bool) {st : ℕ → Step} {i : ℕ}
    (hst : ∀ u < i, (st u = .wed → vec u = pol) ∧ (st u = .con → vec u = !pol))
    {S0 : Finset (Fin n) → SymbolData.GenCoeff ℕ R n} {κ : SymbolData.GenCoeff ℕ R n}
    (hS0 : ∀ K, Lam (Aw pol) S0 K = κ * S0 K) (K : Finset (Fin n)) :
    κ * run (fun u a => gtr vec (Set.Iio i) (X (u, a))) st S0 i K =
      MvPolynomial.C (genMat R n).det ^ ncon st i * Lam (Aw pol) (run Yv st S0 i) K := by
  refine run_transform (Aw_mul_Ac pol) hS0 (fun u hu => ⟨fun h => ?_, fun h => ?_⟩) K
  · have hv := (hst u hu).1 h
    funext d
    rw [gtr_X_lt vec hu]
    cases pol <;> simp [hv, Aw, mul_comm]
  · have hv := (hst u hu).2 h
    funext d
    rw [gtr_X_lt vec hu]
    cases pol <;> simp [hv, Ac, mul_comm]

/-- **`Λ_A [∅] = [∅]`.** -/
theorem Lam_st0 (A : Matrix (Fin n) (Fin n) (SymbolData.GenCoeff ℕ R n)) (K : Finset (Fin n)) :
    Lam A st0 K = 1 * st0 K := by
  show ∑ J, st0 J * W A J K = 1 * st0 K
  rw [one_mul, Finset.sum_eq_single ∅ (fun J _ hJ => by simp [st0, hJ]) (by simp)]
  simp [st0, W_empty]

/-- **The entries of `Aw` are constants**, so the wedges of its rows are. -/
theorem W_Aw_isWH (vec : ℕ → Bool) (S : Set ℕ) (pol : Bool) (J K : Finset (Fin n)) :
    IsWeightedHomogeneous (twWt vec S) (W (Aw (R := R) pol) J K) 0 := by
  have e : Aw (R := R) (n := n) pol = (if pol then (genMat R n).adjugate else (genMat R n).transpose).map
      MvPolynomial.C := by
    ext b d; cases pol <;> simp [Aw]
  rw [e, ← map_W]
  exact isWeightedHomogeneous_C _ _

end Translate

/-! ## The degrees of the column states of a path -/

section Deg

variable {Λ : Type*} [CommRing Λ] {n N : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **The degree of a column state**: the height for `c ≥ 1`, its complement for `c ≤ 0`. -/
def cdeg (μ : ℕ → Fin n → ℤ) (c : ℤ) (t : ℕ) : ℕ := if 1 ≤ c then colH (μ t) c else n - colH (μ t) c

/-- **A column height is at most `n`.** -/
theorem colH_le_n (w : Fin n → ℤ) (c : ℤ) : colH w c ≤ n := (card_le_univ _).trans (by simp)

/-- **The column states of a path are homogeneous** of the degree `cdeg`. -/
theorem run_isDeg (P : PieriPath n N vec B) (y : ℕ → Fin n → Λ) (c : ℤ) :
    ∀ t ≤ N, PathSpan.IsDeg (run y (colStep P.mu c) st0 t) (cdeg P.mu c t) := by
  intro t
  induction t with
  | zero =>
    intro _ J hJ
    simp only [run, st0]
    rw [ite_eq_right_iff]
    intro h
    subst h
    refine absurd ?_ hJ
    simp only [cdeg, P.zero, colH_zero, card_empty]
    split_ifs <;> simp
  | succ t ih =>
    intro ht
    have ih' := ih (by omega)
    have hs := P.colH_step (show t < N by omega) c
    have hle1 := colH_le_n (P.mu t) c
    have hle2 := colH_le_n (P.mu (t + 1)) c
    rw [run_succ]
    by_cases h1 : colH (P.mu t) c < colH (P.mu (t + 1)) c
    · rw [colStep_grow h1]
      by_cases hc : 1 ≤ c
      · simp only [hc, ite_true, Step.app]
        have e : cdeg P.mu c (t + 1) = cdeg P.mu c t + 1 := by
          simp only [cdeg, hc, ite_true]
          cases hv : vec t
          · have := (hs.2 hv).1; omega
          · have := (hs.1 hv).2; omega
        rw [e]
        exact ih'.wedge _
      · simp only [hc, ite_false, Step.app]
        have e : cdeg P.mu c t = cdeg P.mu c (t + 1) + 1 := by
          simp only [cdeg, hc, ite_false]
          cases hv : vec t
          · have := (hs.2 hv).1; omega
          · have := (hs.1 hv).2; omega
        rw [e] at ih'
        exact ih'.contr _
    · by_cases h2 : colH (P.mu (t + 1)) c < colH (P.mu t) c
      · rw [colStep_drop h2]
        by_cases hc : 1 ≤ c
        · simp only [hc, ite_true, Step.app]
          have e : cdeg P.mu c t = cdeg P.mu c (t + 1) + 1 := by
            simp only [cdeg, hc, ite_true]
            cases hv : vec t
            · have := (hs.2 hv).2; omega
            · have := (hs.1 hv).1; omega
          rw [e] at ih'
          exact ih'.contr _
        · simp only [hc, ite_false, Step.app]
          have e : cdeg P.mu c (t + 1) = cdeg P.mu c t + 1 := by
            simp only [cdeg, hc, ite_false]
            cases hv : vec t
            · have := (hs.2 hv).2; omega
            · have := (hs.1 hv).1; omega
          rw [e]
          exact ih'.wedge _
      · rw [colStep_keep (by omega)]
        have e : cdeg P.mu c (t + 1) = cdeg P.mu c t := by
          simp only [cdeg]; rw [show colH (P.mu (t + 1)) c = colH (P.mu t) c by omega]
        rw [e]
        exact ih'

/-- **The steps of a Pieri path** sit at letters of the right type: for `c ≥ 1` wedges at vector letters and
contractions at covector letters, for `c ≤ 0` the reverse. -/
theorem colStep_vec (P : PieriPath n N vec B) (c : ℤ) {u : ℕ} (hu : u < N) :
    (colStep P.mu c u = .wed → vec u = decide (1 ≤ c)) ∧ (colStep P.mu c u = .con → vec u = !decide (1 ≤ c)) := by
  have hs := P.colH_step hu c
  have hg : colH (P.mu u) c < colH (P.mu (u + 1)) c → vec u = true := fun h => by
    cases hv : vec u
    · have := (hs.2 hv).1; omega
    · rfl
  have hd : colH (P.mu (u + 1)) c < colH (P.mu u) c → vec u = false := fun h => by
    cases hv : vec u
    · rfl
    · have := (hs.1 hv).1; omega
  unfold colStep
  by_cases h1 : colH (P.mu u) c < colH (P.mu (u + 1)) c
  · by_cases hc : 1 ≤ c <;> simp [h1, hc, hg h1]
  · by_cases h2 : colH (P.mu (u + 1)) c < colH (P.mu u) c
    · by_cases hc : 1 ≤ c <;> simp [h1, h2, hc, hd h2]
    · simp [h1, h2]

end Deg

/-! ## (E1) The easy direction, and V4 -/

section E1

variable {R : Type*} [CommRing R] {n N : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **The weights present in a product** of factors dominated by `τ_c` are dominated by `Σ τ_c`. -/
theorem wtIn_prod {σ ι : Type*} (w : σ → Fin n → ℤ) (s : Finset ι) (f : ι → MvPolynomial σ R) (τ : ι → Fin n → ℤ)
    (h : ∀ c ∈ s, WtIn w (f c) {ν | DomLe ν (τ c)}) :
    WtIn w (∏ c ∈ s, f c) {ν | DomLe ν (∑ c ∈ s, τ c)} := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro u hu
    rw [prod_empty] at hu
    have hu0 : u = 0 := by
      by_contra hne
      exact mem_support_iff.1 hu (by simp [coeff_one, Ne.symm hne])
    subst hu0
    show DomLe _ _
    rw [map_zero, sum_empty]
    exact DomLe.refl 0
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    intro u hu
    obtain ⟨p, hp, q, hq, hpq⟩ := WtIn.mul (h a (mem_insert_self a s))
      (ih fun c hc => h c (mem_insert_of_mem hc)) u hu
    rw [← hpq]
    exact DomLe.add hp hq

/-- **The weight of a letter variable of the prefix.** -/
theorem isWH_X_lt (vec : ℕ → Bool) {i u : ℕ} (hu : u < i) (a : Fin n) :
    IsWeightedHomogeneous (twWt vec (Set.Iio i)) (X (u, a) : SymbolData.GenCoeff ℕ R n)
      (if vec u then Pi.single a 1 else -Pi.single a 1) := by
  have := isWeightedHomogeneous_X (R := MvPolynomial (Fin n × Fin n) R) (twWt vec (Set.Iio i)) (u, a)
  simpa [twWt, hu] using this

/-- **The later letter variables have weight `0`.** -/
theorem isWH_X_ge (vec : ℕ → Bool) {i u : ℕ} (hu : i ≤ u) (a : Fin n) :
    IsWeightedHomogeneous (twWt vec (Set.Iio i)) (X (u, a) : SymbolData.GenCoeff ℕ R n) 0 := by
  have := isWeightedHomogeneous_X (R := MvPolynomial (Fin n × Fin n) R) (twWt vec (Set.Iio i)) (u, a)
  simpa [twWt, show ¬ u < i by omega] using this

/-- **The prefix run of a column has the weights `±[J]`**: `+` if the wedges sit at vector letters (`pol`). -/
theorem run_isWH_prefix (vec : ℕ → Bool) (pol : Bool) {st : ℕ → Step} {i : ℕ}
    (hst : ∀ u < i, (st u = .wed → vec u = pol) ∧ (st u = .con → vec u = !pol))
    {S0 : Finset (Fin n) → SymbolData.GenCoeff ℕ R n} (δ : Fin n → ℤ)
    (hS0 : ∀ J, IsWeightedHomogeneous (twWt vec (Set.Iio i)) (S0 J) ((if pol then 1 else -1 : ℤ) • ind J + δ))
    (J : Finset (Fin n)) :
    IsWeightedHomogeneous (twWt vec (Set.Iio i)) (run Yv st S0 i J) ((if pol then 1 else -1 : ℤ) • ind J + δ) := by
  refine run_isWH _ _ δ hS0 (fun u hu => ⟨fun h a => ?_, fun h a => ?_⟩) J
  · have hv := (hst u hu).1 h
    have := isWH_X_lt (R := R) vec hu a
    cases pol <;> simpa [hv] using this
  · have hv := (hst u hu).2 h
    have := isWH_X_lt (R := R) vec hu a
    cases pol <;> simpa [hv] using this

/-- **`[∅]` has the weights `±[J]`.** -/
theorem isWH_st0 (w : ℕ × Fin n → Fin n → ℤ) (ε : ℤ) (J : Finset (Fin n)) :
    IsWeightedHomogeneous w (st0 J : SymbolData.GenCoeff ℕ R n) (ε • ind J + 0) := by
  by_cases hJ : J = ∅
  · subst hJ
    have : ind (∅ : Finset (Fin n)) = 0 := by funext a; simp [ind]
    simpa [st0, this] using isWeightedHomogeneous_one (MvPolynomial (Fin n × Fin n) R) w
  · simpa [st0, hJ] using isWeightedHomogeneous_zero (MvPolynomial (Fin n × Fin n) R) w _

/-- **The top weight in indicator form.** -/
theorem tau_eq (lam : Fin n → ℤ) (c : ℤ) :
    tau lam c = ind (univ.filter fun a : Fin n => a.val < colH lam c) + fun _ => -(if c ≤ 0 then 1 else 0) := by
  funext a
  simp only [tau, ind, mem_filter, mem_univ, true_and, Pi.add_apply]
  ring

/-- **The coordinate weights of the right size are dominated by the top weight.** -/
theorem domLe_tau (lam : Fin n → ℤ) (c : ℤ) (J : Finset (Fin n))
    (hcard : J.card = if 1 ≤ c then colH lam c else n - colH lam c) :
    DomLe ((if decide (1 ≤ c) then 1 else -1 : ℤ) • ind J + 0) (tau lam c) := by
  rw [add_zero, tau_eq]
  by_cases hc : 1 ≤ c
  · simp only [hc, ite_true] at hcard
    have h1 := ind_domLe J
    rw [hcard] at h1
    have e : (fun _ : Fin n => -(if c ≤ 0 then (1 : ℤ) else 0)) = 0 := by
      funext a; simp [show ¬ c ≤ 0 by omega]
    rw [e, add_zero, decide_eq_true hc]
    simpa using h1
  · simp only [hc, ite_false] at hcard
    have hcc : Jᶜ.card = colH lam c := by
      rw [card_compl, Fintype.card_fin, hcard]
      have := colH_le_n lam c
      omega
    have h1 := (ind_domLe Jᶜ).add (DomLe.refl (-fun _ : Fin n => (1 : ℤ)))
    rw [hcc] at h1
    have e : (fun _ : Fin n => -(if c ≤ 0 then (1 : ℤ) else 0)) = -fun _ => 1 := by
      funext a; simp [show c ≤ 0 by omega]
    rw [e, decide_eq_false hc]
    simp only [Bool.false_eq_true, ite_false, neg_smul, one_smul]
    rw [neg_ind, sub_eq_add_neg]
    exact h1

/-- **The weights of the prefix part of a translated column state.** -/
theorem prefix_wtIn (P : PieriPath n N vec B) {i : ℕ} (hi : i ≤ N) (c : ℤ) (J : Finset (Fin n)) :
    WtIn (twWt vec (Set.Iio i)) (run (fun u a => gtr (R := R) vec (Set.Iio i) (X (u, a))) (colStep P.mu c) st0 i J)
      {ν | DomLe ν (tau (P.mu i) c)} := by
  have hst : ∀ u < i, (colStep P.mu c u = .wed → vec u = decide (1 ≤ c)) ∧
      (colStep P.mu c u = .con → vec u = !decide (1 ≤ c)) := fun u hu => colStep_vec P c (by omega)
  have hCE := gtr_run vec (decide (1 ≤ c)) hst (Lam_st0 (R := R) _) J
  rw [one_mul] at hCE
  rw [hCE, Lam_def]
  refine WtIn.mul_left0 ?_ (WtIn.sum _ fun J' _ => ?_)
  · simpa using (isWeightedHomogeneous_C (twWt vec (Set.Iio i)) (genMat R n).det).pow (ncon (colStep P.mu c) i)
  have hJ' := run_isWH_prefix (R := R) vec (decide (1 ≤ c)) hst 0 (fun J => isWH_st0 _ _ J) J'
  have hW := W_Aw_isWH (R := R) vec (Set.Iio i) (decide (1 ≤ c)) J' J
  refine WtIn.of_isWH (hJ'.mul hW) fun hne => ?_
  have hne' : run (Yv (R := R)) (colStep P.mu c) st0 i J' ≠ 0 := fun h => hne (by rw [h, zero_mul])
  have hcard : J'.card = cdeg P.mu c i := by
    by_contra h
    exact hne' (run_isDeg P Yv c i hi J' h)
  rw [add_zero]
  exact domLe_tau _ c J' hcard

/-- **The weights of a translated column state** are dominated by the top weight of the column. -/
theorem colK_wtIn (P : PieriPath n N vec B) {i : ℕ} (hi : i ≤ N) (c : ℤ) (K : Finset (Fin n)) :
    WtIn (twWt vec (Set.Iio i)) (gtr (R := R) vec (Set.Iio i) (colK R P.mu c N K))
      {ν | DomLe ν (tau (P.mu i) c)} := by
  rw [colK, colSt_one_eq_run, map_run]
  have h0 : (fun J : Finset (Fin n) => gtr (R := R) vec (Set.Iio i) (st0 J : MvPolynomial (ℕ × Fin n) R)) =
      (st0 : Finset (Fin n) → SymbolData.GenCoeff ℕ R n) := by
    funext J; simp only [st0]; split_ifs <;> simp
  have hN : run (fun t a => gtr (R := R) (n := n) vec (Set.Iio i) (X (t, a))) (colStep P.mu c) st0 N =
      runFrom (Yv (R := R)) (colStep P.mu c) i
        (run (fun t a => gtr (R := R) (n := n) vec (Set.Iio i) (X (t, a))) (colStep P.mu c) st0 i) (N - i) := by
    have h := run_add (fun t a => gtr (R := R) (n := n) vec (Set.Iio i) (X (t, a))) (colStep P.mu c) st0 i (N - i)
    rw [Nat.add_sub_cancel' hi] at h
    rw [h]
    exact runFrom_congr _ _ _ _ fun u hu => gtr_ge_eq vec hu
  rw [h0, hN]
  exact runFrom_wtIn _ (fun u hu a => isWH_X_ge vec hu a) (fun J => prefix_wtIn P hi c J) _ _

/-- **(E1) The easy direction, dominance form** (any ring, any filling, standard or not): every weight of the generic
translate through the first `i` letters of `Ψ(P, I)` is dominated by `μ_i`. -/
theorem gcomp_pathPoly_domLe (P : PieriPath n N vec B) (I : ℤ → Finset (Fin n)) {i : ℕ} (hi : i ≤ N)
    {ν : Fin n → ℤ} (h : gcomp vec (Set.Iio i) ν (pathPoly R P.mu N I) ≠ 0) : DomLe ν (P.mu i) := by
  have hW : WtIn (twWt vec (Set.Iio i)) (gtr vec (Set.Iio i) (pathPoly R P.mu N I))
      {ν | DomLe ν (∑ c ∈ colRange P.mu N, tau (P.mu i) c)} := by
    rw [pathPoly, map_prod]
    exact wtIn_prod _ _ _ _ fun c _ => colK_wtIn P hi c (I c)
  rw [sum_tau P.mu hi (P.antitone i)] at hW
  obtain ⟨u, hu, hw⟩ := (weightedHomogeneousComponent_ne_zero_iff _ _ _).1 h
  exact hw ▸ hW u hu

/-- **V4 (`val`)**: `val_{<i} Ψ(P, I) ≥ μ_i(n − 1)` (N7's input). -/
theorem valS_pathPoly [NeZero n] (P : PieriPath n N vec B) (I : ℤ → Finset (Fin n)) {i : ℕ} (hi : i ≤ N) :
    ((P.mu i (LetterFock.lastC n) : ℤ) : WithTop ℤ) ≤ SymbolData.valS vec (Set.Iio i) (pathPoly R P.mu N I) :=
  le_valS_of vec _ _ _ fun _ hν => (gcomp_pathPoly_domLe P I hi hν).last_ge

/-- **V4 (`top`)**: `top_{<i} Ψ(P, I) ≤ μ_i(0)`. -/
theorem topS_pathPoly [NeZero n] (P : PieriPath n N vec B) (I : ℤ → Finset (Fin n)) {i : ℕ} (hi : i ≤ N) :
    SymbolData.topS vec (Set.Iio i) (pathPoly R P.mu N I) ≤ ((P.mu i 0 : ℤ) : WithBot ℤ) :=
  topS_le_of vec _ _ _ fun _ hν => (gcomp_pathPoly_domLe P I hi hν).first_le

end E1

/-! ## The capacity sets, the easy inclusion and the conditional coefficient form -/

section Cap

open PathSpan

/-- **The capacity condition on a path** at the checkpoints `chk` (prefix lengths): `θ_i ≤ μ_i(n − 1)`,
`μ_i(0) ≤ M_i`. -/
def CapOK {m N : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ} (chk : Finset ℕ) (θ M : ℕ → ℤ) (P : PieriPath (m + 1) N vec B) :
    Prop :=
  ∀ i ∈ chk, θ i ≤ P.mu i (LetterFock.lastC (m + 1)) ∧ P.mu i 0 ≤ M i

variable (R : Type*) [CommRing R] (m N : ℕ) (vec : ℕ → Bool) (B : ℕ → ℕ)

/-- **The capacity set**: the multidegree-`B` polynomials with `θ_i ≤ val_{<i}` and `top_{<i} ≤ M_i` at the
checkpoints. -/
def capSet (chk : Finset ℕ) (θ M : ℕ → ℤ) : Set (MvPolynomial (ℕ × Fin (m + 1)) R) :=
  {G | G ∈ weightedHomogeneousSubmodule R (LetterFock.rowW ℕ (m + 1)) (mdeg N B) ∧
    ∀ i ∈ chk, (θ i : WithTop ℤ) ≤ SymbolData.valS vec (Set.Iio i) G ∧
      SymbolData.topS vec (Set.Iio i) G ≤ (M i : WithBot ℤ)}

variable {R m N vec B}

/-- **The twisted exponents of a sum.** -/
theorem twistExps_add_subset {ι : Type*} {n : ℕ} (vec : ι → Bool) (S : Set ι) (c : Fin n)
    (F G : MvPolynomial (ι × Fin n) R) :
    SymbolData.twistExps vec S c (F + G) ⊆ SymbolData.twistExps vec S c F ∪ SymbolData.twistExps vec S c G := by
  classical
  unfold SymbolData.twistExps
  rw [map_add, AddMonoidAlgebra.coeff_add]
  exact Finsupp.support_add

/-- **The twisted exponents of a multiple.** -/
theorem twistExps_smul_subset {ι : Type*} {n : ℕ} (vec : ι → Bool) (S : Set ι) (c : Fin n) (r : R)
    (F : MvPolynomial (ι × Fin n) R) :
    SymbolData.twistExps vec S c (r • F) ⊆ SymbolData.twistExps vec S c F := by
  intro e he
  rw [SymbolData.twistExps, Finsupp.mem_support_iff, smul_eq_C_mul, map_mul] at he
  rw [SymbolData.twistExps, Finsupp.mem_support_iff]
  intro h0
  apply he
  have hC : SymbolData.twistSub vec S c (MvPolynomial.C r) =
      LaurentPolynomial.C (MvPolynomial.C (MvPolynomial.C r)) := by
    simp [SymbolData.twistSub]
  rw [hC, ← LaurentPolynomial.smul_eq_C_mul, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, h0, smul_zero]

/-- **The capacity set is a submodule** (over any commutative ring). -/
def capSub (chk : Finset ℕ) (θ M : ℕ → ℤ) : Submodule R (MvPolynomial (ℕ × Fin (m + 1)) R) where
  carrier := capSet R m N vec B chk θ M
  add_mem' {F G} hF hG := by
    refine ⟨add_mem hF.1 hG.1, fun i hi => ⟨Finset.le_min fun e he => ?_, Finset.max_le fun e he => ?_⟩⟩
    · rcases Finset.mem_union.1 (twistExps_add_subset vec _ _ F G he) with h | h
      · exact Finset.le_min_iff.1 (hF.2 i hi).1 e h
      · exact Finset.le_min_iff.1 (hG.2 i hi).1 e h
    · rcases Finset.mem_union.1 (twistExps_add_subset vec _ _ F G he) with h | h
      · exact Finset.max_le_iff.1 (hF.2 i hi).2 e h
      · exact Finset.max_le_iff.1 (hG.2 i hi).2 e h
  zero_mem' := ⟨zero_mem _, fun i _ => by simp [SymbolData.valS_zero, SymbolData.topS_zero]⟩
  smul_mem' r F hF := by
    refine ⟨Submodule.smul_mem _ r hF.1, fun i hi => ⟨Finset.le_min fun e he => ?_, Finset.max_le fun e he => ?_⟩⟩
    · exact Finset.le_min_iff.1 (hF.2 i hi).1 e (twistExps_smul_subset vec _ _ r F he)
    · exact Finset.max_le_iff.1 (hF.2 i hi).2 e (twistExps_smul_subset vec _ _ r F he)

/-- **An admissible path polynomial lies in the capacity set** (V4). -/
theorem pathFam_mem_capSet {chk : Finset ℕ} (hchk : ∀ i ∈ chk, i ≤ N) {θ M : ℕ → ℤ}
    {x : PathIdx (m + 1) N vec B} (hx : CapOK chk θ M x.1) : pathFam R x ∈ capSet R m N vec B chk θ M := by
  refine ⟨(mem_weightedHomogeneousSubmodule _ _ _ _).2 (x.1.pathPoly_isWH x.2.1), fun i hi => ⟨?_, ?_⟩⟩
  · exact (WithTop.coe_le_coe.2 (hx i hi).1).trans (valS_pathPoly x.1 x.2.1 (hchk i hi))
  · exact (topS_pathPoly x.1 x.2.1 (hchk i hi)).trans (WithBot.coe_le_coe.2 (hx i hi).2)

variable (R m N vec B) in
/-- **The easy inclusion over any ring**: the span of the admissible path polynomials lies in the capacity set. -/
theorem span_subset_capSet {chk : Finset ℕ} (hchk : ∀ i ∈ chk, i ≤ N) (θ M : ℕ → ℤ) :
    (Submodule.span R (pathFam R '' {x : PathIdx (m + 1) N vec B | CapOK chk θ M x.1}) : Set _) ⊆
      capSet R m N vec B chk θ M := by
  have : Submodule.span R (pathFam R '' {x : PathIdx (m + 1) N vec B | CapOK chk θ M x.1}) ≤
      capSub (R := R) (m := m) (N := N) (vec := vec) (B := B) chk θ M := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact pathFam_mem_capSet hchk hx
  exact this

/-- **The generic translate is `R`-linear.** -/
theorem gcomp_smul {ι : Type*} {n : ℕ} (vec : ι → Bool) (S : Set ι) (ν : Fin n → ℤ) (r : R)
    (F : MvPolynomial (ι × Fin n) R) : gcomp vec S ν (r • F) = r • gcomp vec S ν F := by
  rw [gcomp, gcomp, smul_eq_C_mul, map_mul, gtr_C', weightedHomogeneousComponent_C_mul, Algebra.smul_def,
    MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]

/-- **The generic translate is additive.** -/
theorem gcomp_sum {ι κ : Type*} {n : ℕ} (vec : ι → Bool) (S : Set ι) (ν : Fin n → ℤ) (s : Finset κ)
    (F : κ → MvPolynomial (ι × Fin n) R) : gcomp vec S ν (∑ x ∈ s, F x) = ∑ x ∈ s, gcomp vec S ν (F x) := by
  simp only [gcomp, map_sum]

/-- **The path-basis expansion** of a multidegree-`B` polynomial. -/
theorem eq_sum_repr [Fintype (PathIdx (m + 1) N vec B)] {G : MvPolynomial (ℕ × Fin (m + 1)) R}
    (hG : G ∈ weightedHomogeneousSubmodule R (LetterFock.rowW ℕ (m + 1)) (mdeg N B)) :
    G = ∑ x, (pathFam_basis R m N vec B).repr ⟨G, hG⟩ x • pathFam R x := by
  have h := congrArg Subtype.val ((pathFam_basis R m N vec B).sum_repr ⟨G, hG⟩)
  rw [Submodule.coe_sum] at h
  simp only [Submodule.coe_smul, pathFam_basis_apply] at h
  exact h.symm

/-- **(T3, coefficient form, from the independence of the top components)**: over a domain, if for every checkpoint
`i` and dominant `μ₀` the weight-`μ₀` components of the translates of the `Ψ(x)` with `μ_i = μ₀` are independent,
the path-basis coordinates of a member of the capacity set vanish off the admissible paths. Route: the
dominance-maximal argument (choose `x₀` in the support with `μ_i(x₀) ⊵ μ_i(x₁)` of largest height; its top component
survives by (E1) and the independence, so `μ_i(x₀)` is a weight of `gtr G`; capacity conditions are dominance-lower). -/
theorem repr_eq_zero_of_indep [IsDomain R] {chk : Finset ℕ} (hchk : ∀ i ∈ chk, i ≤ N) {θ M : ℕ → ℤ}
    {G : MvPolynomial (ℕ × Fin (m + 1)) R} (hG : G ∈ capSet R m N vec B chk θ M)
    (hE3 : ∀ i ≤ N, ∀ μ₀ : Fin (m + 1) → ℤ,
      LinearIndependent R (fun x : {x : PathIdx (m + 1) N vec B // x.1.mu i = μ₀} =>
        gcomp vec (Set.Iio i) μ₀ (pathFam R x.1)))
    (x : PathIdx (m + 1) N vec B) (hx : ¬ CapOK chk θ M x.1) : (pathFam_basis R m N vec B).repr ⟨G, hG.1⟩ x = 0 := by
  classical
  let _ : Fintype (PathIdx (m + 1) N vec B) := Fintype.ofFinite _
  set c := (pathFam_basis R m N vec B).repr ⟨G, hG.1⟩
  have hGsum := eq_sum_repr (R := R) (vec := vec) hG.1
  have key : ∀ i ∈ chk, ∀ x₁, c x₁ ≠ 0 →
      θ i ≤ x₁.1.mu i (LetterFock.lastC (m + 1)) ∧ x₁.1.mu i 0 ≤ M i := by
    intro i hi x₁ hx₁
    by_contra hbad
    obtain ⟨x₀, hx₀A, hmax⟩ := Finset.exists_max_image
      (univ.filter fun x : PathIdx (m + 1) N vec B => c x ≠ 0 ∧ DomLe (x₁.1.mu i) (x.1.mu i))
      (fun x => hgt (x.1.mu i)) ⟨x₁, by simp [hx₁, DomLe.refl]⟩
    have hx₀ := (mem_filter.1 hx₀A).2
    have hzero : ∀ x : PathIdx (m + 1) N vec B, x.1.mu i ≠ x₀.1.mu i →
        c x • gcomp vec (Set.Iio i) (x₀.1.mu i) (pathFam R x) = 0 := by
      intro x hxμ
      by_cases hcx : c x = 0
      · rw [hcx, zero_smul]
      by_cases hgx : gcomp vec (Set.Iio i) (x₀.1.mu i) (pathFam R x) = 0
      · rw [hgx, smul_zero]
      exfalso
      have hd := gcomp_pathPoly_domLe x.1 x.2.1 (hchk i hi) hgx
      have hA : x ∈ univ.filter fun x : PathIdx (m + 1) N vec B => c x ≠ 0 ∧ DomLe (x₁.1.mu i) (x.1.mu i) :=
        mem_filter.2 ⟨mem_univ _, hcx, hx₀.2.trans hd⟩
      exact hxμ (hd.eq_of_hgt_le (hmax x hA)).symm
    have hcomp : gcomp vec (Set.Iio i) (x₀.1.mu i) G =
        ∑ x : {x : PathIdx (m + 1) N vec B // x.1.mu i = x₀.1.mu i},
          c x.1 • gcomp vec (Set.Iio i) (x₀.1.mu i) (pathFam R x.1) := by
      conv_lhs => rw [hGsum]
      rw [gcomp_sum]
      simp only [gcomp_smul]
      rw [← Finset.sum_subset (Finset.subset_univ (univ.filter fun x : PathIdx (m + 1) N vec B =>
        x.1.mu i = x₀.1.mu i)) fun x _ hx => hzero x (by simpa using hx)]
      exact Finset.sum_subtype _ (fun x => by simp) _
    have hne : gcomp vec (Set.Iio i) (x₀.1.mu i) G ≠ 0 := by
      rw [hcomp]
      intro h0
      exact hx₀.1 (linearIndependent_iff'.1 (hE3 i (hchk i hi) (x₀.1.mu i)) univ (fun x => c x.1) h0
        ⟨x₀, rfl⟩ (mem_univ _))
    have hval := (le_valS_iff vec _ G (θ i)).1 (hG.2 i hi).1 _ hne
    have htop := (topS_le_iff vec _ G (M i)).1 (hG.2 i hi).2 _ hne
    exact hbad ⟨hval.trans hx₀.2.last_ge, hx₀.2.first_le.trans htop⟩
  by_contra hcx
  exact hx fun i hi => key i hi x hcx

variable (R m N vec B) in
/-- **(T3, from the independence of the top components)** the capacity set is the span of the admissible path
polynomials. -/
theorem capSet_eq_span_of_indep [IsDomain R] {chk : Finset ℕ} (hchk : ∀ i ∈ chk, i ≤ N) (θ M : ℕ → ℤ)
    (hE3 : ∀ i ≤ N, ∀ μ₀ : Fin (m + 1) → ℤ,
      LinearIndependent R (fun x : {x : PathIdx (m + 1) N vec B // x.1.mu i = μ₀} =>
        gcomp vec (Set.Iio i) μ₀ (pathFam R x.1))) :
    capSet R m N vec B chk θ M =
      (Submodule.span R (pathFam R '' {x : PathIdx (m + 1) N vec B | CapOK chk θ M x.1}) : Set _) := by
  classical
  refine Set.Subset.antisymm (fun G hG => ?_) (span_subset_capSet R m N vec B hchk θ M)
  let _ : Fintype (PathIdx (m + 1) N vec B) := Fintype.ofFinite _
  rw [eq_sum_repr (vec := vec) hG.1]
  refine Submodule.sum_mem _ fun x _ => ?_
  by_cases hx : CapOK chk θ M x.1
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)
  · rw [repr_eq_zero_of_indep hchk hG hE3 x hx, zero_smul]
    exact zero_mem _

variable (m N vec B) in
/-- **Dimension = chain sum** (over a field): the admissible pairs (path, standard filling). -/
theorem finrank_capSpan (K : Type*) [Field K] (chk : Finset ℕ) (θ M : ℕ → ℤ) :
    Module.finrank K (Submodule.span K (pathFam K '' {x : PathIdx (m + 1) N vec B | CapOK chk θ M x.1})) =
      Nat.card {x : PathIdx (m + 1) N vec B // CapOK chk θ M x.1} := by
  classical
  let _ : Fintype (PathIdx (m + 1) N vec B) := Fintype.ofFinite _
  have hli : LinearIndependent K (fun x : {x : PathIdx (m + 1) N vec B // CapOK chk θ M x.1} => pathFam K x.1) := by
    have h := (pathVec_linearIndependent K m N vec B).map' (Submodule.subtype _) (Submodule.ker_subtype _)
    exact h.comp Subtype.val Subtype.val_injective
  have e : pathFam K '' {x : PathIdx (m + 1) N vec B | CapOK chk θ M x.1} =
      Set.range (fun x : {x : PathIdx (m + 1) N vec B // CapOK chk θ M x.1} => pathFam K x.1) := by
    ext p; simp
  rw [e, finrank_span_eq_card hli, Nat.card_eq_fintype_card]

variable (m N vec B) in
open Classical in
/-- **The chain sum**: the admissible pairs number `Σ_{P admissible} dimW(μ_N)`. -/
theorem card_capOK (chk : Finset ℕ) (θ M : ℕ → ℤ) :
    Nat.card {x : PathIdx (m + 1) N vec B // CapOK chk θ M x.1} =
      ∑ μ ∈ (pathSet (n := m + 1) vec B N).filter
          (fun μ => ∀ i ∈ chk, θ i ≤ μ i (LetterFock.lastC (m + 1)) ∧ μ i 0 ≤ M i),
        WeylCount.dimW (m + 1) (μ N) := by
  have : ∀ P : {P : PieriPath (m + 1) N vec B // CapOK chk θ M P}, Finite {I // IsStdFilling (P.1.mu N) I} :=
    fun P => (card_stdFilling (P.1.antitone N)).1
  rw [Nat.card_congr (Equiv.subtypeSigmaEquiv _ (CapOK chk θ M)), Nat.card_sigma]
  rw [show (∑ P : {P : PieriPath (m + 1) N vec B // CapOK chk θ M P}, Nat.card {I // IsStdFilling (P.1.mu N) I}) =
      ∑ P : {P : PieriPath (m + 1) N vec B // CapOK chk θ M P}, WeylCount.dimW (m + 1) (P.1.mu N) from
    Finset.sum_congr rfl fun P _ => (card_stdFilling (P.1.antitone N)).2]
  rw [← Finset.sum_subtype (univ.filter (CapOK chk θ M)) (fun P => by simp)
    (fun P : PieriPath (m + 1) N vec B => WeylCount.dimW (m + 1) (P.mu N))]
  refine Finset.sum_bij' (fun P _ => P.mu) (fun μ hμ => PieriPath.equiv.symm ⟨μ, (mem_filter.1 hμ).1⟩)
    (fun P hP => ?_) (fun μ hμ => ?_) (fun P _ => rfl) (fun μ _ => rfl) (fun P _ => rfl)
  · exact mem_filter.2 ⟨mem_pathSet.2 P.isPath, (mem_filter.1 hP).2⟩
  · exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hμ).2⟩

/-- **The weighted components commute with coefficient maps.** -/
theorem weightedHomogeneousComponent_map {σ A A' M : Type*} [CommRing A] [CommRing A'] [AddCommMonoid M]
    (φ : A →+* A') (w : σ → M) (m : M) (p : MvPolynomial σ A) :
    weightedHomogeneousComponent w m (MvPolynomial.map φ p) =
      MvPolynomial.map φ (weightedHomogeneousComponent w m p) := by
  classical
  ext d
  simp only [coeff_weightedHomogeneousComponent, coeff_map]
  split_ifs <;> simp

/-- **The generic matrix is defined over `ℤ`**: coefficient maps carry it and its adjugate along. -/
theorem map_genMat {A A' : Type*} [CommRing A] [CommRing A'] (φ : A →+* A') {n : ℕ} (a b : Fin n) :
    MvPolynomial.map φ (genMat A n a b) = genMat A' n a b ∧
      MvPolynomial.map φ ((genMat A n).adjugate a b) = (genMat A' n).adjugate a b := by
  have e : (MvPolynomial.map φ).mapMatrix (genMat A n) = genMat A' n := by
    ext a b; simp [genMat]
  refine ⟨by simp [genMat], ?_⟩
  have h := RingHom.map_adjugate (R := MvPolynomial (Fin n × Fin n) A) (S := MvPolynomial (Fin n × Fin n) A')
    (MvPolynomial.map φ) (genMat A n)
  rw [e] at h
  rw [← h]
  rfl

/-- **The generic translate commutes with coefficient maps.** -/
theorem gtr_map {A A' : Type*} [CommRing A] [CommRing A'] (φ : A →+* A') {ι : Type*} {n : ℕ} (vec : ι → Bool)
    (S : Set ι) (F : MvPolynomial (ι × Fin n) A) :
    gtr vec S (MvPolynomial.map φ F) = MvPolynomial.map (MvPolynomial.map φ) (gtr vec S F) := by
  classical
  change ((gtr vec S).comp (MvPolynomial.map φ)) F = ((MvPolynomial.map (MvPolynomial.map φ)).comp (gtr vec S)) F
  congr 1
  refine MvPolynomial.ringHom_ext (fun r => by simp [gtr]) fun v => ?_
  obtain ⟨l, a⟩ := v
  simp only [RingHom.comp_apply, map_X, gtr, coe_eval₂Hom, eval₂_X]
  split_ifs <;> simp [(map_genMat φ _ _).1, (map_genMat φ _ _).2]

/-- **The weight components commute with coefficient maps.** -/
theorem gcomp_map {A A' : Type*} [CommRing A] [CommRing A'] (φ : A →+* A') {ι : Type*} {n : ℕ} (vec : ι → Bool)
    (S : Set ι) (ν : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) A) :
    gcomp vec S ν (MvPolynomial.map φ F) = MvPolynomial.map (MvPolynomial.map φ) (gcomp vec S ν F) := by
  rw [gcomp, gcomp, gtr_map, weightedHomogeneousComponent_map]

variable (m N vec B) in
/-- **Saturation**: membership is detected after an injective coefficient map between domains (`val`/`top` do not
change), so the `O`-capacity set is the `Kf`-capacity set intersected with the `O`-polynomials. -/
theorem mem_capSet_map_iff {O K : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) (chk : Finset ℕ) (θ M : ℕ → ℤ)
    (G : MvPolynomial (ℕ × Fin (m + 1)) O) :
    G ∈ capSet O m N vec B chk θ M ↔ MvPolynomial.map (algebraMap O K) G ∈ capSet K m N vec B chk θ M := by
  have hinj2 : Function.Injective (MvPolynomial.map (σ := ℕ × Fin (m + 1)) (MvPolynomial.map (σ := Fin (m + 1) ×
      Fin (m + 1)) (algebraMap O K))) := MvPolynomial.map_injective _ (MvPolynomial.map_injective _ hinj)
  have hg : ∀ i ν, gcomp vec (Set.Iio i) ν (MvPolynomial.map (algebraMap O K) G) ≠ 0 ↔
      gcomp vec (Set.Iio i) ν G ≠ 0 := fun i ν => by
    rw [gcomp_map, Ne, Ne, (map_eq_zero_iff _ hinj2)]
  have hwh : G ∈ weightedHomogeneousSubmodule O (LetterFock.rowW ℕ (m + 1)) (mdeg N B) ↔
      MvPolynomial.map (algebraMap O K) G ∈ weightedHomogeneousSubmodule K (LetterFock.rowW ℕ (m + 1)) (mdeg N B) := by
    simp only [mem_weightedHomogeneousSubmodule, IsWeightedHomogeneous, coeff_map]
    exact forall_congr' fun d => by rw [Ne, Ne, map_eq_zero_iff _ hinj]
  refine and_congr hwh (forall₂_congr fun i _ => and_congr ?_ ?_)
  · rw [le_valS_iff, le_valS_iff]
    exact forall_congr' fun ν => by rw [hg]
  · rw [topS_le_iff, topS_le_iff]
    exact forall_congr' fun ν => by rw [hg]

end Cap

end

end CapacitySpan
