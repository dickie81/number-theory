import TwistWeights
import PathStraighten

/-!
# Column states under a change of frame (the CE step of T3)

Generic tools for the capacity spans (`CapacitySpan`): column states run from an arbitrary initial state, the wedge
products of the rows of a matrix (`W`), the induced action `Λ_A` on states, and the transformation rule of a column
state when its letter vectors are transformed by a matrix (wedge steps) and a complementary one (contraction steps).

**Conventions** (those of `TwistedDegree`). A *state* is `Finset (Fin n) → Λ` over a commutative ring `Λ`, with
`wedge`, `contr` and the steps `Step` of `TwistedDegree`. A matrix `A` acts on row vectors, `(y·A)_d = Σ_b y_b A_{bd}`,
and `A'` on column vectors, `(A'·η)_d = Σ_e A'_{de} η_e`.

**Main results.**
* *Runs* (`run`, `runFrom`): `run y st S0 t` applies the steps `st` with the letter vectors `y` to `S0`; `colSt` with
  unit exponents is the run from `[∅]` (`colSt_one_eq_run`); runs commute with ring homomorphisms (`map_run`) and
  split at any stage (`run_add`).
* *Wedges of rows* (`W A J`, by recursion on the largest element: `W A J = A_{max J} ∧ W A (J ∖ max J)`): wedging a row
  `A_b` gives `0` if `b ∈ J` and `sg(b, J ∪ b)·W A (J ∪ b)` otherwise (`wedge_W_mem`, `wedge_W_notMem`); if
  `A·A' = s·1`, contracting `A'·η` is `s·Σ_{a ∈ J} sg(a, J)·η_a·W A (J ∖ a)` (`contr_W`), by the derivation rule
  `contr_wedge` and `⟨A'η, A_m⟩ = s·η_m`. `W 1 J = [J]` (`W_one`).
* *The action on states* (`Lam A S = Σ_J S(J)·W A J`): `Λ_A (y ∧ S) = (y·A) ∧ Λ_A S` (`Lam_wedge`) and
  `(A'·η) ⌟ Λ_A S = s·Λ_A (η ⌟ S)` (`Lam_contr`). So if the letter vectors of the wedge steps are transformed by `A`
  and those of the contraction steps by `A'`, and `Λ_A S0 = κ·S0`, then `κ·run z = s^{#con}·Λ_A (run y)`
  (`run_transform`).
* *Hodge duality* (`hodge_wedge`, `hodge_contr`): `y ∧ ⋆K = ⋆(y ⌟ K)` and `y ⌟ ⋆K = ⋆(y ∧ K)` with
  `⋆K(J) = σ(J)·K(Jᶜ)`, over any commutative ring (the `ℤ`-polynomial versions are `PathSpan.wedge_hodge`,
  `PathSpan.contr_hodge`).
* *Weights* (`WtIn`, `run_isWH`, `comp_runFrom`): a run whose wedge letters have weight `ε·e_a` and contraction letters
  `−ε·e_a` has the coordinate `J` of weight `ε·[J] + δ` when `S0` does; letters of weight `0` preserve the weights
  present and commute with taking weighted components.
-/

namespace CapStates

open MvPolynomial Finset TwistedDegree

noncomputable section

/-! ## Runs -/

section Run

variable {Λ : Type*} [CommRing Λ] {n : ℕ}

/-- **The run** of the steps `st` with the letter vectors `y` from the state `S0`: the state after `t` letters. -/
def run (y : ℕ → Fin n → Λ) (st : ℕ → Step) (S0 : Finset (Fin n) → Λ) : ℕ → Finset (Fin n) → Λ
  | 0 => S0
  | t + 1 => (st t).app (y t) (run y st S0 t)

/-- **One more letter.** -/
theorem run_succ (y : ℕ → Fin n → Λ) (st : ℕ → Step) (S0 : Finset (Fin n) → Λ) (t : ℕ) :
    run y st S0 (t + 1) = (st t).app (y t) (run y st S0 t) := rfl

/-- **The column states with unit exponents are runs from `[∅]`.** -/
theorem colSt_one_eq_run (y : ℕ → Fin n → Λ) (st : ℕ → Step) (t : ℕ) :
    colSt y st (fun _ => 1) t = run y st st0 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext J
    rw [colSt_succ, ih, run_succ]
    simp [pw]

/-- **Runs commute with ring homomorphisms.** -/
theorem map_run {Λ' : Type*} [CommRing Λ'] (f : Λ →+* Λ') (y : ℕ → Fin n → Λ) (st : ℕ → Step)
    (S0 : Finset (Fin n) → Λ) (t : ℕ) (J : Finset (Fin n)) :
    f (run y st S0 t J) = run (fun t a => f (y t a)) st (fun J => f (S0 J)) t J := by
  induction t generalizing J with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, run_succ, map_app]
    exact congrArg (fun S => (st t).app _ S J) (funext ih)

/-- **The run from a stage**: the state after `k` more letters `i, i + 1, …` from `S`. -/
def runFrom (y : ℕ → Fin n → Λ) (st : ℕ → Step) (i : ℕ) (S : Finset (Fin n) → Λ) : ℕ → Finset (Fin n) → Λ
  | 0 => S
  | k + 1 => (st (i + k)).app (y (i + k)) (runFrom y st i S k)

/-- **A run splits at any stage.** -/
theorem run_add (y : ℕ → Fin n → Λ) (st : ℕ → Step) (S0 : Finset (Fin n) → Λ) (i k : ℕ) :
    run y st S0 (i + k) = runFrom y st i (run y st S0 i) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← add_assoc, run_succ, ih]; rfl

/-- **A run from a stage only sees the later letters.** -/
theorem runFrom_congr {y y' : ℕ → Fin n → Λ} (st : ℕ → Step) (i : ℕ) (S : Finset (Fin n) → Λ) (k : ℕ)
    (h : ∀ u, i ≤ u → y u = y' u) : runFrom y st i S k = runFrom y' st i S k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [runFrom, runFrom, ih, h _ (Nat.le_add_right i k)]

/-- **Wedging is linear in the state.** -/
theorem wedge_sum_st {ι : Type*} (s : Finset ι) (y : Fin n → Λ) (f : ι → Finset (Fin n) → Λ) (J : Finset (Fin n)) :
    wedge y (fun K => ∑ j ∈ s, f j K) J = ∑ j ∈ s, wedge y (f j) J := by
  simp only [wedge, Finset.mul_sum]
  exact Finset.sum_comm

/-- **Contracting is linear in the state.** -/
theorem contr_sum_st {ι : Type*} (s : Finset ι) (y : Fin n → Λ) (f : ι → Finset (Fin n) → Λ) (J : Finset (Fin n)) :
    contr y (fun K => ∑ j ∈ s, f j K) J = ∑ j ∈ s, contr y (f j) J := by
  simp only [contr, Finset.mul_sum]
  exact Finset.sum_comm

/-- **A step commutes with scalars.** -/
theorem app_smul (st : Step) (y : Fin n → Λ) (p : Λ) (S : Finset (Fin n) → Λ) (J : Finset (Fin n)) :
    st.app y (fun K => p * S K) J = p * st.app y S J := by
  cases st
  · rfl
  · simp only [Step.app, wedge, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  · simp only [Step.app, contr, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring

/-- **A step is additive in the state.** -/
theorem app_sum (st : Step) {ι : Type*} (s : Finset ι) (y : Fin n → Λ) (f : ι → Finset (Fin n) → Λ)
    (J : Finset (Fin n)) : st.app y (fun K => ∑ j ∈ s, f j K) J = ∑ j ∈ s, st.app y (f j) J := by
  cases st
  · rfl
  · exact wedge_sum_st s y f J
  · exact contr_sum_st s y f J

/-- **A run from a stage commutes with scalars.** -/
theorem runFrom_smul (y : ℕ → Fin n → Λ) (st : ℕ → Step) (i : ℕ) (p : Λ) (S : Finset (Fin n) → Λ) (k : ℕ)
    (J : Finset (Fin n)) : runFrom y st i (fun K => p * S K) k J = p * runFrom y st i S k J := by
  induction k generalizing J with
  | zero => rfl
  | succ k ih =>
    rw [runFrom, runFrom]
    rw [show runFrom y st i (fun K => p * S K) k = fun K => p * runFrom y st i S k K from funext ih, app_smul]

/-- **Wedging commutes with scalars.** -/
theorem wedge_smul (y : Fin n → Λ) (p : Λ) (S : Finset (Fin n) → Λ) (J : Finset (Fin n)) :
    wedge y (fun K => p * S K) J = p * wedge y S J :=
  app_smul Step.wed y p S J

/-- **Contracting commutes with scalars.** -/
theorem contr_smul (y : Fin n → Λ) (p : Λ) (S : Finset (Fin n) → Λ) (J : Finset (Fin n)) :
    contr y (fun K => p * S K) J = p * contr y S J :=
  app_smul Step.con y p S J

/-- **Wedging with a combination of rows.** -/
theorem wedge_comb (y : Fin n → Λ) (A : Matrix (Fin n) (Fin n) Λ) (S : Finset (Fin n) → Λ) (J : Finset (Fin n)) :
    wedge (fun d => ∑ b, y b * A b d) S J = ∑ b, y b * wedge (A b) S J := by
  simp only [wedge, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Run

/-! ## Wedges of rows -/

section Rows

variable {Λ : Type*} [CommRing Λ] {n : ℕ}

/-- **The wedge of the rows of `A` indexed by `J`**, the largest outermost: `W A J = A_{max J} ∧ W A (J ∖ max J)`,
`W A ∅ = [∅]`. -/
def W (A : Matrix (Fin n) (Fin n) Λ) (J : Finset (Fin n)) : Finset (Fin n) → Λ :=
  if h : J.Nonempty then wedge (A (J.max' h)) (W A (J.erase (J.max' h))) else st0
termination_by J.card
decreasing_by exact Finset.card_erase_lt_of_mem (Finset.max'_mem J h)

/-- **`W A ∅ = [∅]`.** -/
theorem W_empty (A : Matrix (Fin n) (Fin n) Λ) : W A ∅ = st0 := by
  rw [W, dite_eq_right_of_eq_false (eq_false Finset.not_nonempty_empty)]

/-- **Unfolding `W` at the largest element.** -/
theorem W_max (A : Matrix (Fin n) (Fin n) Λ) {J : Finset (Fin n)} {m : Fin n} (hm : m ∈ J) (hle : ∀ j ∈ J, j ≤ m) :
    W A J = wedge (A m) (W A (J.erase m)) := by
  rw [W, dite_eq_left_of_eq_true (eq_true ⟨m, hm⟩)]
  have e : J.max' ⟨m, hm⟩ = m := le_antisymm (Finset.max'_le _ _ _ hle) (Finset.le_max' _ _ hm)
  rw [e]

/-- **Wedging a row already present gives `0`.** -/
theorem wedge_W_mem (A : Matrix (Fin n) (Fin n) Λ) : ∀ (J : Finset (Fin n)) {b : Fin n}, b ∈ J →
    wedge (A b) (W A J) = 0 := by
  intro J
  induction J using Finset.strongInduction with
  | H J ih =>
    intro b hb
    have hne : J.Nonempty := ⟨b, hb⟩
    set m := J.max' hne
    have hm : m ∈ J := Finset.max'_mem J hne
    rw [W_max A hm fun j hj => Finset.le_max' J j hj]
    funext K
    by_cases hbm : b = m
    · rw [hbm, wedge_wedge_self]; rfl
    · rw [wedge_anti, ih (J.erase m) (Finset.erase_ssubset hm) (Finset.mem_erase.2 ⟨hbm, hb⟩)]
      simp [wedge]

/-- **Wedging a new row**: `A_b ∧ W A J = sg(b, J ∪ b)·W A (J ∪ b)`. -/
theorem wedge_W_notMem (A : Matrix (Fin n) (Fin n) Λ) : ∀ (J : Finset (Fin n)) {b : Fin n}, b ∉ J →
    ∀ K, wedge (A b) (W A J) K = sg b (insert b J) * W A (insert b J) K := by
  intro J
  induction J using Finset.strongInduction with
  | H J ih =>
    intro b hb K
    by_cases hbig : ∀ j ∈ J, j < b
    · have hs : sg b (insert b J) = (1 : Λ) := by
        rw [sg, Finset.filter_eq_empty_iff.2 fun j hj => ?_, Finset.card_empty, pow_zero]
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact lt_irrefl _
        · exact not_lt.2 (hbig j hj).le
      rw [hs, one_mul, W_max A (Finset.mem_insert_self b J) fun j hj => ?_, Finset.erase_insert hb]
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact le_rfl
      · exact (hbig j hj).le
    · obtain ⟨j0, hj0, hbj0⟩ : ∃ j ∈ J, b ≤ j := by simpa using hbig
      have hne : J.Nonempty := ⟨j0, hj0⟩
      set m := J.max' hne
      have hm : m ∈ J := Finset.max'_mem J hne
      have hbm : b < m := lt_of_le_of_ne (hbj0.trans (Finset.le_max' J j0 hj0)) fun h => hb (h ▸ hm)
      have hmax : ∀ j ∈ insert b J, j ≤ m := fun j hj => by
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact hbm.le
        · exact Finset.le_max' J j hj
      rw [W_max A hm fun j hj => Finset.le_max' J j hj, W_max A (Finset.mem_insert_of_mem hm) hmax,
        Finset.erase_insert_of_ne (ne_of_lt hbm), wedge_anti]
      have hb' : b ∉ J.erase m := fun h => hb (Finset.mem_of_mem_erase h)
      rw [show wedge (A b) (W A (J.erase m)) = fun K => sg b (insert b (J.erase m)) * W A (insert b (J.erase m)) K
        from funext (ih (J.erase m) (Finset.erase_ssubset hm) hb')]
      have hm' : m ∉ insert b (J.erase m) := by simp [ne_of_gt hbm]
      have hs : (sg b (insert b J) : Λ) = -sg b (insert b (J.erase m)) := by
        have e : insert b J = insert m (insert b (J.erase m)) := by
          rw [Finset.insert_comm, Finset.insert_erase hm]
        rw [e, sg_insert hm', ite_eq_left_iff.2 fun h => absurd hbm h]
        ring
      rw [hs]
      simp only [wedge, Finset.mul_sum]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring

/-- **Wedging the largest row last**: if `m` exceeds every element of `J`, `A_m ∧ W A J = W A (J ∪ m)`. -/
theorem wedge_W_top (A : Matrix (Fin n) (Fin n) Λ) {J : Finset (Fin n)} {m : Fin n} (hm : ∀ j ∈ J, j < m) :
    wedge (A m) (W A J) = W A (insert m J) := by
  have hmJ : m ∉ J := fun h => lt_irrefl _ (hm m h)
  rw [W_max A (Finset.mem_insert_self m J) fun j hj => ?_, Finset.erase_insert hmJ]
  rcases Finset.mem_insert.1 hj with rfl | hj
  · exact le_rfl
  · exact (hm j hj).le

/-- **Contracting `A'·η` into a wedge of rows**, when `A·A' = s·1`: `s·Σ_{a ∈ J} sg(a, J)·η_a·W A (J ∖ a)`. -/
theorem contr_W {A A' : Matrix (Fin n) (Fin n) Λ} {s : Λ} (hAA : A * A' = s • 1) (η : Fin n → Λ) :
    ∀ (J : Finset (Fin n)) (K : Finset (Fin n)), contr (fun d => ∑ e, A' d e * η e) (W A J) K =
      s * ∑ a ∈ J, sg a J * η a * W A (J.erase a) K := by
  intro J
  induction J using Finset.strongInduction with
  | H J ih =>
    intro K
    by_cases hne : J.Nonempty
    · set m := J.max' hne
      have hm : m ∈ J := Finset.max'_mem J hne
      have hle : ∀ j ∈ J, j ≤ m := fun j hj => Finset.le_max' J j hj
      have hpair : ∑ d, (∑ e, A' d e * η e) * A m d = s * η m := by
        have h1 : ∀ e, ∑ d, A m d * A' d e = if m = e then s else 0 := fun e => by
          rw [← Matrix.mul_apply, hAA, Matrix.smul_apply, Matrix.one_apply]
          split_ifs <;> simp
        calc ∑ d, (∑ e, A' d e * η e) * A m d = ∑ e, η e * ∑ d, A m d * A' d e := by
              simp only [Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          _ = s * η m := by
              simp only [h1, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
              ring
      have hcw := contr_wedge (fun d => ∑ e, A' d e * η e) (A m) (W A (J.erase m)) K
      rw [hpair] at hcw
      rw [W_max A hm hle]
      have hih : contr (fun d => ∑ e, A' d e * η e) (W A (J.erase m)) = fun K' =>
          s * ∑ a ∈ J.erase m, sg a (J.erase m) * η a * W A ((J.erase m).erase a) K' :=
        funext (ih (J.erase m) (Finset.erase_ssubset hm))
      rw [hih] at hcw
      have hw : wedge (A m) (fun K' => s * ∑ a ∈ J.erase m, sg a (J.erase m) * η a * W A ((J.erase m).erase a) K')
          K = s * ∑ a ∈ J.erase m, sg a (J.erase m) * η a * W A (J.erase a) K := by
        rw [wedge_smul, wedge_sum_st]
        congr 1
        refine Finset.sum_congr rfl fun a ha => ?_
        have ham : a ≠ m := Finset.ne_of_mem_erase ha
        have hlt : ∀ j ∈ (J.erase m).erase a, j < m := fun j hj =>
          lt_of_le_of_ne (hle j (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj)))
            (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj))
        rw [wedge_smul, wedge_W_top A hlt, Finset.erase_right_comm, Finset.insert_erase
          (Finset.mem_erase.2 ⟨fun h => ham h.symm, hm⟩)]
      rw [hw] at hcw
      rw [← Finset.add_sum_erase J _ hm]
      have hsm : (sg m J : Λ) = 1 := by
        rw [sg, Finset.filter_eq_empty_iff.2 fun j hj => not_lt.2 (hle j hj), Finset.card_empty, pow_zero]
      have hsa : ∀ a ∈ J.erase m, (sg a J : Λ) = -sg a (J.erase m) := fun a ha => by
        have hlt : a < m := lt_of_le_of_ne (hle a (Finset.mem_of_mem_erase ha)) (Finset.ne_of_mem_erase ha)
        rw [sg_erase hm, ite_eq_left_iff.2 fun h => absurd hlt h]
        rw [neg_one_mul, neg_neg]
      rw [hsm, Finset.sum_congr rfl fun a ha => by rw [hsa a ha]]
      simp only [neg_mul, Finset.sum_neg_distrib]
      linear_combination hcw
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      rw [W_empty, Finset.sum_empty, mul_zero]
      refine Finset.sum_eq_zero fun a _ => ?_
      simp [st0]

/-- **The wedge of rows has degree `|J|`.** -/
theorem W_isDeg (A : Matrix (Fin n) (Fin n) Λ) : ∀ J : Finset (Fin n), PathSpan.IsDeg (W A J) J.card := by
  intro J
  induction J using Finset.strongInduction with
  | H J ih =>
    by_cases hne : J.Nonempty
    · have hm : J.max' hne ∈ J := Finset.max'_mem J hne
      rw [W_max A hm fun j hj => Finset.le_max' J j hj]
      have h := (ih (J.erase _) (Finset.erase_ssubset hm)).wedge (A (J.max' hne))
      rwa [Finset.card_erase_of_mem hm, Nat.sub_add_cancel (Finset.card_pos.2 hne)] at h
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      intro K hK
      rw [W_empty, st0, ite_eq_right_iff.2 fun h => absurd (congrArg Finset.card h) hK]

/-- **The wedges of the rows of the identity** are the coordinate states. -/
theorem W_one : ∀ (J K : Finset (Fin n)), W (1 : Matrix (Fin n) (Fin n) Λ) J K = if K = J then 1 else 0 := by
  intro J
  induction J using Finset.strongInduction with
  | H J ih =>
    intro K
    by_cases hne : J.Nonempty
    · set m := J.max' hne
      have hm : m ∈ J := Finset.max'_mem J hne
      have hle : ∀ j ∈ J, j ≤ m := fun j hj => Finset.le_max' J j hj
      rw [W_max _ hm hle, wedge]
      simp only [ih (J.erase m) (Finset.erase_ssubset hm), Matrix.one_apply]
      by_cases hmK : m ∈ K
      · rw [Finset.sum_eq_single m (fun b _ hb => by simp [Ne.symm hb]) (fun h => absurd hmK h)]
        simp only [ite_true, mul_one]
        by_cases hKJ : K = J
        · rw [hKJ, sg, Finset.filter_eq_empty_iff.2 fun j hj => not_lt.2 (hle j hj)]
          simp
        · have : K.erase m ≠ J.erase m := fun h => hKJ (by
            rw [← Finset.insert_erase hmK, h, Finset.insert_erase hm])
          simp [hKJ, this]
      · rw [Finset.sum_eq_zero fun b hb => by simp [show m ≠ b from fun h => hmK (h ▸ hb)]]
        simp [show K ≠ J from fun h => hmK (h ▸ hm)]
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      rw [W_empty, st0]

/-- **Wedges of rows commute with ring homomorphisms.** -/
theorem map_W {Λ' : Type*} [CommRing Λ'] (f : Λ →+* Λ') (A : Matrix (Fin n) (Fin n) Λ) :
    ∀ (J K : Finset (Fin n)), f (W A J K) = W (A.map f) J K := by
  intro J
  induction J using Finset.strongInduction with
  | H J ih =>
    intro K
    by_cases hne : J.Nonempty
    · have hm : J.max' hne ∈ J := Finset.max'_mem J hne
      rw [W_max A hm fun j hj => Finset.le_max' J j hj, W_max (A.map f) hm fun j hj => Finset.le_max' J j hj]
      have := map_app f Step.wed (A (J.max' hne)) (W A (J.erase (J.max' hne))) K
      simp only [Step.app] at this
      rw [this]
      exact congrArg (fun S => wedge _ S K) (funext (ih _ (Finset.erase_ssubset hm)))
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      rw [W_empty, W_empty, st0, st0]
      split_ifs <;> simp

/-- **Reindexing pairs** `b ∈ J'` as pairs `b ∉ J` through `J' = J ∪ b`. -/
theorem sum_mem_eq_sum_insert {M : Type*} [AddCommMonoid M] (f : Finset (Fin n) → Fin n → M) :
    ∑ J, ∑ b ∈ J, f J b = ∑ J, ∑ b ∈ Jᶜ, f (insert b J) b := by
  rw [Finset.sum_comm' (t' := univ) (s' := fun b : Fin n => univ.filter fun J : Finset (Fin n) => b ∈ J)
      (fun J b => by simp),
    Finset.sum_comm' (t' := univ) (s' := fun b : Fin n => univ.filter fun J : Finset (Fin n) => b ∉ J)
      (fun J b => by simp)]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_nbij' (fun J => J.erase b) (fun J => insert b J) ?_ ?_ ?_ ?_ ?_
  · intro J _; simp
  · intro J _; simp
  · intro J hJ; simp at hJ; exact Finset.insert_erase hJ
  · intro J hJ; simp at hJ; exact Finset.erase_insert hJ
  · intro J hJ; simp at hJ; rw [Finset.insert_erase hJ]

/-- **The action of a matrix on states**: `Λ_A S = Σ_J S(J)·W A J`. -/
def Lam (A : Matrix (Fin n) (Fin n) Λ) (S : Finset (Fin n) → Λ) : Finset (Fin n) → Λ :=
  fun K => ∑ J, S J * W A J K

/-- **Unfolding `Λ_A`.** -/
theorem Lam_def (A : Matrix (Fin n) (Fin n) Λ) (S : Finset (Fin n) → Λ) :
    Lam A S = fun K => ∑ J, S J * W A J K := rfl

/-- **`Λ_A (y ∧ S) = (y·A) ∧ Λ_A S`.** -/
theorem Lam_wedge (A : Matrix (Fin n) (Fin n) Λ) (y : Fin n → Λ) (S : Finset (Fin n) → Λ) (K : Finset (Fin n)) :
    Lam A (wedge y S) K = wedge (fun d => ∑ b, y b * A b d) (Lam A S) K := by
  rw [wedge_comb]
  have hR : ∀ b, wedge (A b) (Lam A S) K = ∑ J, S J * wedge (A b) (W A J) K := fun b => by
    rw [Lam_def, wedge_sum_st]
    exact Finset.sum_congr rfl fun J _ => wedge_smul _ _ _ _
  simp only [hR, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hL : Lam A (wedge y S) K = ∑ J, ∑ b ∈ J, sg b J * y b * S (J.erase b) * W A J K := by
    simp only [Lam_def, wedge, Finset.sum_mul]
  rw [hL, sum_mem_eq_sum_insert]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [← Finset.sum_subset (Finset.subset_univ Jᶜ) fun b _ hb => by
    rw [wedge_W_mem A J (by simpa using hb)]; simp]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [wedge_W_notMem A J (Finset.mem_compl.1 hb), Finset.erase_insert (Finset.mem_compl.1 hb)]
  ring

/-- **`(A'·η) ⌟ Λ_A S = s·Λ_A (η ⌟ S)`** when `A·A' = s·1`. -/
theorem Lam_contr {A A' : Matrix (Fin n) (Fin n) Λ} {s : Λ} (hAA : A * A' = s • 1) (η : Fin n → Λ)
    (S : Finset (Fin n) → Λ) (K : Finset (Fin n)) :
    contr (fun d => ∑ e, A' d e * η e) (Lam A S) K = s * Lam A (contr η S) K := by
  rw [Lam_def, contr_sum_st]
  simp only [contr_smul, contr_W hAA]
  have hR : Lam A (contr η S) K = ∑ J, ∑ a ∈ Jᶜ, sg a J * η a * S (insert a J) * W A J K := by
    simp only [Lam_def, contr, Finset.sum_mul]
  rw [hR]
  have e : ∑ J, S J * (s * ∑ a ∈ J, sg a J * η a * W A (J.erase a) K) =
      s * ∑ J, ∑ a ∈ J, S J * sg a J * η a * W A (J.erase a) K := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e, sum_mem_eq_sum_insert]
  congr 1
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.erase_insert (Finset.mem_compl.1 ha), sg_insert_self]
  ring

/-- **The number of contraction steps** before the letter `t`. -/
def ncon (st : ℕ → Step) : ℕ → ℕ
  | 0 => 0
  | t + 1 => ncon st t + (match st t with | .con => 1 | _ => 0)

/-- **(CE) The transformation rule of a run**: if the letter vectors of the wedge steps are transformed by `A`, those
of the contraction steps by `A'`, `A·A' = s·1` and `Λ_A S0 = κ·S0`, then `κ·run z = s^{#con}·Λ_A (run y)`. -/
theorem run_transform {y z : ℕ → Fin n → Λ} {st : ℕ → Step} {S0 : Finset (Fin n) → Λ}
    {A A' : Matrix (Fin n) (Fin n) Λ} {s κ : Λ} (hAA : A * A' = s • 1) (hS0 : ∀ K, Lam A S0 K = κ * S0 K) :
    ∀ {t : ℕ}, (∀ u < t, (st u = .wed → z u = fun d => ∑ b, y u b * A b d) ∧
      (st u = .con → z u = fun d => ∑ e, A' d e * y u e)) →
    ∀ K, κ * run z st S0 t K = s ^ ncon st t * Lam A (run y st S0 t) K := by
  intro t
  induction t with
  | zero => intro _ K; rw [run, run, ncon, pow_zero, one_mul, hS0]
  | succ t ih =>
    intro hz K
    have ih' := ih fun u hu => hz u (by omega)
    have hzt := hz t (by omega)
    rw [run_succ, run_succ, ncon]
    cases h : st t
    · simp only [Step.app, add_zero]
      exact ih' K
    · simp only [Step.app, add_zero]
      rw [← wedge_smul, show (fun K => κ * run z st S0 t K) = fun K => s ^ ncon st t * Lam A (run y st S0 t) K
        from funext ih', wedge_smul, hzt.1 h, Lam_wedge]
    · simp only [Step.app]
      rw [← contr_smul, show (fun K => κ * run z st S0 t K) = fun K => s ^ ncon st t * Lam A (run y st S0 t) K
        from funext ih', contr_smul, hzt.2 h, Lam_contr hAA, pow_succ]
      ring

end Rows

/-! ## Hodge duality over any ring -/

section Hodge

variable {Λ : Type*} [CommRing Λ] {n : ℕ}

/-- **The Hodge sign** `σ(J) = (−1)^{Σ_{x ∈ J} (n − 1 − x)}` in any ring. -/
def hsg (J : Finset (Fin n)) : Λ := (-1) ^ PathSpan.hexp J

/-- **The Hodge sign squares to one.** -/
theorem hsg_mul_self (J : Finset (Fin n)) : (hsg J : Λ) * hsg J = 1 := by
  rw [hsg, ← pow_add, ← two_mul, pow_mul]; simp

/-- **The Hodge sign with one more element.** -/
theorem hsg_insert {a : Fin n} {J : Finset (Fin n)} (ha : a ∉ J) :
    (hsg (insert a J) : Λ) = hsg J * (-1) ^ (n - 1 - a.val) := by
  rw [hsg, hsg, PathSpan.hexp, PathSpan.hexp, sum_insert ha, ← pow_add, add_comm]

/-- **The sign of `a` in `J` and in `Jᶜ`** differ by `(−1)^{n − 1 − a}`. -/
theorem sg_mul_pow (J : Finset (Fin n)) (a : Fin n) : (sg a J : Λ) * (-1) ^ (n - 1 - a.val) = sg a Jᶜ := by
  rw [sg, sg, ← pow_add]
  have := PathSpan.card_gt_add_card_gt_compl J a
  exact PathSpan.neg_one_pow_congr (by omega)

/-- **Contracting the Hodge dual is the dual of wedging**: `y ⌟ ⋆K = ⋆(y ∧ K)`. -/
theorem hodge_contr (y : Fin n → Λ) (K : Finset (Fin n) → Λ) (J : Finset (Fin n)) :
    contr y (fun J => hsg J * K Jᶜ) J = hsg J * wedge y K Jᶜ := by
  rw [contr, wedge, mul_sum]
  refine sum_congr rfl fun a ha => ?_
  have ha' : a ∉ J := mem_compl.1 ha
  rw [hsg_insert ha', compl_insert, ← sg_mul_pow J a]
  ring

/-- **Wedging the Hodge dual is the dual of contracting**: `y ∧ ⋆K = ⋆(y ⌟ K)`. -/
theorem hodge_wedge (y : Fin n → Λ) (K : Finset (Fin n) → Λ) (J : Finset (Fin n)) :
    wedge y (fun J => hsg J * K Jᶜ) J = hsg J * contr y K Jᶜ := by
  rw [contr, wedge, mul_sum, compl_compl]
  refine sum_congr rfl fun a ha => ?_
  have h1 : (hsg J : Λ) = hsg (J.erase a) * (-1) ^ (n - 1 - a.val) := by
    rw [← hsg_insert (notMem_erase a J), insert_erase ha]
  have h2 : (sg a J : Λ) = sg a (J.erase a) := (sg_erase_self a J).symm
  have h4 : (sg a Jᶜ : Λ) = sg a (J.erase a) * (-1) ^ (n - 1 - a.val) := by
    rw [sg_mul_pow, compl_erase, sg_insert_self]
  rw [compl_erase, h1, h2, h4]
  have h3 : ((-1 : Λ) ^ (n - 1 - a.val)) * (-1) ^ (n - 1 - a.val) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination (-(sg a (J.erase a) * y a * hsg (J.erase a) * K (insert a Jᶜ))) * h3

/-- **The swapped step**: wedge and contraction exchanged. -/
def stepSwap : Step → Step
  | .keep => .keep
  | .wed => .con
  | .con => .wed

/-- **The Hodge dual of a run** is the run of the swapped steps from the dual initial state. -/
theorem run_hodge (y : ℕ → Fin n → Λ) (st : ℕ → Step) (S0 : Finset (Fin n) → Λ) :
    ∀ (t : ℕ) (J : Finset (Fin n)), run y (fun u => stepSwap (st u)) (fun J => hsg J * S0 Jᶜ) t J =
      hsg J * run y st S0 t Jᶜ := by
  intro t
  induction t with
  | zero => intro J; rfl
  | succ t ih =>
    intro J
    rw [run_succ, run_succ, show run y (fun u => stepSwap (st u)) (fun J => hsg J * S0 Jᶜ) t =
      fun J => hsg J * run y st S0 t Jᶜ from funext (ih)]
    cases st t
    · rfl
    · exact hodge_contr _ _ _
    · exact hodge_wedge _ _ _

end Hodge

/-! ## Weights -/

section Weights

variable {σ B : Type*} [CommRing B] {n : ℕ}

/-- **The indicator weight** `[J] = Σ_{a ∈ J} e_a`. -/
def ind (J : Finset (Fin n)) : Fin n → ℤ := fun b => if b ∈ J then 1 else 0

/-- **The indicator with one element removed.** -/
theorem ind_erase {J : Finset (Fin n)} {a : Fin n} (ha : a ∈ J) : ind J = ind (J.erase a) + Pi.single a 1 := by
  funext b
  simp only [ind, Pi.add_apply, Pi.single_apply, Finset.mem_erase]
  by_cases h : b = a
  · subst h; simp [ha]
  · simp [h]

/-- **The indicator with one element added.** -/
theorem ind_insert {J : Finset (Fin n)} {a : Fin n} (ha : a ∉ J) : ind (insert a J) = ind J + Pi.single a 1 := by
  rw [ind_erase (Finset.mem_insert_self a J), Finset.erase_insert ha]

/-- **The indicator determines the set.** -/
theorem ind_injective : Function.Injective (ind : Finset (Fin n) → Fin n → ℤ) := by
  intro J J' h
  ext b
  have := congrFun h b
  simp only [ind] at this
  split_ifs at this <;> simp_all

/-- **Signs have weight `0`.** -/
theorem isWH_sg (w : σ → Fin n → ℤ) (a : Fin n) (J : Finset (Fin n)) :
    IsWeightedHomogeneous w (sg a J : MvPolynomial σ B) 0 := by
  rw [sg, show ((-1 : MvPolynomial σ B)) = C (-1) from by simp, ← map_pow]
  exact isWeightedHomogeneous_C w _

/-- **The weights of a run**: if the wedge letters have weight `ε·e_a`, the contraction letters `−ε·e_a` and the
coordinate `J` of `S0` has weight `ε·[J] + δ`, then so does the coordinate `J` of the run. -/
theorem run_isWH (w : σ → Fin n → ℤ) {y : ℕ → Fin n → MvPolynomial σ B} {st : ℕ → Step}
    {S0 : Finset (Fin n) → MvPolynomial σ B} (ε : ℤ) (δ : Fin n → ℤ)
    (hS0 : ∀ J, IsWeightedHomogeneous w (S0 J) (ε • ind J + δ)) :
    ∀ {t : ℕ}, (∀ u < t, (st u = .wed → ∀ a, IsWeightedHomogeneous w (y u a) (ε • Pi.single a 1)) ∧
      (st u = .con → ∀ a, IsWeightedHomogeneous w (y u a) (-(ε • Pi.single a 1)))) →
    ∀ J, IsWeightedHomogeneous w (run y st S0 t J) (ε • ind J + δ) := by
  intro t
  induction t with
  | zero => intro _ J; exact hS0 J
  | succ t ih =>
    intro hy J
    have ih' := ih fun u hu => hy u (by omega)
    have hyt := hy t (by omega)
    rw [run_succ]
    cases h : st t
    · exact ih' J
    · refine IsWeightedHomogeneous.sum _ _ _ fun a ha => ?_
      have e : ε • ind J + δ = 0 + ε • Pi.single a 1 + (ε • ind (J.erase a) + δ) := by
        rw [ind_erase ha, smul_add]; abel
      rw [e]
      exact ((isWH_sg w a J).mul (hyt.1 h a)).mul (ih' _)
    · refine IsWeightedHomogeneous.sum _ _ _ fun a ha => ?_
      have e : ε • ind J + δ = 0 + -(ε • Pi.single a 1) + (ε • ind (insert a J) + δ) := by
        rw [ind_insert (Finset.mem_compl.1 ha), smul_add]; abel
      rw [e]
      exact ((isWH_sg w a J).mul (hyt.2 h a)).mul (ih' _)

/-- **The weights present in a polynomial lie in `P`.** -/
def WtIn (w : σ → Fin n → ℤ) (p : MvPolynomial σ B) (P : Set (Fin n → ℤ)) : Prop :=
  ∀ u ∈ p.support, Finsupp.weight w u ∈ P

/-- **A homogeneous polynomial has its weight.** -/
theorem WtIn.of_isWH {w : σ → Fin n → ℤ} {p : MvPolynomial σ B} {m : Fin n → ℤ} {P : Set (Fin n → ℤ)}
    (hp : IsWeightedHomogeneous w p m) (hm : p ≠ 0 → m ∈ P) : WtIn w p P := fun u hu => by
  rw [hp (mem_support_iff.1 hu)]
  exact hm (ne_zero_iff.2 ⟨u, mem_support_iff.1 hu⟩)

/-- **Weights of a sum.** -/
theorem WtIn.sum {w : σ → Fin n → ℤ} {ι : Type*} (s : Finset ι) {f : ι → MvPolynomial σ B} {P : Set (Fin n → ℤ)}
    (h : ∀ i ∈ s, WtIn w (f i) P) : WtIn w (∑ i ∈ s, f i) P := by
  classical
  intro u hu
  obtain ⟨i, hi, hu'⟩ := Finset.mem_biUnion.1 (support_sum hu)
  exact h i hi u hu'

/-- **Weights of a product.** -/
theorem WtIn.mul {w : σ → Fin n → ℤ} {p q : MvPolynomial σ B} {P Q : Set (Fin n → ℤ)} (hp : WtIn w p P)
    (hq : WtIn w q Q) : WtIn w (p * q) {x | ∃ a ∈ P, ∃ b ∈ Q, a + b = x} := by
  classical
  intro u hu
  obtain ⟨u1, hu1, u2, hu2, rfl⟩ := Finset.mem_add.1 (support_mul p q hu)
  exact ⟨_, hp u1 hu1, _, hq u2 hu2, (map_add _ _ _).symm⟩

/-- **A factor of weight `0` keeps the weights.** -/
theorem WtIn.mul_left0 {w : σ → Fin n → ℤ} {p q : MvPolynomial σ B} {P : Set (Fin n → ℤ)}
    (hq : IsWeightedHomogeneous w q 0) (hp : WtIn w p P) : WtIn w (q * p) P := by
  intro u hu
  obtain ⟨a, ha, b, hb, hab⟩ := WtIn.mul (P := {0}) (fun u hu => hq (mem_support_iff.1 hu)) hp u hu
  rw [← hab, Set.mem_singleton_iff.1 ha, zero_add]
  exact hb

/-- **Letters of weight `0` keep the weights of a state.** -/
theorem runFrom_wtIn {w : σ → Fin n → ℤ} {y : ℕ → Fin n → MvPolynomial σ B} (st : ℕ → Step) {i : ℕ}
    (hy : ∀ u, i ≤ u → ∀ a, IsWeightedHomogeneous w (y u a) 0) {S : Finset (Fin n) → MvPolynomial σ B}
    {P : Set (Fin n → ℤ)} (hS : ∀ J, WtIn w (S J) P) : ∀ k J, WtIn w (runFrom y st i S k J) P := by
  intro k
  induction k with
  | zero => exact hS
  | succ k ih =>
    intro J
    rw [runFrom]
    have hya := hy (i + k) (Nat.le_add_right i k)
    cases st (i + k)
    · exact ih J
    · refine WtIn.sum _ fun a _ => ?_
      rw [mul_assoc]
      exact WtIn.mul_left0 (isWH_sg w a J) (WtIn.mul_left0 (hya a) (ih _))
    · refine WtIn.sum _ fun a _ => ?_
      rw [mul_assoc]
      exact WtIn.mul_left0 (isWH_sg w a J) (WtIn.mul_left0 (hya a) (ih _))

/-- **A component of a product with a factor of weight `0`.** -/
theorem comp_mul_of_isWH0 (w : σ → Fin n → ℤ) {q : MvPolynomial σ B} (hq : IsWeightedHomogeneous w q 0)
    (m : Fin n → ℤ) (p : MvPolynomial σ B) :
    weightedHomogeneousComponent w m (q * p) = q * weightedHomogeneousComponent w m p := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  simp only [coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · refine Finset.sum_congr rfl fun x hx => ?_
    by_cases hq0 : q.coeff x.1 = 0
    · simp [hq0]
    · have h1 : Finsupp.weight w x.2 = m := by
        rw [← hd, ← Finset.HasAntidiagonal.mem_antidiagonal.1 hx, map_add, hq hq0, zero_add]
      rw [ite_eq_left_iff.2 fun h => absurd h1 h]
  · refine (Finset.sum_eq_zero fun x hx => ?_).symm
    by_cases hq0 : q.coeff x.1 = 0
    · simp [hq0]
    · have h1 : Finsupp.weight w x.2 ≠ m := by
        rw [← zero_add (Finsupp.weight w x.2), ← hq hq0, ← map_add, Finset.HasAntidiagonal.mem_antidiagonal.1 hx]
        exact hd
      rw [ite_eq_right_iff.2 fun h => absurd h h1, mul_zero]

/-- **Components pass through letters of weight `0`.** -/
theorem comp_runFrom (w : σ → Fin n → ℤ) {y : ℕ → Fin n → MvPolynomial σ B} (st : ℕ → Step) {i : ℕ}
    (hy : ∀ u, i ≤ u → ∀ a, IsWeightedHomogeneous w (y u a) 0) (m : Fin n → ℤ) (S : Finset (Fin n) → MvPolynomial σ B) :
    ∀ k J, weightedHomogeneousComponent w m (runFrom y st i S k J) =
      runFrom y st i (fun J => weightedHomogeneousComponent w m (S J)) k J := by
  intro k
  induction k with
  | zero => intro J; rfl
  | succ k ih =>
    intro J
    rw [runFrom, runFrom, ← funext ih]
    have hya := hy (i + k) (Nat.le_add_right i k)
    cases st (i + k)
    · rfl
    · simp only [Step.app, wedge, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have h0 := (isWH_sg w a J).mul (hya a)
      rw [zero_add] at h0
      rw [comp_mul_of_isWH0 w h0 m]
    · simp only [Step.app, contr, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have h0 := (isWH_sg w a J).mul (hya a)
      rw [zero_add] at h0
      rw [comp_mul_of_isWH0 w h0 m]

end Weights

end

end CapStates
