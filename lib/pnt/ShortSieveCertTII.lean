import ShortSieveCertSem
import ShortSieveWit

/-!
# The certificate's Type II test on a box

The certificate shows a box asymptotic by a partition of the node's items into groups and Harman's test with real
exponents: `Σ_g 1/δ_req(c/(a_g − κ)) > 1`, `a_g` the exponent of group `g`, `c = 1 − θ + κ`
(`ShortSieveNode.abs_count_sub_le_of_test`). The check is in integers, as the generator's linearised test: each
group's least exponent `lo_g` on the box (domain-aware), `⌊SCF/δ_req⌋` there (`fexact`), and on a ramp of `δ_req` the
tangent slope (`fslope`), whose linear terms keep the cancellations between groups.

* `LF.minD_le`: the deterministic domain-aware least value (the generator's multipliers, one pass of coordinate
  ascent over the active constraints) bounds a form at the points of the box where the active constraints hold.
* `fexact_le`, `fpiece_spec`, `fslope_le`: the integer values are below `SCF/δ_req` and the tangent slope on a ramp.
* `lt_sum_of_tiiCheck`: a passing check (`tiiCheck`) gives every group's exponent above `κ` and the test, at every
  point of the closed box where the active constraints hold.
-/

open Finset Real

namespace ShortSieveCert

open ShortSieveWit

/-! ### Sums and multiples of forms -/

/-- Adding coefficient lists, the shorter padded with zeros. -/
def addC : List ℤ → List ℤ → List ℤ
  | [], d => d
  | c, [] => c
  | a :: c, b :: d => (a + b) :: addC c d

/-- The sum of two forms. -/
def LF.add (L M : LF) : LF := ⟨L.c0 + M.c0, addC L.c M.c, L.ce + M.ce⟩

/-- A multiple of a form. -/
def LF.smul (μ : ℤ) (L : LF) : LF := ⟨μ * L.c0, L.c.map (μ * ·), μ * L.ce⟩

theorem dotR_addC : ∀ (c d : List ℤ) (X : ℕ → ℝ), dotR (addC c d) X = dotR c X + dotR d X
  | [], d, X => by simp [addC, dotR]
  | a :: c, [], X => by simp [addC, dotR]
  | a :: c, b :: d, X => by
    simp only [addC, dotR, dotR_addC c d]
    push_cast
    ring

theorem length_addC : ∀ c d : List ℤ, (addC c d).length = max c.length d.length
  | [], d => by simp [addC]
  | a :: c, [] => by simp [addC]
  | a :: c, b :: d => by simp [addC, length_addC c d, Nat.succ_max_succ]

theorem LF.val_add (L M : LF) (X : ℕ → ℝ) (H : ℝ) : (L.add M).val X H = L.val X H + M.val X H := by
  unfold LF.add LF.val
  rw [dotR_addC]
  push_cast
  ring

theorem LF.val_smul (μ : ℤ) (L : LF) (X : ℕ → ℝ) (H : ℝ) : (L.smul μ).val X H = μ * L.val X H := by
  unfold LF.smul LF.val
  rw [dotR_map_mul]
  push_cast
  ring

/-! ### Domain-aware least values, with the multipliers chosen deterministically -/

/-- The best multiple of the active constraint `g` to add to `M` (and the value reached), from the candidates
`q − 1, q, q + 1` with `q = −M_j/g_j` for each coordinate `j` with `g_j ≠ 0`; `0` when none improves on `best`. -/
def bestMu (B : Box) (E : ℤ) (M g : LF) (best : ℤ) : ℤ × ℤ :=
  ((List.range g.c.length).filter fun j => g.c.getD j 0 ≠ 0).foldl (fun acc j =>
    let q := -(M.c.getD j 0) / g.c.getD j 0
    [q - 1, q, q + 1].foldl (fun acc' μ =>
      if 0 < μ then
        let v := (M.add (g.smul μ)).min B E
        if acc'.2 < v then (μ, v) else acc'
      else acc') acc) (0, best)

/-- One pass over the active constraints: `M ↦ M + μ g` with the best multiple of each. -/
def passMu (B : Box) (E : ℤ) : LF × ℤ → List LF → LF × ℤ
  | s, [] => s
  | (M, best), g :: gs =>
    let r := bestMu B E M g best
    passMu B E (if r.1 = 0 then (M, best) else (M.add (g.smul r.1), r.2)) gs

/-- The domain-aware least value: `⌊min_B (6L + Σ μ_i g_i)/6⌋` with the deterministic multipliers. -/
def LF.minD (L : LF) (B : Box) (E : ℤ) (acts : List LF) : ℤ :=
  (passMu B E (L.smul 6, (L.smul 6).min B E) acts).2 / 6

/-- The multiple chosen by `bestMu` is nonnegative. -/
theorem bestMu_nonneg (B : Box) (E : ℤ) (M g : LF) (best : ℤ) : 0 ≤ (bestMu B E M g best).1 := by
  unfold bestMu
  suffices h : ∀ (l : List ℕ) (acc : ℤ × ℤ), 0 ≤ acc.1 → 0 ≤ (l.foldl (fun acc j =>
      let q := -(M.c.getD j 0) / g.c.getD j 0
      [q - 1, q, q + 1].foldl (fun acc' μ =>
        if 0 < μ then
          let v := (M.add (g.smul μ)).min B E
          if acc'.2 < v then (μ, v) else acc'
        else acc') acc) acc).1 from h _ _ le_rfl
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons j l ih =>
    intro acc hacc
    refine ih _ ?_
    simp only [List.foldl_cons, List.foldl_nil]
    split_ifs <;> first | assumption | (simp only; omega)

theorem bestMu_spec (B : Box) (E : ℤ) (M g : LF) (best : ℤ) :
    (bestMu B E M g best).1 = 0 ∧ (bestMu B E M g best).2 = best ∨
      (bestMu B E M g best).2 = (M.add (g.smul (bestMu B E M g best).1)).min B E := by
  unfold bestMu
  suffices h : ∀ (l : List ℕ) (acc : ℤ × ℤ), (acc.1 = 0 ∧ acc.2 = best ∨ acc.2 = (M.add (g.smul acc.1)).min B E) →
      let r := l.foldl (fun acc j =>
        let q := -(M.c.getD j 0) / g.c.getD j 0
        [q - 1, q, q + 1].foldl (fun acc' μ =>
          if 0 < μ then
            let v := (M.add (g.smul μ)).min B E
            if acc'.2 < v then (μ, v) else acc'
          else acc') acc) acc
      r.1 = 0 ∧ r.2 = best ∨ r.2 = (M.add (g.smul r.1)).min B E from h _ _ (Or.inl ⟨rfl, rfl⟩)
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons j l ih =>
    intro acc hacc
    refine ih _ ?_
    simp only [List.foldl_cons, List.foldl_nil]
    split_ifs <;> first | exact hacc | exact Or.inr rfl

/-- **The deterministic domain-aware least value bounds the form** at the points of the box where every active
constraint is `≤ 0`. -/
theorem LF.minD_le (L : LF) {B : Box} {E : ℤ} (acts : List LF) {X : ℕ → ℝ} (hX : InBoxC B X) {H : ℝ}
    (hH : |H| ≤ E) (hacts : ∀ g ∈ acts, g.val X H ≤ 0) (hfit : L.c.length ≤ B.length)
    (hfit' : ∀ g ∈ acts, g.c.length ≤ B.length) :
    (L.minD B E acts : ℝ) ≤ L.val X H := by
  -- the invariant: `best = min_B M` (or `best` is the initial value) and `M ≤ 6L` at the point
  have key : ∀ (gs : List LF) (M : LF) (best : ℤ), (∀ g ∈ gs, g.val X H ≤ 0 ∧ g.c.length ≤ B.length) →
      M.c.length ≤ B.length → (best : ℝ) ≤ M.val X H → M.val X H ≤ 6 * L.val X H →
      ((passMu B E (M, best) gs).2 : ℝ) ≤ 6 * L.val X H := by
    intro gs
    induction gs with
    | nil => intro M best _ _ h1 h2; simp only [passMu]; linarith
    | cons g gs ih =>
      intro M best hg hM h1 h2
      simp only [passMu]
      obtain ⟨hg0, hgl⟩ := hg g List.mem_cons_self
      have hg' : ∀ g' ∈ gs, g'.val X H ≤ 0 ∧ g'.c.length ≤ B.length := fun g' h => hg g' (List.mem_cons_of_mem _ h)
      have hμ := bestMu_nonneg B E M g best
      split_ifs with h0
      · exact ih M best hg' hM h1 h2
      · set μ := (bestMu B E M g best).1
        have hlenN : (M.add (g.smul μ)).c.length ≤ B.length := by
          simp only [LF.add, LF.smul, length_addC, List.length_map]
          omega
        have hv : (M.add (g.smul μ)).val X H ≤ M.val X H := by
          rw [LF.val_add, LF.val_smul]
          have : (μ : ℝ) * g.val X H ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast hμ) hg0
          linarith
        refine ih _ _ hg' hlenN ?_ (hv.trans h2)
        rcases bestMu_spec B E M g best with ⟨h3, -⟩ | h3
        · exact absurd h3 h0
        · rw [h3]
          exact (M.add (g.smul μ)).min_leC hlenN hX hH
  have h6 : (L.smul 6).c.length ≤ B.length := by simpa [LF.smul] using hfit
  have h := key acts (L.smul 6) _ (fun g hg => ⟨hacts g hg, hfit' g hg⟩) h6 ((L.smul 6).min_leC h6 hX hH)
    (by rw [LF.val_smul]; push_cast; exact le_rfl)
  have hd := Int.ediv_mul_le (passMu B E (L.smul 6, (L.smul 6).min B E) acts).2 (by norm_num : (6 : ℤ) ≠ 0)
  have hd' : (((passMu B E (L.smul 6, (L.smul 6).min B E) acts).2 / 6 : ℤ) : ℝ) * 6 ≤
      (passMu B E (L.smul 6, (L.smul 6).min B E) acts).2 := by exact_mod_cast hd
  unfold LF.minD
  linarith

/-! ### Harman's exponent in integers -/

/-- The fixed point of the Hölder sums: `2^40`. -/
def SCF : ℤ := 2 ^ 40

theorem ediv_le_div (a b : ℤ) (hb : 0 < b) : ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast Int.ediv_mul_le a hb.ne'

/-- `⌊SCF/δ_req(P/Q)⌋`, `Q = A − K > 0`, for `P = (1 − θ + κ) DEN`, `K = κ DEN` and a group's least exponent `A/DEN`:
`SCF/2` for `P ≤ Q`; with `m = ⌊(P − 1)/Q⌋`, `⌊SCF Q/(4P − 2mQ)⌋` if `2P ≤ (2m + 1)Q`, else `⌊SCF/(2m + 2)⌋`; and
`0` when `A ≤ K`. -/
def fexact (P K A : ℤ) : ℤ :=
  if A ≤ K then 0
  else if P ≤ A - K then SCF / 2
  else if 2 * P ≤ (2 * ((P - 1) / (A - K)) + 1) * (A - K) then
    SCF * (A - K) / (4 * P - 2 * ((P - 1) / (A - K)) * (A - K))
  else SCF / (2 * ((P - 1) / (A - K)) + 2)

/-- The ramp of `δ_req` at `P/(A − K)`: `m = ⌊(P − 1)/(A − K)⌋` when `m < P/(A − K) ≤ m + 1/2`, else `0`. -/
def fpiece (P K A : ℤ) : ℤ :=
  if A ≤ K then 0 else if P ≤ A - K then 0
  else if 2 * P ≤ (2 * ((P - 1) / (A - K)) + 1) * (A - K) then (P - 1) / (A - K) else 0

/-- The tangent slope of `SCF/δ_req` on the ramp at `A`, per unit of exponent: `⌊⌊4 SCF P/d⌋ DEN/d⌋`,
`d = 4P − 2mQ`. -/
def fslope (P K A : ℤ) : ℤ :=
  SCF * 4 * P / (4 * P - 2 * ((P - 1) / (A - K)) * (A - K)) * DEN / (4 * P - 2 * ((P - 1) / (A - K)) * (A - K))

/-- The integer facts of `m = ⌊(P − 1)/Q⌋` for `0 < Q < P`. -/
theorem ramp_facts {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) :
    1 ≤ (P - 1) / Q ∧ (P - 1) / Q * Q < P ∧ P ≤ ((P - 1) / Q + 1) * Q := by
  refine ⟨(Int.le_ediv_iff_mul_le hQ).2 (by omega), ?_, ?_⟩
  · have := Int.ediv_mul_le (P - 1) hQ.ne'; omega
  · have := Int.lt_ediv_add_one_mul_self (P - 1) hQ; omega

/-- **`fexact` is below `SCF/δ_req`.** -/
theorem fexact_le {P K A : ℤ} (hKA : K < A) :
    (fexact P K A : ℝ) ≤ SCF * (1 / dreq ((P : ℝ) / ((A : ℝ) - K))) := by
  have hQ : 0 < A - K := by omega
  have hQ' : (0 : ℝ) < (A : ℝ) - K := by
    have h' : ((K : ℤ) : ℝ) < A := by exact_mod_cast hKA
    linarith
  have hSCF : (0 : ℝ) < SCF := by norm_num [SCF]
  unfold fexact
  rw [ite_eq_right (by omega : ¬A ≤ K)]
  by_cases h1 : P ≤ A - K
  · rw [ite_eq_left h1]
    have hD : (P : ℝ) / ((A : ℝ) - K) ≤ 1 := by
      rw [div_le_one hQ']
      have : ((P : ℤ) : ℝ) ≤ ((A - K : ℤ) : ℝ) := by exact_mod_cast h1
      push_cast at this; linarith
    have : dreq ((P : ℝ) / ((A : ℝ) - K)) = 2 := by unfold dreq; rw [ite_eq_left hD]
    rw [this]
    norm_num [SCF]
  · rw [ite_eq_right h1]
    obtain ⟨hm1, hm2, hm3⟩ := ramp_facts hQ (not_le.1 h1)
    set m := (P - 1) / (A - K) with hm
    lift m to ℕ using (by omega) with mN hmN
    have hmN1 : 1 ≤ mN := by exact_mod_cast hm1
    have hm2' : (mN : ℝ) * ((A : ℝ) - K) < P := by
      have : ((mN : ℤ) * (A - K) : ℤ) < P := hm2
      have h' : (((mN : ℤ) * (A - K) : ℤ) : ℝ) < (P : ℝ) := by exact_mod_cast this
      push_cast at h'; linarith
    have hm3' : (P : ℝ) ≤ ((mN : ℝ) + 1) * ((A : ℝ) - K) := by
      have h' : ((P : ℤ) : ℝ) ≤ ((((mN : ℤ) + 1) * (A - K) : ℤ) : ℝ) := by exact_mod_cast hm3
      push_cast at h'; linarith
    have hmD : (mN : ℝ) < (P : ℝ) / ((A : ℝ) - K) := by rw [lt_div_iff₀ hQ']; linarith
    have hDm : (P : ℝ) / ((A : ℝ) - K) ≤ mN + 1 := by rw [div_le_iff₀ hQ']; linarith
    rw [ShortSieveWit.dreq_eq_of hmN1 hmD hDm]
    by_cases h2 : 2 * P ≤ (2 * (mN : ℤ) + 1) * (A - K)
    · rw [ite_eq_left h2]
      have h2' : (P : ℝ) / ((A : ℝ) - K) ≤ mN + 1 / 2 := by
        rw [div_le_iff₀ hQ']
        have h' : ((2 * P : ℤ) : ℝ) ≤ (((2 * (mN : ℤ) + 1) * (A - K) : ℤ) : ℝ) := by exact_mod_cast h2
        push_cast at h'; linarith
      rw [ite_eq_left h2']
      have hP0 : 0 < P := by omega
      have hd : 0 < 4 * P - 2 * (mN : ℤ) * (A - K) := by
        have : (mN : ℤ) * (A - K) < P := hm2
        linarith
      refine (ediv_le_div _ _ hd).trans (le_of_eq ?_)
      have hP' : (0 : ℝ) < P := by exact_mod_cast hP0
      have hd' : (0 : ℝ) < 4 * P - 2 * mN * ((A : ℝ) - K) := by linarith
      push_cast
      field_simp
    · rw [ite_eq_right h2]
      have h2' : ¬(P : ℝ) / ((A : ℝ) - K) ≤ mN + 1 / 2 := by
        rw [div_le_iff₀ hQ', not_le]
        have h' : (((2 * (mN : ℤ) + 1) * (A - K) : ℤ) : ℝ) < ((2 * P : ℤ) : ℝ) := by
          exact_mod_cast not_le.1 h2
        push_cast at h'; linarith
      rw [ite_eq_right h2']
      have hd : (0 : ℤ) < 2 * (mN : ℤ) + 2 := by omega
      refine (ediv_le_div _ _ hd).trans (le_of_eq ?_)
      push_cast
      field_simp

/-- On a ramp, `fpiece` is the ramp's `m ≥ 1` and the point lies on it: `m < P/(A − K) ≤ m + 1/2`. -/
theorem fpiece_spec {P K A : ℤ} (h : fpiece P K A ≠ 0) :
    K < A ∧ 1 ≤ fpiece P K A ∧ (fpiece P K A : ℝ) * ((A : ℝ) - K) < P ∧
      2 * (P : ℝ) ≤ (2 * fpiece P K A + 1) * ((A : ℝ) - K) := by
  unfold fpiece at h ⊢
  by_cases h1 : A ≤ K
  · rw [ite_eq_left h1] at h; exact absurd rfl h
  rw [ite_eq_right h1] at h ⊢
  by_cases h2 : P ≤ A - K
  · rw [ite_eq_left h2] at h; exact absurd rfl h
  rw [ite_eq_right h2] at h ⊢
  by_cases h3 : 2 * P ≤ (2 * ((P - 1) / (A - K)) + 1) * (A - K)
  · rw [ite_eq_left h3]
    have hQ : 0 < A - K := by omega
    obtain ⟨hm1, hm2, -⟩ := ramp_facts hQ (not_le.1 h2)
    refine ⟨not_le.1 h1, hm1, ?_, ?_⟩
    · have h' : (((P - 1) / (A - K) * (A - K) : ℤ) : ℝ) < (P : ℝ) := by exact_mod_cast hm2
      push_cast at h'; linarith
    · have h' : ((2 * P : ℤ) : ℝ) ≤ (((2 * ((P - 1) / (A - K)) + 1) * (A - K) : ℤ) : ℝ) := by exact_mod_cast h3
      push_cast at h'; linarith
  · rw [ite_eq_right h3] at h; exact absurd rfl h

/-- **`fslope` is below the tangent slope** on the ramp `m = fpiece P K A`, per `DEN` units of exponent:
`fslope/(SCF DEN) ≤ 4P/(4P − 2m(A − K))²`. -/
theorem fslope_le {P K A : ℤ} (hP : 0 < P) (h : fpiece P K A ≠ 0) :
    (fslope P K A : ℝ) / (SCF * DEN) ≤
      4 * P / (4 * P - 2 * (fpiece P K A : ℝ) * ((A : ℝ) - K)) ^ 2 ∧ 0 ≤ fslope P K A := by
  obtain ⟨hKA, hm1, hm2, -⟩ := fpiece_spec h
  have hpe : fpiece P K A = (P - 1) / (A - K) := by
    unfold fpiece at h ⊢
    rw [ite_eq_right (not_le.2 hKA)] at h ⊢
    by_cases h2 : P ≤ A - K
    · rw [ite_eq_left h2] at h; exact absurd rfl h
    rw [ite_eq_right h2] at h ⊢
    by_cases h3 : 2 * P ≤ (2 * ((P - 1) / (A - K)) + 1) * (A - K)
    · rw [ite_eq_left h3]
    · rw [ite_eq_right h3] at h; exact absurd rfl h
  have hSCF : (0 : ℝ) < SCF := by norm_num [SCF]
  have hD := DEN_pos
  set m := fpiece P K A with hmdef
  set d := 4 * P - 2 * m * (A - K) with hd
  have hdpos : 0 < d := by
    have : (m : ℝ) * ((A : ℝ) - K) < P := hm2
    have hP' : (0 : ℝ) < P := by exact_mod_cast hP
    have h' : (0 : ℝ) < ((4 * P - 2 * m * (A - K) : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast h'
  have hdR : ((d : ℤ) : ℝ) = 4 * P - 2 * (m : ℝ) * ((A : ℝ) - K) := by rw [hd]; push_cast; ring
  have hfs : fslope P K A = SCF * 4 * P / d * DEN / d := by
    unfold fslope; rw [← hpe]
  have hq0 : 0 ≤ SCF * 4 * P / d := Int.ediv_nonneg (by norm_num [SCF]; omega) hdpos.le
  have h0 : 0 ≤ fslope P K A := by
    rw [hfs]; exact Int.ediv_nonneg (mul_nonneg hq0 (by norm_num [DEN])) hdpos.le
  refine ⟨?_, h0⟩
  rw [div_le_iff₀ (mul_pos hSCF hD), ← hdR, hfs]
  have e1 := ediv_le_div (SCF * 4 * P / d * DEN) d hdpos
  have e2 := ediv_le_div (SCF * 4 * P) d hdpos
  have hdR' : (0 : ℝ) < d := by exact_mod_cast hdpos
  have e3 : ((SCF * 4 * P / d * DEN : ℤ) : ℝ) ≤ (SCF * 4 * P : ℝ) / d * DEN := by
    push_cast
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast e2) hD.le
  calc ((SCF * 4 * P / d * DEN / d : ℤ) : ℝ) ≤ ((SCF * 4 * P / d * DEN : ℤ) : ℝ) / d := e1
    _ ≤ (SCF * 4 * P : ℝ) / d * DEN / d := div_le_div_of_nonneg_right e3 hdR'.le
    _ = 4 * P / (d : ℝ) ^ 2 * (SCF * DEN) := by field_simp

/-! ### The check -/

/-- The zero form. -/
def LF.zero : LF := ⟨0, [], 0⟩

theorem LF.val_zero (X : ℕ → ℝ) (H : ℝ) : LF.zero.val X H = 0 := by simp [LF.zero, LF.val, dotR]

/-- The sum of the forms `f t` over a list. -/
def sumLF {α : Type*} (f : α → LF) (l : List α) : LF := l.foldr (fun t acc => (f t).add acc) LF.zero

theorem val_sumLF {α : Type*} (f : α → LF) (X : ℕ → ℝ) (H : ℝ) :
    ∀ l : List α, (sumLF f l).val X H = (l.map fun t => (f t).val X H).sum
  | [] => by simp [sumLF, LF.val_zero]
  | t :: l => by
    simp only [sumLF, List.foldr_cons, List.map_cons, List.sum_cons] at *
    rw [LF.val_add, ← val_sumLF f X H l]
    rfl

theorem length_sumLF {α : Type*} (f : α → LF) {n : ℕ} :
    ∀ l : List α, (∀ t ∈ l, (f t).c.length ≤ n) → (sumLF f l).c.length ≤ n
  | [], _ => by simp [sumLF, LF.zero]
  | t :: l, h => by
    have h1 := h t List.mem_cons_self
    have h2 := length_sumLF f l fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    show ((f t).add (sumLF f l)).c.length ≤ n
    simp only [LF.add, length_addC]
    omega

/-- The form of a group: the sum of the items with label `g`. -/
def grpLF (items : List LF) (labels : List ℕ) (g : ℕ) : LF :=
  sumLF Prod.fst ((items.zip labels).filter fun p => p.2 = g)

theorem length_grpLF {items : List LF} {n : ℕ} (h : ∀ L ∈ items, L.c.length ≤ n) (labels : List ℕ) (g : ℕ) :
    (grpLF items labels g).c.length ≤ n :=
  length_sumLF _ _ fun p hp => h p.1 (List.of_mem_zip (List.mem_filter.1 hp).1).1

/-- The tangent term of a group with domain-aware least and largest exponents `lo`, `hi`: `fslope(lo) (L − lo)` when
both lie on one ramp, else `0`. -/
def tanLF (P K : ℤ) (L : LF) (lo hi : ℤ) : LF :=
  if fpiece P K lo ≠ 0 ∧ fpiece P K lo = fpiece P K hi then (L.add ⟨-lo, [], 0⟩).smul (fslope P K lo) else LF.zero

/-- A group with its domain-aware least and largest exponents. -/
def grpData (B : Box) (E : ℤ) (acts : List LF) (L : LF) : LF × ℤ × ℤ :=
  (L, L.minD B E acts, -((L.smul (-1)).minD B E acts))

/-- **The linearised Type II check** (the generator's `checkTIIlin`): every group's least exponent exceeds `K`, and
`Σ_g ⌊SCF/δ_req(lo_g)⌋ + ⌊max(0, min_B Σ_g tan_g)/DEN⌋ > SCF`. -/
def tiiCheck (P K E : ℤ) (B : Box) (acts : List LF) (items : List LF) (labels : List ℕ) (ng : ℕ) : Bool :=
  let lh := (List.range ng).map fun g => grpData B E acts (grpLF items labels g)
  lh.all (fun t => decide (K < t.2.1)) &&
    decide (SCF < (lh.map fun t => fexact P K t.2.1).sum +
      max 0 ((sumLF (fun t => tanLF P K t.1 t.2.1 t.2.2) lh).min B E) / DEN)

theorem list_sum_map_range (f : ℕ → ℝ) : ∀ n : ℕ, ((List.range n).map f).sum = ∑ i ∈ range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_map_range f n, sum_range_succ]
    simp

theorem cast_list_sum_map_range (f : ℕ → ℤ) : ∀ n : ℕ,
    ((((List.range n).map f).sum : ℤ) : ℝ) = ∑ i ∈ range n, (f i : ℝ)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, Int.cast_add, cast_list_sum_map_range f n,
      sum_range_succ]
    simp

theorem val_tanLF (P K : ℤ) (L : LF) (lo hi : ℤ) (X : ℕ → ℝ) (H : ℝ) :
    (tanLF P K L lo hi).val X H =
      if fpiece P K lo ≠ 0 ∧ fpiece P K lo = fpiece P K hi then (fslope P K lo : ℝ) * (L.val X H - lo) else 0 := by
  unfold tanLF
  split_ifs
  · rw [LF.val_smul, LF.val_add]
    have e : (⟨-lo, [], 0⟩ : LF).val X H = -lo := by simp [LF.val, dotR]
    rw [e]
    ring
  · exact LF.val_zero X H

/-- **A passing check gives Harman's test.** At a point of the closed box where every active constraint is `≤ 0`,
every group's exponent `a_g` (in units of `1/DEN`) exceeds `K` and `Σ_g 1/δ_req(P/(a_g − K)) > 1`. -/
theorem lt_sum_of_tiiCheck {P K E : ℤ} (hP : 0 < P) {B : Box} {acts items : List LF} {labels : List ℕ} {ng : ℕ}
    (hcheck : tiiCheck P K E B acts items labels ng = true) (hfit : ∀ L ∈ items, L.c.length ≤ B.length)
    (hfa : ∀ g ∈ acts, g.c.length ≤ B.length) {X : ℕ → ℝ} (hX : InBoxC B X) {H : ℝ} (hH : |H| ≤ E)
    (hacts : ∀ g ∈ acts, g.val X H ≤ 0) :
    (∀ g < ng, (K : ℝ) < (grpLF items labels g).val X H) ∧
      1 < ∑ g ∈ range ng, 1 / dreq ((P : ℝ) / ((grpLF items labels g).val X H - K)) := by
  unfold tiiCheck at hcheck
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_map, List.mem_range] at hcheck
  obtain ⟨hK, hS⟩ := hcheck
  have hSCF : (0 : ℝ) < SCF := by norm_num [SCF]
  have hD := DEN_pos
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  set Lg := fun g : ℕ => grpLF items labels g with hLg
  set lo := fun g : ℕ => (Lg g).minD B E acts with hlo
  set hi := fun g : ℕ => -(((Lg g).smul (-1)).minD B E acts) with hhi
  have hfitG : ∀ g, (Lg g).c.length ≤ B.length := fun g => length_grpLF hfit labels g
  -- each group's exponent lies between its least and largest values
  have hlo_le : ∀ g, (lo g : ℝ) ≤ (Lg g).val X H := fun g => (Lg g).minD_le acts hX hH hacts (hfitG g) hfa
  have hle_hi : ∀ g, (Lg g).val X H ≤ hi g := fun g => by
    have h := ((Lg g).smul (-1)).minD_le acts hX hH hacts (by simpa [LF.smul] using hfitG g) hfa
    rw [LF.val_smul] at h
    simp only [hhi, Int.cast_neg]
    push_cast at h
    linarith
  have hKlo : ∀ g < ng, K < lo g := fun g hg => hK _ ⟨g, hg, rfl⟩
  refine ⟨fun g hg => lt_of_lt_of_le (by exact_mod_cast hKlo g hg) (hlo_le g), ?_⟩
  -- the tangent terms
  set F : Fin ng → ℝ := fun g => (fexact P K (lo g) : ℝ) / SCF with hF
  set sl : Fin ng → ℝ := fun g => if fpiece P K (lo g) ≠ 0 ∧ fpiece P K (lo g) = fpiece P K (hi g) then
    (fslope P K (lo g) : ℝ) / (SCF * DEN) else 0 with hsl
  have key := ShortSieveWit.lt_sum_inv_dreq_of_linear (G := ng) (c := P) (c' := P) (κ := K) (κ' := K) hP' le_rfl
    (fun g => (Lg g).val X H) (fun g => (Lg g).val X H) (fun g => (lo g : ℝ)) F sl
    (fun g => ⟨by exact_mod_cast hKlo g g.2, hlo_le g⟩) (fun g => le_rfl)
    (fun g => by
      have h := fexact_le (P := P) (hKlo g g.2)
      simp only [hF]
      rw [div_le_iff₀ hSCF]
      linarith)
    (fun g => by
      simp only [hsl]
      split_ifs with hs
      · obtain ⟨hs1, hs2⟩ := hs
        obtain ⟨-, hm1, -, hlo2⟩ := fpiece_spec hs1
        obtain ⟨-, -, hhi1, -⟩ := fpiece_spec (hs2 ▸ hs1)
        obtain ⟨hsle, -⟩ := fslope_le hP hs1
        obtain ⟨mN, hmN⟩ : ∃ n : ℕ, (n : ℤ) = fpiece P K (lo g) := ⟨_, Int.toNat_of_nonneg (by omega)⟩
        have e : ((fpiece P K (lo g) : ℤ) : ℝ) = (mN : ℝ) := by rw [← hmN]; norm_cast
        have e' : ((fpiece P K (hi g) : ℤ) : ℝ) = (mN : ℝ) := by rw [← hs2, e]
        rw [e] at hlo2 hsle
        rw [e'] at hhi1
        have hm1' : 1 ≤ mN := by rw [← hmN] at hm1; exact_mod_cast hm1
        have hKl : (K : ℝ) < lo g := by exact_mod_cast hKlo g g.2
        refine Or.inr ⟨mN, hm1', ?_, ?_, hsle⟩
        · -- `m < P/(a − K)` from the largest exponent on the ramp
          have ha0 : (0 : ℝ) < (Lg g).val X H - K := by linarith [hlo_le g]
          rw [lt_div_iff₀ ha0]
          nlinarith [mul_le_mul_of_nonneg_left (hle_hi g) (Nat.cast_nonneg (α := ℝ) mN)]
        · have hl0 : (0 : ℝ) < (lo g : ℝ) - K := by linarith
          rw [div_le_iff₀ hl0]
          linarith
      · exact Or.inl le_rfl)
    ?_
  · -- conclude
    rw [Finset.sum_range]
    exact key
  · -- the check's sum
    have e1 : ∑ g : Fin ng, (F g + sl g * ((Lg g).val X H - lo g)) =
        ∑ g ∈ range ng, ((fexact P K (lo g) : ℝ) / SCF + (if fpiece P K (lo g) ≠ 0 ∧
          fpiece P K (lo g) = fpiece P K (hi g) then (fslope P K (lo g) : ℝ) / (SCF * DEN) else 0) *
          ((Lg g).val X H - lo g)) :=
      Fin.sum_univ_eq_sum_range (fun g => (fexact P K (lo g) : ℝ) / SCF + (if fpiece P K (lo g) ≠ 0 ∧
          fpiece P K (lo g) = fpiece P K (hi g) then (fslope P K (lo g) : ℝ) / (SCF * DEN) else 0) *
          ((Lg g).val X H - lo g)) ng
    rw [e1]
    -- the tangent form's value at the point
    set T := sumLF (fun t : LF × ℤ × ℤ => tanLF P K t.1 t.2.1 t.2.2)
      ((List.range ng).map fun g => grpData B E acts (grpLF items labels g)) with hT
    have hTval : T.val X H = ∑ g ∈ range ng, (tanLF P K (Lg g) (lo g) (hi g)).val X H := by
      rw [hT, val_sumLF, List.map_map, list_sum_map_range]
      rfl
    have hterm : ∀ g, 0 ≤ (tanLF P K (Lg g) (lo g) (hi g)).val X H := fun g => by
      rw [val_tanLF]
      split_ifs with hs
      · exact mul_nonneg (by exact_mod_cast (fslope_le hP hs.1).2) (by linarith [hlo_le g])
      · exact le_rfl
    have hT0 : 0 ≤ T.val X H := by rw [hTval]; exact sum_nonneg fun g _ => hterm g
    have hTmin : (T.min B E : ℝ) ≤ T.val X H :=
      T.min_leC (length_sumLF _ _ fun t ht => by
        obtain ⟨g, -, rfl⟩ := List.mem_map.1 ht
        unfold tanLF grpData
        split_ifs
        · simp only [LF.smul, LF.add, List.length_map, length_addC, List.length_nil]
          have := hfitG g
          simp only [hLg] at this
          omega
        · simp [LF.zero]) hX hH
    -- `⌊max(0, min T)/DEN⌋ ≤ T(X)/DEN`
    have hmax : ((max 0 (T.min B E) / DEN : ℤ) : ℝ) ≤ T.val X H / DEN := by
      have h1 := ediv_le_div (max 0 (T.min B E)) DEN (by norm_num [DEN])
      refine h1.trans (div_le_div_of_nonneg_right ?_ hD.le)
      push_cast
      exact max_le hT0 hTmin
    -- the check in real numbers
    have hfx : ((((List.range ng).map fun g => grpData B E acts (grpLF items labels g)).map
        fun t => fexact P K t.2.1).sum : ℝ) = ∑ g ∈ range ng, (fexact P K (lo g) : ℝ) := by
      rw [List.map_map]
      exact cast_list_sum_map_range _ ng
    have hS' : (SCF : ℝ) < ∑ g ∈ range ng, (fexact P K (lo g) : ℝ) + T.val X H / DEN := by
      have h1 : (SCF : ℝ) < ((((List.range ng).map fun g => grpData B E acts (grpLF items labels g)).map
          fun t => fexact P K t.2.1).sum : ℝ) + ((max 0 (T.min B E) / DEN : ℤ) : ℝ) := by exact_mod_cast hS
      rw [hfx] at h1
      linarith
    have e2 : ∀ g ∈ range ng, (fexact P K (lo g) : ℝ) / SCF + (if fpiece P K (lo g) ≠ 0 ∧
        fpiece P K (lo g) = fpiece P K (hi g) then (fslope P K (lo g) : ℝ) / (SCF * DEN) else 0) *
        ((Lg g).val X H - lo g) = (fexact P K (lo g) : ℝ) / SCF +
          (tanLF P K (Lg g) (lo g) (hi g)).val X H / (SCF * DEN) := fun g _ => by
      rw [val_tanLF]
      split_ifs
      · field_simp
      · simp
    rw [sum_congr rfl e2, sum_add_distrib, ← sum_div, ← sum_div, ← hTval]
    have h3 := mul_lt_mul_of_pos_right hS' (mul_pos hD hSCF)
    have h4 : (∑ g ∈ range ng, (fexact P K (lo g) : ℝ) + T.val X H / DEN) * (DEN * SCF) =
        ((∑ g ∈ range ng, (fexact P K (lo g) : ℝ)) / SCF + T.val X H / (SCF * DEN)) * (SCF * (DEN * SCF)) := by
      field_simp
    rw [h4] at h3
    have h7 : (1 : ℝ) * (SCF * (DEN * SCF)) < ((∑ g ∈ range ng, (fexact P K (lo g) : ℝ)) / SCF +
        T.val X H / (SCF * DEN)) * (SCF * (DEN * SCF)) := by rw [one_mul]; exact h3
    exact lt_of_mul_lt_mul_right h7 (by positivity)

end ShortSieveCert

#print axioms ShortSieveCert.LF.minD_le
#print axioms ShortSieveCert.fexact_le
#print axioms ShortSieveCert.fslope_le
#print axioms ShortSieveCert.lt_sum_of_tiiCheck
