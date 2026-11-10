/-
# The family of a box as a family of atoms

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. The estimates of the library are stated for families cut out by atoms (`SieveDecomp.famSet`), or by
the comparisons of atoms (`SieveChain.RTg`). The family of a box (`SieveAd.famB`) is one:

* `specB q bx`: the atoms of the box `bx` at the modulus `q`: for each prime its two cell ends, `x^{lo_i/DEN} ≤ p_i`
  and `p_i < x^{hi_i/DEN}`, and for each two consecutive primes `p_{i+1} < p_i`. They are at most `3k`.
* `sem_specB`: a tuple satisfies them exactly when it is strictly decreasing with its primes in their cells;
  `famB_eq_famSet`: so the family of the box is `famSet k N₂ (specB q bx)`.
* `thrOK_specB`: for `x ≥ 1` and cells with ends at most `DEN`, the atoms' thresholds lie in `[1, q^{L+1}]`
  (`SieveLeaves.ThrOK`).
* `ofFn_boxFn`: the cells of a list, by the prime's index, are the list reversed.
* `le_Xq`: for `δ > 0` and `η > 0`, `q^{L−δ} ≤ η·x/log x` for large `q`.

The file imports `SieveAdTree.lean`.
-/
import SieveAdTree

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN DEN_pos')

/-- The cells of a list, by the prime's index, are the list reversed. -/
theorem ofFn_boxFn : ∀ (bl : List Cell) (k : ℕ) (h : bl.length = k), List.ofFn (boxFn bl k h) = bl.reverse := by
  intro bl
  induction bl with
  | nil =>
    intro k h
    subst h
    simp
  | cons x bl ih =>
    intro k h
    subst h
    show List.ofFn (boxFn (x :: bl) (bl.length + 1) rfl) = _
    rw [boxFn_cons x bl bl.length rfl, List.ofFn_succ', List.reverse_cons]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [List.concat_eq_append, ← ih bl.length rfl]

variable [Route]

/-- The atoms of a box: the cells' ends, and the order of consecutive primes. -/
noncomputable def specB (q : ℕ) : {k : ℕ} → (Fin k → Cell) → List (Atom k)
  | 0, _ => []
  | k' + 1, bx =>
    (List.ofFn fun i : Fin (k' + 1) => Atom.ge i (xq q ^ (((bx i).1 : ℝ) / DEN))) ++
      ((List.ofFn fun i : Fin (k' + 1) => Atom.lt i (xq q ^ (((bx i).2 : ℝ) / DEN))) ++
        List.ofFn fun i : Fin k' => Atom.ltVar i.castSucc i.succ)

theorem specB_length (q : ℕ) {k : ℕ} (bx : Fin k → Cell) : (specB q bx).length ≤ 3 * k := by
  cases k with
  | zero => simp [specB]
  | succ k' =>
    simp only [specB, List.length_append, List.length_ofFn]
    omega

/-- A tuple satisfies the atoms of a box exactly when it is strictly decreasing with its primes in their cells. -/
theorem sem_specB (q : ℕ) {k : ℕ} (bx : Fin k → Cell) (rt : Fin k → ℕ) :
    (∀ A ∈ specB q bx, A.sem rt) ↔ StrictAnti rt ∧
      ∀ i, xq q ^ (((bx i).1 : ℝ) / DEN) ≤ rt i ∧ (rt i : ℝ) < xq q ^ (((bx i).2 : ℝ) / DEN) := by
  cases k with
  | zero =>
    simp only [specB, List.not_mem_nil, false_implies, implies_true, true_iff]
    exact ⟨fun a => a.elim0, fun i => i.elim0⟩
  | succ k' =>
    simp only [specB, List.forall_mem_append, List.forall_mem_ofFn_iff, Atom.sem_ge, Atom.sem_lt, Atom.sem_ltVar]
    rw [Fin.strictAnti_iff_succ_lt]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h3, fun i => ⟨h1 i, h2 i⟩⟩
    · rintro ⟨h3, h12⟩
      exact ⟨fun i => (h12 i).1, fun i => (h12 i).2, h3⟩

/-- The family of a box is the family of its atoms. -/
theorem famB_eq_famSet (q : ℕ) {k : ℕ} (bx : Fin k → Cell) : famB q bx = famSet k (N2 q) (specB q bx) := by
  ext rt
  rw [mem_famB, mem_famSet, sem_specB]

/-- For `x ≥ 1` and cells with ends at most `DEN`, the thresholds of the box's atoms lie in `[1, q^{L+1}]`. -/
theorem thrOK_specB {q : ℕ} (hq : 1 ≤ q) (hL : 0 ≤ L) {k : ℕ} (bx : Fin k → Cell)
    (hb : ∀ i, (bx i).1 ≤ DEN ∧ (bx i).2 ≤ DEN) : ThrOK q (specB q bx) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hx1 : 1 ≤ xq q := Real.one_le_rpow hq1 hL
  have hD := DEN_pos'
  have hpow : ∀ a : ℕ, a ≤ DEN → 1 ≤ xq q ^ ((a : ℝ) / DEN) ∧ xq q ^ ((a : ℝ) / DEN) ≤ (q : ℝ) ^ (L + 1 : ℝ) := by
    intro a ha
    refine ⟨Real.one_le_rpow hx1 (by positivity), ?_⟩
    have h1 : xq q ^ ((a : ℝ) / DEN) ≤ xq q ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by rw [div_le_one hD]; exact_mod_cast ha)
    rw [Real.rpow_one] at h1
    exact h1.trans (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith))
  have hone : (1 : ℝ) ≤ (q : ℝ) ^ (L + 1 : ℝ) := Real.one_le_rpow hq1 (by linarith)
  cases k with
  | zero =>
    intro A hA
    simp [specB] at hA
  | succ k' =>
    intro A hA
    simp only [specB, List.mem_append, List.mem_ofFn] at hA
    rcases hA with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact hpow _ (hb i).1
    · exact hpow _ (hb i).2
    · exact ⟨le_refl _, hone⟩

/-- For `δ > 0` and `η > 0`: `q^{L−δ} ≤ η·x/log x` for large `q`. -/
theorem le_Xq [RouteOK] {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) : ∀ᶠ q : ℕ in atTop, (q : ℝ) ^ (L - δ) ≤ η * Xq q := by
  have hL0 : 0 < L := L_pos
  filter_upwards [SieveMain.ev_log_le (c := η / L) (r := δ) (by positivity) hδ, eventually_ge_atTop 2] with q hq hq2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hlogx : Real.log (xq q) = L * Real.log q := Real.log_rpow hq0 _
  unfold Xq
  rw [hlogx, ← mul_div_assoc, le_div_iff₀ (by positivity)]
  have h1 : L * Real.log q ≤ η * (q : ℝ) ^ δ := by
    have := hq
    rw [div_mul_eq_mul_div, le_div_iff₀ hL0] at this
    linarith
  have hsplit : (q : ℝ) ^ (L - δ) * (q : ℝ) ^ δ = xq q := by
    rw [← Real.rpow_add hq0, sub_add_cancel]
  calc (q : ℝ) ^ (L - δ) * (L * Real.log q) ≤ (q : ℝ) ^ (L - δ) * (η * (q : ℝ) ^ δ) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = η * xq q := by rw [← hsplit]; ring

end SieveAd
