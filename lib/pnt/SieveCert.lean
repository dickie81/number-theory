/-
# The certificate of the sieve route's loss, checked by the kernel

The loss certificate of the sieve route is computed here in natural numbers on a grid of cells (`Grid`: the window's
ends, the number `n` of cells a side and the cells' multiplier). Each cell's bound is computed from its corners,
rounding up twice (the value of `ω*`, then the bound), and is a multiple of `2^{−60}`. The library's certificate is on
`grid22000E`, the grid of the curve `g7d` at `L = 11/5` on the window `[43457/100000, 46959/100000]` with `n = 272`
(`SieveGrid22000E.lean`), and is the one of `SieveDeepDefs.lean`, to depth 8; the kernel checks it by
`decide +kernel` (`SieveCert22000E.lean`).

* The grid. Coordinates are multiples of `1/DEN`, `DEN = 2^40`. The window's ends are `U1 < U2` (for `grid22000E`,
  `U1 = ⌈(43457/100000)DEN⌉` and `U2 = ⌊(46959/100000)DEN⌋`), `V = U2 − U1`, and the cells of side
  `H = ⌈(DEN/2 − V)/n⌉` start at `e k = V + Hk`. `GridOK` lists the facts about the grid that the semantic lemmas below
  and the route's proofs use; for a given grid each is checked by `decide`.
* The tests, as in the certificate: `cand` (a cell of `(α₁, α₂)` that may meet the region and may be non-evaluable),
  `inKK` and `ne3` (the cells of `α₃`), and `counted4` (the cells of depth 4). Evaluability is a subset sum of the
  cell's corners inside `U = (u₁, u₂) ∪ (1 − u₂, 1 − u₁)` (`surelyEval`).
* The bound `ω*` for Buchstab's `ω` (`omegaC`): `0` below `1`, `1/u` on `[1, 2)`, Buchstab's `(1 + log(u − 1))/u` on
  `[2, 3]` and `0.565073` above. On a cell, `omKw` (and `omK`, its case of `m` cells of side `H`) bounds it on the
  arguments the cell's points can have, from its corners.
* The bounds: `omK/K` times a factor for each cell, the trapezoid bound `trB a H = H(2a + H)/(2a(a + H))` of the cell's
  `Σ 1/p` for the first ones and the exact `exB a H = DEN·H/(a(a + H))` of the last cell's `log x · Σ 1/(p log p)`,
  rounded up to a multiple of `2^{−60}` (`bound2`).

The semantic lemmas:

* `omegaC_le_w`: `ω*` on the box's arguments, widened by `τ < 1/DEN`, is at most `omKw/K`; on `[2, 3]` by Buchstab's
  `ω` at the box's ends where it is monotone (`SieveOmegaB`).
* `bound2_ge`: the bound is at least `omK/K` times the cells' `trB` and `exB`.

The grid is a parameter (`Grid`, with `GridOK`); the certificates' grids are in `SieveGrid…`.

The file imports Mathlib, `SieveCertDefs.lean`, which holds the definitions, and `SieveOmegaB.lean`.
-/
import Mathlib
import SieveCertDefs
import SieveOmegaB

namespace SieveCert

/-! The definitions that the certificate builds on (`DEN` … `counted6`) and the class `GridOK` are in
`SieveCertDefs.lean`. -/

variable [Grid]

/-! ### Sums -/

omit [Grid] in
theorem sumTo_eq (m : ℕ) (f : ℕ → ℕ) : sumTo m f = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Finset.sum_range_succ, ← ih]; rfl

/-! ### Facts about the grid -/

omit [Grid] in
theorem DEN_pos : 0 < DEN := by decide

variable [GridOK]

theorem H_pos : 0 < H := GridOK.H_pos
theorem U1_lt_U2 : U1 < U2 := GridOK.U1_lt_U2
theorem two_U2_lt : 2 * U2 < DEN := GridOK.two_U2_lt
theorem U2_le_DEN : U2 ≤ DEN := by have := two_U2_lt; omega
theorem U1_le_DEN : U1 ≤ DEN := le_trans U1_lt_U2.le U2_le_DEN
theorem V_pos : 0 < V := by unfold V; have := U1_lt_U2; omega
theorem two_e_lt (i : ℕ) (hi : i < n) : 2 * e i < DEN := by
  have h : 2 * e (n - 1) < DEN := GridOK.two_e_lt
  have hle : e i ≤ e (n - 1) := by
    unfold e
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  omega
theorem n_pos : 0 < n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · have h0 := H_pos
    unfold H at h0
    rw [h, Nat.zero_mul, Nat.div_zero, Nat.mul_zero] at h0
    exact absurd h0 (lt_irrefl 0)
  · exact h
theorem two_V_lt : 2 * V < DEN := by simpa [e] using two_e_lt 0 n_pos
/-- For a grid with `GridOK`, the grid's top `V + nH` lies above `DEN/2`. -/
theorem DEN_lt_top : DEN < 2 * (V + n * H) := GridOK.DEN_lt_top
/-- For a grid with `GridOK`, the grid's top `V + nH` is at most `DEN`. -/
theorem top_le_DEN : V + n * H ≤ DEN := by
  have h1 : 2 * e (n - 1) < DEN := GridOK.two_e_lt
  have h2 : 4 * H ≤ V := GridOK.four_H_le_V
  have h3 := two_V_lt
  have hn : n * H = H * (n - 1) + H := by
    calc n * H = ((n - 1) + 1) * H := by rw [Nat.sub_add_cancel n_pos]
      _ = H * (n - 1) + H := by ring
  unfold e at h1
  omega

/-! ### Points -/

noncomputable section

/-- `α ∈ [e k, e k + H)/DEN`. -/
def InCell (k : ℕ) (α : ℝ) : Prop := (e k : ℝ) ≤ α * DEN ∧ α * DEN < e k + H

omit [Grid] [GridOK] in
theorem DEN_pos' : (0 : ℝ) < DEN := by exact_mod_cast DEN_pos

omit [GridOK] in
theorem insideF_eq (lo hi : ℕ) : insideF lo hi = inside lo hi := by
  simp only [insideF, inside]
  rw [Bool.eq_iff_iff]
  simp [Nat.blt_eq]

omit [GridOK] in
theorem anySub_eq (xs : List (ℕ × ℕ)) : ∀ a b : ℕ,
    anySub xs a b = (subsetSums xs).any (fun s => inside (a + s.1) (b + s.2)) := by
  induction xs with
  | nil => intro a b; simp [anySub, insideF_eq, subsetSums]
  | cons p rest ih =>
    intro a b
    simp only [anySub, ih, subsetSums, List.any_append, List.any_map, Function.comp_def]
    congr 2
    funext s
    simp only [Nat.add_assoc, Nat.add_left_comm s.1 p.1, Nat.add_left_comm s.2 p.2]
    simp [Nat.add_comm p.1, Nat.add_comm p.2, Nat.add_assoc, Nat.add_left_comm]

omit [GridOK] in
/-- `surelyEval` (the unrolled search) is `surelyEvalSpec` (the list of all subset sums). -/
theorem surelyEval_eq (xs : List (ℕ × ℕ)) : surelyEval xs = surelyEvalSpec xs := by
  have key : ∀ xs : List (ℕ × ℕ), anySub xs 0 0 = surelyEvalSpec xs := fun xs => by
    simp [surelyEvalSpec, anySub_eq]
  match xs with
  | [] => rw [← key]; rfl
  | [p] => rw [← key]; rfl
  | [p, q] => rw [← key]; rfl
  | [p, q, r] => rw [← key]; rfl
  | [p, q, r, s] => rw [← key]; rfl
  | [p, q, r, s, t] => rw [← key]; rfl
  | [p, q, r, s, t, u] => rw [← key]; rfl
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => simp [surelyEval]

theorem exists_cell {α : ℝ} (h0 : (V : ℝ) ≤ α * DEN) (h1 : α * DEN < V + n * H) : ∃ k < n, InCell k α := by
  have hH : (0 : ℝ) < H := by exact_mod_cast H_pos
  set y := (α * DEN - V) / H with hy
  have hy0 : 0 ≤ y := div_nonneg (by linarith) hH.le
  refine ⟨⌊y⌋₊, ?_, ?_, ?_⟩
  · have : y < n := by rw [hy, div_lt_iff₀ hH]; linarith
    exact_mod_cast (Nat.floor_lt hy0).2 this
  · have hf := Nat.floor_le hy0
    simp only [e]
    push_cast
    have : (⌊y⌋₊ : ℝ) * H ≤ α * DEN - V := by
      calc (⌊y⌋₊ : ℝ) * H ≤ y * H := by gcongr
        _ = α * DEN - V := by rw [hy]; field_simp
    linarith
  · have hf := Nat.lt_floor_add_one y
    simp only [e]
    push_cast
    have : α * DEN - V < ((⌊y⌋₊ : ℝ) + 1) * H := by
      calc α * DEN - V = y * H := by rw [hy]; field_simp
        _ < ((⌊y⌋₊ : ℝ) + 1) * H := by gcongr
    linarith

omit [GridOK] in
theorem e_add_H_le {j : ℕ} (hj : j < n) : (e j : ℝ) + H ≤ V + n * H := by
  have : e j + H ≤ V + n * H := by
    unfold e
    have : H * j + H ≤ n * H := by nlinarith
    omega
  exact_mod_cast this

/-! ### The bound `ω*` for Buchstab's `ω` -/

/-- The upper bound `ω*` for Buchstab's `ω`: `0` below `1`, `1/u` on `[1, 2)`, Buchstab's own `(1 + log(u − 1))/u` on
`[2, 3]` (`SieveOmegaB.omB`) and `0.565073` above `3`. -/
def omegaC (u : ℝ) : ℝ :=
  if u < 1 then 0 else if u < 2 then 1 / u else if u ≤ 3 then SieveOmegaB.omB u else 565073 / 1000000

omit [Grid] [GridOK] in
theorem K_pos' : (0 : ℝ) < K := by norm_num [K]

omit [Grid] [GridOK] in
theorem topK_ge : (565073 / 1000000 : ℝ) ≤ topK / K := by
  rw [le_div_iff₀ K_pos']
  have h : K * 565073 ≤ topK * 1000000 := by decide
  have h' : (K : ℝ) * 565073 ≤ topK * 1000000 := by exact_mod_cast h
  linarith

omit [Grid] [GridOK] in
theorem w1K_ge : (5671433 / 10000000 : ℝ) ≤ w1K / K := by
  rw [le_div_iff₀ K_pos']
  have h : K * 5671433 ≤ w1K * 10000000 := by decide
  have h' : (K : ℝ) * 5671433 ≤ w1K * 10000000 := by exact_mod_cast h
  linarith

omit [Grid] [GridOK] in
theorem div_le_cdiv (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ cdiv a b := SieveOmegaB.div_le_cdiv a b hb

omit [Grid] [GridOK] in
/-- `ω*` is at most `0.565073` from `3` on (`ω(3) = (1 + log 2)/3 ≤ 0.565073`). -/
theorem omegaC_le_of_three_le {u : ℝ} (h3 : 3 ≤ u) : omegaC u ≤ 565073 / 1000000 := by
  unfold omegaC
  rw [ite_eq_right (not_lt.mpr (by linarith)), ite_eq_right (not_lt.mpr (by linarith))]
  split_ifs with h
  · rw [le_antisymm h h3]; exact SieveOmegaB.omB_three_le
  · exact le_rfl

omit [Grid] [GridOK] in
/-- **`ω*` on a box.** Let the other exponents sum to `σ` and the last be `α`, with `s ≤ σ·DEN`, `t ≤ α·DEN ≤ t + w`
and `(σ + α)DEN ≤ s + t + W`, as for the lower corner `(s, t)` of a box whose widths sum to `W`, the last `w`. Then on
the argument `(1 − σ − α + τ)/α`, widened by `0 ≤ τ < 1/DEN`, `ω*` is at most `omKw s t W w / K`. The argument lies
in `[lo, hi)`, `lo = (DEN − s − t − W)/(t + w)` and `hi = (DEN + 1 − s − t)/t`, and `omKw`'s tests read its place
there. -/
theorem omegaC_le_w {s t W w : ℕ} {σ α τ : ℝ} (ht : 0 < t) (hσ : (s : ℝ) ≤ σ * DEN) (hα : (t : ℝ) ≤ α * DEN)
    (hαH : α * DEN ≤ t + w) (hsum : (σ + α) * DEN ≤ s + t + W) (hτ0 : 0 ≤ τ) (hτ : τ * DEN < 1) :
    omegaC ((1 - σ - α + τ) / α) ≤ (omKw s t W w : ℝ) / K := by
  have hD := DEN_pos'
  have hK := K_pos'
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hα0 : 0 < α := by
    by_contra h
    have : α * DEN ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hD.le
    linarith
  have hτD : 0 ≤ τ * DEN := mul_nonneg hτ0 hD.le
  set u := (1 - σ - α + τ) / α with hu
  have hua : u * α = 1 - σ - α + τ := by rw [hu]; field_simp
  -- the tests of `omKw`, read on `u`
  have lt1 : DEN < s + 2 * t → u < 1 := by
    intro h
    have h' : (DEN : ℝ) + 1 ≤ s + 2 * t := by exact_mod_cast h
    have : (1 + τ) * DEN < (σ + 2 * α) * DEN := by nlinarith
    have : 1 + τ < σ + 2 * α := lt_of_mul_lt_mul_right this hD.le
    nlinarith
  have ge2 : s + 3 * t + W + 2 * w ≤ DEN → 2 ≤ u := by
    intro h
    have h' : (s : ℝ) + 3 * t + W + 2 * w ≤ DEN := by exact_mod_cast h
    have : (σ + 3 * α) * DEN ≤ (1 + τ) * DEN := by nlinarith
    have : σ + 3 * α ≤ 1 + τ := le_of_mul_le_mul_right this hD
    nlinarith
  have lt2 : DEN < s + 3 * t → u < 2 := by
    intro h
    have h' : (DEN : ℝ) + 1 ≤ s + 3 * t := by exact_mod_cast h
    have : (1 + τ) * DEN < (σ + 3 * α) * DEN := by nlinarith
    have : 1 + τ < σ + 3 * α := lt_of_mul_lt_mul_right this hD.le
    nlinarith
  have ge3 : s + 4 * t + W + 3 * w ≤ DEN → 3 ≤ u := by
    intro h
    have h' : (s : ℝ) + 4 * t + W + 3 * w ≤ DEN := by exact_mod_cast h
    have : (σ + 4 * α) * DEN ≤ (1 + τ) * DEN := by nlinarith
    have : σ + 4 * α ≤ 1 + τ := le_of_mul_le_mul_right this hD
    nlinarith
  have lt3 : DEN < s + 4 * t → u < 3 := by
    intro h
    have h' : (DEN : ℝ) + 1 ≤ s + 4 * t := by exact_mod_cast h
    have : (1 + τ) * DEN < (σ + 4 * α) * DEN := by nlinarith
    have : 1 + τ < σ + 4 * α := lt_of_mul_lt_mul_right this hD.le
    nlinarith
  -- `u` against the box's ends
  have hhi : 0 ≤ u → u * t < (DEN : ℝ) + 1 - s - t := by
    intro hu0
    have h1 : u * t ≤ u * (α * DEN) := mul_le_mul_of_nonneg_left hα hu0
    have h2 : u * (α * DEN) = (1 - σ - α + τ) * DEN := by rw [← mul_assoc, hua]
    nlinarith
  have hlo : 0 ≤ u → (DEN : ℝ) - s - t - W ≤ u * (t + w) := by
    intro hu0
    have h1 : u * (α * DEN) ≤ u * (t + w) := mul_le_mul_of_nonneg_left hαH hu0
    have h2 : u * (α * DEN) = (1 - σ - α + τ) * DEN := by rw [← mul_assoc, hua]
    nlinarith
  -- `1/u ≤ invKw/K` for `u ≥ 1`
  have hinv : 1 ≤ u → 1 / u ≤ (invKw s t W w : ℝ) / K := by
    intro hu1
    have hu0 : 0 < u := by linarith
    unfold invKw
    by_cases hC : DEN ≤ s + 2 * t + W + w
    · simp only [hC, ite_true, div_self (ne_of_gt hK)]
      rw [div_le_one hu0]; exact hu1
    · simp only [hC, ite_false]
      have hDnat : s + t + W < DEN := by omega
      have hpos : 0 < DEN - s - t - W := by omega
      have hDcast : ((DEN - s - t - W : ℕ) : ℝ) = (DEN : ℝ) - s - t - W := by
        have h1 : s ≤ DEN := by omega
        have h2 : t ≤ DEN - s := by omega
        have h3 : W ≤ DEN - s - t := by omega
        rw [Nat.cast_sub h3, Nat.cast_sub h2, Nat.cast_sub h1]
      have hc := div_le_cdiv (K * (t + w)) (DEN - s - t - W) hpos
      rw [hDcast] at hc
      push_cast at hc
      have hDpos : (0 : ℝ) < (DEN : ℝ) - s - t - W := by
        have : (s : ℝ) + t + W < DEN := by exact_mod_cast hDnat
        linarith
      have hi : 1 / u ≤ (t + w) / ((DEN : ℝ) - s - t - W) := by
        rw [div_le_div_iff₀ hu0 hDpos]
        linarith [hlo hu0.le]
      rw [le_div_iff₀ hK]
      calc 1 / u * K ≤ (t + w) / ((DEN : ℝ) - s - t - W) * K := by gcongr
        _ = K * (t + w) / ((DEN : ℝ) - s - t - W) := by ring
        _ ≤ _ := hc
  have hinv0 : (0 : ℝ) ≤ (invKw s t W w : ℝ) / K := by positivity
  -- the cases of `omKw`
  by_cases hA : DEN < s + 2 * t
  · have hu1 := lt1 hA
    have h0 : omKw s t W w = 0 := by simp [omKw, hA]
    rw [h0]
    simp [omegaC, hu1]
  by_cases hB : s + 4 * t + W + 3 * w ≤ DEN
  · have h0 : omKw s t W w = topK := by simp [omKw, hA, hB]
    rw [h0]
    exact (omegaC_le_of_three_le (ge3 hB)).trans topK_ge
  by_cases hC : DEN < s + 3 * t
  · have hu2 := lt2 hC
    have h0 : omKw s t W w = invKw s t W w := by simp [omKw, hA, hB, hC]
    rw [h0]
    by_cases hu1 : u < 1
    · simp only [omegaC, hu1, ite_true]; exact hinv0
    · simp only [omegaC, hu1, hu2, ite_false, ite_true]; exact hinv (not_lt.mp hu1)
  have hs3 : s + 3 * t ≤ DEN := not_lt.mp hC
  have h0 : omKw s t W w = max (max (if s + 3 * t + W + 2 * w ≤ DEN then 0 else invKw s t W w)
      (if 100 * (DEN + 1 - s - t) ≤ 276 * t then omF (DEN + 1 - s - t) t
        else if 277 * (t + w) ≤ 100 * (DEN - s - t - W) then omF (DEN - s - t - W) (t + w) else w1K))
      (if s + 4 * t ≤ DEN then topK else 0) := by
    simp only [omKw, hA, hB, hC, ite_false]
  rw [h0, Nat.cast_max, Nat.cast_max, ← max_div_div_right hK.le, ← max_div_div_right hK.le]
  by_cases hu1 : u < 1
  · have : omegaC u = 0 := by simp [omegaC, hu1]
    rw [this]
    exact le_trans (by positivity) (le_max_right _ _)
  by_cases hu2 : u < 2
  · -- `ω* = 1/u`; then `lo < 2`
    have hp1 : (if s + 3 * t + W + 2 * w ≤ DEN then 0 else invKw s t W w) = invKw s t W w := by
      rw [ite_eq_right]; intro h; have := ge2 h; linarith
    have : omegaC u = 1 / u := by simp [omegaC, hu1, hu2]
    rw [this, hp1]
    exact le_trans (hinv (not_lt.mp hu1)) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hu2' : 2 ≤ u := not_lt.mp hu2
  by_cases hu3 : u ≤ 3
  · -- `ω* = omB u`, bounded by the part on `[2, 3]`
    have hω : omegaC u = SieveOmegaB.omB u := by simp [omegaC, hu1, hu2, hu3]
    rw [hω]
    refine le_trans ?_ (le_trans (le_max_right _ _) (le_max_left _ _))
    split_ifs with hhi276 hlo277
    · -- `hi ≤ 2.76`: `ω` increases up to `hi`
      have hs1 : s ≤ DEN + 1 := by omega
      have ht1 : t ≤ DEN + 1 - s := by omega
      have hcast : ((DEN + 1 - s - t : ℕ) : ℝ) = (DEN : ℝ) + 1 - s - t := by
        rw [Nat.cast_sub ht1, Nat.cast_sub hs1]; push_cast; ring
      have hP2 : 2 * t ≤ DEN + 1 - s - t := by omega
      have hP3 : DEN + 1 - s - t ≤ 3 * t := by omega
      have hle : u ≤ ((DEN + 1 - s - t : ℕ) : ℝ) / t := by
        rw [le_div_iff₀ ht', hcast]; exact (hhi (by linarith)).le
      have h276 : ((DEN + 1 - s - t : ℕ) : ℝ) / t ≤ 276 / 100 := by
        rw [div_le_div_iff₀ ht' (by norm_num)]
        have : ((100 * (DEN + 1 - s - t) : ℕ) : ℝ) ≤ ((276 * t : ℕ) : ℝ) := by exact_mod_cast hhi276
        push_cast at this
        linarith
      exact (SieveOmegaB.omB_mono hu2' hle h276).trans (SieveOmegaB.omF_ge ht hP2 hP3)
    · -- `lo ≥ 2.77`: `ω` decreases from `lo`
      have hW : s + t + W ≤ DEN := by
        by_contra h
        have h' : DEN - s - t - W = 0 := by omega
        rw [h'] at hlo277
        omega
      have hs1 : s ≤ DEN := by omega
      have ht1 : t ≤ DEN - s := by omega
      have hW1 : W ≤ DEN - s - t := by omega
      have hcast : ((DEN - s - t - W : ℕ) : ℝ) = (DEN : ℝ) - s - t - W := by
        rw [Nat.cast_sub hW1, Nat.cast_sub ht1, Nat.cast_sub hs1]
      have hQ : 0 < t + w := by omega
      have hQ' : (0 : ℝ) < ((t + w : ℕ) : ℝ) := by exact_mod_cast hQ
      have hP2 : 2 * (t + w) ≤ DEN - s - t - W := by omega
      have hP3 : DEN - s - t - W ≤ 3 * (t + w) := by omega
      have hge : ((DEN - s - t - W : ℕ) : ℝ) / ((t + w : ℕ) : ℝ) ≤ u := by
        rw [div_le_iff₀ hQ', hcast]
        push_cast
        linarith [hlo (by linarith)]
      have h277 : 277 / 100 ≤ ((DEN - s - t - W : ℕ) : ℝ) / ((t + w : ℕ) : ℝ) := by
        rw [div_le_div_iff₀ (by norm_num) hQ']
        have : ((277 * (t + w) : ℕ) : ℝ) ≤ ((100 * (DEN - s - t - W) : ℕ) : ℝ) := by exact_mod_cast hlo277
        push_cast at this ⊢
        linarith
      exact (SieveOmegaB.omB_anti h277 hge).trans (SieveOmegaB.omF_ge hQ hP2 hP3)
    · exact (SieveOmegaB.omB_le_w1 (by linarith)).trans w1K_ge
  · -- `u > 3`: `ω* = 0.565073`, and `hi > 3`
    have hs4 : s + 4 * t ≤ DEN := by
      by_contra h
      have := lt3 (not_le.mp h)
      linarith
    have hω : omegaC u = 565073 / 1000000 := by simp [omegaC, hu1, hu2, hu3]
    rw [hω, ite_eq_left hs4]
    exact topK_ge.trans (le_max_right _ _)

omit [GridOK] in
theorem omK_eq_omKw (s t m : ℕ) : omK s t m = omKw s t (m * H) H := rfl

/-! ### The cells' bounds -/

theorem e_pos (k : ℕ) : 0 < e k := by unfold e; have := V_pos; omega

omit [Grid] [GridOK] in
/-- The trapezoid bound of a cell's `Σ 1/p`, for the cell `[a, a + w]` (in units of `1/DEN`):
`w(2a + w)/(2a(a + w))`, at least `log(1 + w/a)` (`SieveOmegaB.log_le_half_sub_inv`). -/
def trB (a w : ℕ) : ℝ := (w : ℝ) * (2 * a + w) / (2 * a * (a + w))

omit [Grid] [GridOK] in
/-- The last cell's `log x · Σ 1/(p log p)`, for the cell `[a, a + w]`: `DEN·w/(a(a + w)) = DEN(1/a − 1/(a + w))`. -/
def exB (a w : ℕ) : ℝ := (DEN : ℝ) * w / (a * (a + w))

omit [Grid] [GridOK] in
theorem trB_nonneg (a w : ℕ) : 0 ≤ trB a w := by unfold trB; positivity

omit [Grid] [GridOK] in
theorem exB_nonneg (a w : ℕ) : 0 ≤ exB a w := by unfold exB; positivity

omit [GridOK] in
/-- A cell of depth 2 with lower corner `(a, b)` costs at least `omK/K` times the first cell's trapezoid bound and the
last cell's `DEN·H/(b(b + H))`. -/
theorem bound2_ge {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    trB a H * exB b H * ((omK a b 2 : ℝ) / K) ≤ (bound2 a b : ℝ) / K := by
  have hD := DEN_pos'
  have hK := K_pos'
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have haH : (0 : ℝ) < a + H := by positivity
  have hbH : (0 : ℝ) < b + H := by positivity
  have hc := div_le_cdiv (H * H * (2 * a + H) * DEN * omK a b 2) (2 * a * (a + H) * (b * (b + H))) (by positivity)
  have heq : trB a H * exB b H * ((omK a b 2 : ℝ) / K) =
      ((H * H * (2 * a + H) * DEN * omK a b 2 : ℕ) : ℝ) / ((2 * a * (a + H) * (b * (b + H)) : ℕ) : ℝ) / K := by
    simp only [trB, exB]; push_cast; field_simp
  rw [heq, bound2]
  exact div_le_div_of_nonneg_right hc hK.le

/-! ### The costs -/

end

end SieveCert

#print axioms SieveCert.bound2_ge
#print axioms SieveCert.omK_eq_omKw
#print axioms SieveCert.omegaC_le_w
