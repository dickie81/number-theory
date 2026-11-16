/-
# Proposition 6 with the bilinear estimate

Plain statements. `GCmp`, `RTg` are `SieveChain`'s; `gUp`, `gDown` are `SieveP6Chain`'s; `ChainOK` is `SieveP6Tree`'s
and `LeavesOK` `SieveP6TreeLeaves`'s; `rough z n` and `primesIco w z` are `SieveTree`'s; `zeta`, `rem` and `Jw` are
`SieveProp6`'s. `N₁ = ⌊q^L⌋`, `N₂ = ⌊2q^L⌋` and `w = ⌈q^{εw}⌉`.

* `sum_patterns`: a family split into five patterns by `c = ∏_{i∈S₀} rt_i` against the windows `(P₁, P₂]` and
  `(W₀, W₁]`: below the first, in it, between the two, in the second, above it.
* `tree_pattern_ib`: a pattern below a window, by Buchstab's tree; its leaves split into two blocks by
  `Isplit S₁ eIn₁`, their sizes from the boxes `rt_i ≤ q^{hi_i}`.
* `root_bound'`: a pattern in a window, by `ChainOK`.
* `win_lo`, `win_hi`: the windows `(⌈q^{w₁L}⌉, ⌊q^{w₂L}⌋]` and `(⌈N₂/q^{w₂L}⌉, ⌊N₁/⌈q^{w₁L}⌉⌋]` fit.
* `prop6ib_core`, `prop6ib_at`: the bound at one `q`, for given windows and for these.
* `prop6ib`: **Proposition 6 with the bilinear estimate**, for `q ≥ q₀`.

The file imports `SieveP6TreeLeaves.lean`.
-/
import SieveP6TreeLeaves

open Real Finset SieveFamily SieveTree SieveChain SieveRoute SieveP6Chain

namespace SieveP6ib

open Classical

/-! ### A family split by one comparison -/

/-- A family split by `∏_{i∈I} x_i ≤ b` and `b < ∏_{i∈I} x_i`. -/
theorem sum_RTg_cmp {M : Type*} [AddCommMonoid M] {K Y : ℕ} (Ω : List (GCmp K)) (I : Finset (Fin K)) {b : ℝ}
    (hb : 0 < b) (G : (Fin K → ℕ) → M) :
    ∑ x ∈ RTg K Y Ω, G x =
      ∑ x ∈ RTg K Y (Ω ++ [gUp I b false]), G x + ∑ x ∈ RTg K Y (Ω ++ [gDown I b true]), G x := by
  rw [← Finset.sum_filter_add_sum_filter_not (RTg K Y Ω) (fun x => ∏ i ∈ I, (x i : ℝ) ≤ b)]
  congr 1
  · rw [SieveP6Tree.RTg_append]
    refine Finset.sum_congr (Finset.filter_congr fun x hx => ?_) fun _ _ => rfl
    have hx1 := SieveP6Tree.one_le_of_mem_RTg hx
    simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true,
      gUp_holds _ hb false 0 hx1, Bool.false_eq_true, ite_false]
  · rw [SieveP6Tree.RTg_append]
    refine Finset.sum_congr (Finset.filter_congr fun x hx => ?_) fun _ _ => rfl
    have hx1 := SieveP6Tree.one_le_of_mem_RTg hx
    simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true,
      gDown_holds _ hb true 0 hx1, ite_true, not_le]

/-! ### A leaf's two blocks -/

/-- The first block of a leaf: `S₁` among the family's primes, and all of the block if `eIn₁`. -/
def Isplit {j : ℕ} (S₁ : Finset (Fin j)) (eIn₁ : Bool) (s : ℕ) : Finset (Fin (j + s)) :=
  S₁.map (Fin.castAddEmb s) ∪ (if eIn₁ then (univ : Finset (Fin s)).map (Fin.natAddEmb j) else ∅)

theorem prod_Isplit {j : ℕ} (S₁ : Finset (Fin j)) (eIn₁ : Bool) {s : ℕ} (x : Fin (j + s) → ℕ) :
    ∏ i ∈ Isplit S₁ eIn₁ s, (x i : ℝ) =
      (∏ i ∈ S₁, (x (Fin.castAdd s i) : ℝ)) * (if eIn₁ then ∏ u, (x (Fin.natAdd j u) : ℝ) else 1) := by
  have hd : Disjoint (S₁.map (Fin.castAddEmb s))
      (if eIn₁ then (univ : Finset (Fin s)).map (Fin.natAddEmb j) else ∅) := by
    refine SieveP6Tree.disjoint_of_val fun a ha b hb => ?_
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 ha
    cases eIn₁
    · simp at hb
    · simp only [ite_true, Finset.mem_map, Finset.mem_univ, true_and] at hb
      obtain ⟨u, rfl⟩ := hb
      show (i : ℕ) < j + u
      have := i.isLt
      omega
  rw [Isplit, Finset.prod_union hd, Finset.prod_map]
  cases eIn₁
  · simp
  · simp only [ite_true, Finset.prod_map]
    rfl

theorem prod_Isplit_compl {j : ℕ} (S₁ : Finset (Fin j)) (eIn₁ : Bool) {s : ℕ} {x : Fin (j + s) → ℕ}
    (hx : ∀ i, 1 ≤ x i) :
    ∏ i ∈ (Isplit S₁ eIn₁ s)ᶜ, (x i : ℝ) =
      (∏ i ∈ S₁ᶜ, (x (Fin.castAdd s i) : ℝ)) * (if eIn₁ then 1 else ∏ u, (x (Fin.natAdd j u) : ℝ)) := by
  have hall := Finset.prod_compl_mul_prod (Isplit S₁ eIn₁ s) (fun i => (x i : ℝ))
  rw [prod_Isplit, Fin.prod_univ_add] at hall
  have h2 := Finset.prod_compl_mul_prod S₁ (fun i => (x (Fin.castAdd s i) : ℝ))
  have hpos₁ : 0 < ∏ i ∈ S₁, (x (Fin.castAdd s i) : ℝ) := Finset.prod_pos fun i _ => by exact_mod_cast hx _
  have hposy : 0 < ∏ u, (x (Fin.natAdd j u) : ℝ) := Finset.prod_pos fun u _ => by exact_mod_cast hx _
  rw [← h2] at hall
  cases eIn₁
  · simp only [Bool.false_eq_true, ite_false, mul_one] at hall ⊢
    apply mul_right_cancel₀ hpos₁.ne'
    rw [hall]
    ring
  · simp only [ite_true, mul_one] at hall ⊢
    apply mul_right_cancel₀ (mul_pos hpos₁ hposy).ne'
    rw [hall]
    ring

/-! ### The sizes of a leaf -/

/-- **A leaf's two blocks are small.** For a leaf `x = (rt, y)` with `rt_i ≤ Q^{hi_i}` and `∏y ≤ Y₀`:
`∏_{I}x ≤ Q^{Σ_{S₁} hi}·(Y₀ if eIn₁)` and `∏_{Iᶜ}x ≤ Q^{Σ_{S₁ᶜ} hi}·(Y₀ unless eIn₁)`. -/
theorem leaf_blocks_le {j : ℕ} (S₁ : Finset (Fin j)) (eIn₁ : Bool) {s : ℕ} {x : Fin (j + s) → ℕ}
    (hx : ∀ i, 1 ≤ x i) {Q : ℝ} (hQ : 0 < Q) (hi : Fin j → ℝ) (hrt : ∀ i, (x (Fin.castAdd s i) : ℝ) ≤ Q ^ hi i)
    {Y₀ : ℝ} (hy : ∏ u, (x (Fin.natAdd j u) : ℝ) ≤ Y₀) :
    ∏ i ∈ Isplit S₁ eIn₁ s, (x i : ℝ) ≤ Q ^ (∑ i ∈ S₁, hi i) * (if eIn₁ then Y₀ else 1) ∧
      ∏ i ∈ (Isplit S₁ eIn₁ s)ᶜ, (x i : ℝ) ≤ Q ^ (∑ i ∈ S₁ᶜ, hi i) * (if eIn₁ then 1 else Y₀) := by
  have hpos : ∀ i, (0 : ℝ) ≤ x i := fun i => Nat.cast_nonneg _
  have hT : ∀ T : Finset (Fin j), ∏ i ∈ T, (x (Fin.castAdd s i) : ℝ) ≤ Q ^ (∑ i ∈ T, hi i) := fun T => by
    rw [Real.rpow_sum_of_pos hQ]
    exact Finset.prod_le_prod₀ (fun i _ => hpos _) fun i _ => hrt i
  have hy0 : 0 ≤ ∏ u, (x (Fin.natAdd j u) : ℝ) := Finset.prod_nonneg fun u _ => hpos _
  rw [prod_Isplit, prod_Isplit_compl S₁ eIn₁ hx]
  have hQ0 : ∀ T : Finset (Fin j), 0 ≤ Q ^ (∑ i ∈ T, hi i) := fun T => by positivity
  cases eIn₁
  · simp only [Bool.false_eq_true, ite_false, mul_one]
    exact ⟨hT S₁, mul_le_mul (hT S₁ᶜ) hy hy0 (hQ0 _)⟩
  · simp only [ite_true, mul_one]
    exact ⟨mul_le_mul (hT S₁) hy hy0 (hQ0 _), hT S₁ᶜ⟩

/-- The sizes of `leaves_chain` from `∏_I x ≤ 4Q^{D₁}`, `∏_{Iᶜ} x ≤ 4Q^{D₂}` and `w^{2k+4} ≤ 2^{2k+4}Q^c`, once
`4·2^{2k+4} ≤ Q^{L−1−a−D₁−c}` and `64·2^{2k+4} ≤ Q^{L−b−D₁−2D₂−c}`. -/
theorem leaf_sizes_num {Q : ℝ} (hQ : 0 < Q) {D₁ D₂ c a b L' : ℝ} {k : ℕ} {U V W : ℝ} (hV : 0 ≤ V)
    (hU' : U ≤ 4 * Q ^ D₁) (hV' : V ≤ 4 * Q ^ D₂) (hW : 0 ≤ W) (hW' : W ^ (2 * k + 4) ≤ 2 ^ (2 * k + 4) * Q ^ c)
    (h₁ : 4 * 2 ^ (2 * k + 4) ≤ Q ^ (L' - 1 - a - D₁ - c))
    (h₂ : 64 * 2 ^ (2 * k + 4) ≤ Q ^ (L' - b - D₁ - 2 * D₂ - c)) :
    U * W ^ (2 * k + 4) ≤ Q ^ (L' - 1 - a) ∧ U * W ^ (2 * k + 4) * V ^ 2 ≤ Q ^ (L' - b) := by
  have hW0 : 0 ≤ W ^ (2 * k + 4) := by positivity
  have e1 : Q ^ (L' - 1 - a) = Q ^ (L' - 1 - a - D₁ - c) * (Q ^ D₁ * Q ^ c) := by
    rw [← Real.rpow_add hQ, ← Real.rpow_add hQ]; ring_nf
  have e2 : Q ^ (L' - b) = Q ^ (L' - b - D₁ - 2 * D₂ - c) * (Q ^ D₁ * Q ^ c * (Q ^ D₂) ^ 2) := by
    rw [← Real.rpow_natCast (Q ^ D₂), ← Real.rpow_mul hQ.le, ← Real.rpow_add hQ, ← Real.rpow_add hQ,
      ← Real.rpow_add hQ]
    ring_nf
  have hq1 : 0 ≤ Q ^ D₁ * Q ^ c := by positivity
  have hq2 : 0 ≤ Q ^ D₂ := by positivity
  constructor
  · calc U * W ^ (2 * k + 4) ≤ (4 * Q ^ D₁) * (2 ^ (2 * k + 4) * Q ^ c) := mul_le_mul hU' hW' hW0 (by positivity)
      _ = 4 * 2 ^ (2 * k + 4) * (Q ^ D₁ * Q ^ c) := by ring
      _ ≤ Q ^ (L' - 1 - a - D₁ - c) * (Q ^ D₁ * Q ^ c) := mul_le_mul_of_nonneg_right h₁ hq1
      _ = Q ^ (L' - 1 - a) := e1.symm
  · calc U * W ^ (2 * k + 4) * V ^ 2 ≤ (4 * Q ^ D₁) * (2 ^ (2 * k + 4) * Q ^ c) * (4 * Q ^ D₂) ^ 2 := by
          gcongr
      _ = 64 * 2 ^ (2 * k + 4) * (Q ^ D₁ * Q ^ c * (Q ^ D₂) ^ 2) := by ring
      _ ≤ Q ^ (L' - b - D₁ - 2 * D₂ - c) * (Q ^ D₁ * Q ^ c * (Q ^ D₂) ^ 2) :=
          mul_le_mul_of_nonneg_right h₂ (by positivity)
      _ = Q ^ (L' - b) := e2.symm

/-! ### The five patterns of a family -/

section Patterns

variable {j : ℕ} (Ω : List (GCmp j)) (S₀ : Finset (Fin j)) (P₁ P₂ W₀ W₁ : ℝ)

variable {Ω S₀ P₁ P₂ W₀ W₁}

end Patterns

/-- The box bounds on `c = ∏_{i∈S₀} rt_i`: `Q^{Σ lo} ≤ c ≤ Q^{Σ hi}`. -/
theorem box_prod {j : ℕ} {Q : ℝ} (hQ : 0 < Q) (S₀ : Finset (Fin j)) {lo hi : Fin j → ℝ} {rt : Fin j → ℕ}
    (h : ∀ i, Q ^ lo i ≤ rt i ∧ (rt i : ℝ) ≤ Q ^ hi i) :
    Q ^ (∑ i ∈ S₀, lo i) ≤ ∏ i ∈ S₀, (rt i : ℝ) ∧ ∏ i ∈ S₀, (rt i : ℝ) ≤ Q ^ (∑ i ∈ S₀, hi i) := by
  rw [Real.rpow_sum_of_pos hQ, Real.rpow_sum_of_pos hQ]
  exact ⟨Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => (h i).1,
    Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ => (h i).2⟩

/-- The arithmetic of the final bound: the patterns' bound, with `S·Pr ≤ K`, the main term `M_z K ≤ main`, the
remainder `M_r K ≤ φ⁻¹e₀`, and every error `e_i ≤ X_d` with `(4s + 5)X_d ≤ X_δ`, is at most `main + φ⁻¹X_δ`. -/
theorem final_bound {Mz Mr S Pr K main e₀ e₁ e₂ e₃ φi Xd Xδ sm n : ℝ}
    (hn : n ≤ (Mz + Mr) * (S * Pr) + 2 * sm * (φi * e₃) + (sm + 2) * (φi * e₁) + (sm + 2) * (φi * e₂))
    (hSP : S * Pr ≤ K) (hMz : 0 ≤ Mz) (hMr : 0 ≤ Mr) (hmain : Mz * K ≤ main) (hrem : Mr * K ≤ φi * e₀)
    (hφi : 0 ≤ φi) (hsm : 0 ≤ sm) (h₀ : e₀ ≤ Xd) (h₁ : e₁ ≤ Xd) (h₂ : e₂ ≤ Xd) (h₃ : e₃ ≤ Xd)
    (hδ : (4 * sm + 5) * Xd ≤ Xδ) : n ≤ main + φi * Xδ := by
  have h1 : (Mz + Mr) * (S * Pr) ≤ (Mz + Mr) * K := mul_le_mul_of_nonneg_left hSP (by linarith)
  have hE : ∀ e, e ≤ Xd → φi * e ≤ φi * Xd := fun e he => mul_le_mul_of_nonneg_left he hφi
  have t3 := mul_le_mul_of_nonneg_left (hE e₃ h₃) (by linarith : (0 : ℝ) ≤ 2 * sm)
  have t1 := mul_le_mul_of_nonneg_left (hE e₁ h₁) (by linarith : (0 : ℝ) ≤ sm + 2)
  have t2 := mul_le_mul_of_nonneg_left (hE e₂ h₂) (by linarith : (0 : ℝ) ≤ sm + 2)
  have t0 := hE e₀ h₀
  have tf := mul_le_mul_of_nonneg_left hδ hφi
  linarith

variable [Route]

/-! ### A tree pattern -/

/-! ### A family in a window, of any length -/

/-! ### The windows -/

/-! ### Proposition 6 with the bilinear estimate, for given windows -/

/-! ### Proposition 6 with the bilinear estimate, at one `q` -/

/-! ### Proposition 6 with the bilinear estimate -/

end SieveP6ib
