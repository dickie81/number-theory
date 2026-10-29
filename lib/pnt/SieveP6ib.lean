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

/-- `c ≤ P₁`, with `c = ∏_{i∈S₀} rt_i`. -/
noncomputable def patB : List (GCmp j) := Ω ++ [gUp S₀ P₁ false]

/-- `P₁ < c ≤ P₂`. -/
noncomputable def patW : List (GCmp j) := Ω ++ [gDown S₀ P₁ true] ++ [gUp S₀ P₂ false]

/-- `P₁ < c`, `P₂ < c ≤ W₀`. -/
noncomputable def patM : List (GCmp j) := Ω ++ [gDown S₀ P₁ true] ++ [gDown S₀ P₂ true] ++ [gUp S₀ W₀ false]

/-- `P₁ < c`, `P₂ < c`, `W₀ < c ≤ W₁`. -/
noncomputable def patR : List (GCmp j) :=
  Ω ++ [gDown S₀ P₁ true] ++ [gDown S₀ P₂ true] ++ [gDown S₀ W₀ true] ++ [gUp S₀ W₁ false]

/-- `P₁ < c`, `P₂ < c`, `W₀ < c`, `W₁ < c`. -/
noncomputable def patA : List (GCmp j) :=
  Ω ++ [gDown S₀ P₁ true] ++ [gDown S₀ P₂ true] ++ [gDown S₀ W₀ true] ++ [gDown S₀ W₁ true]

/-- **The five patterns partition the family.** -/
theorem sum_patterns {M : Type*} [AddCommMonoid M] {Y : ℕ} {P₁ P₂ W₀ W₁ : ℝ} (h1 : 0 < P₁) (h2 : 0 < P₂)
    (h3 : 0 < W₀) (h4 : 0 < W₁) (G : (Fin j → ℕ) → M) :
    ∑ x ∈ RTg j Y Ω, G x = ∑ x ∈ RTg j Y (patB Ω S₀ P₁), G x + ∑ x ∈ RTg j Y (patW Ω S₀ P₁ P₂), G x +
      ∑ x ∈ RTg j Y (patM Ω S₀ P₁ P₂ W₀), G x + ∑ x ∈ RTg j Y (patR Ω S₀ P₁ P₂ W₀ W₁), G x +
        ∑ x ∈ RTg j Y (patA Ω S₀ P₁ P₂ W₀ W₁), G x := by
  rw [sum_RTg_cmp Ω S₀ h1 G, sum_RTg_cmp (Ω ++ [gDown S₀ P₁ true]) S₀ h2 G,
    sum_RTg_cmp (Ω ++ [gDown S₀ P₁ true] ++ [gDown S₀ P₂ true]) S₀ h3 G,
    sum_RTg_cmp (Ω ++ [gDown S₀ P₁ true] ++ [gDown S₀ P₂ true] ++ [gDown S₀ W₀ true]) S₀ h4 G]
  simp only [patB, patW, patM, patR, patA]
  abel

theorem length_patB : (patB Ω S₀ P₁).length = Ω.length + 1 := by simp [patB]
theorem length_patW : (patW Ω S₀ P₁ P₂).length = Ω.length + 2 := by simp [patW]
theorem length_patM : (patM Ω S₀ P₁ P₂ W₀).length = Ω.length + 3 := by simp [patM]
theorem length_patR : (patR Ω S₀ P₁ P₂ W₀ W₁).length = Ω.length + 4 := by simp [patR]

variable {Ω S₀ P₁ P₂ W₀ W₁}

theorem forall_append_singleton {α : Type*} {P : α → Prop} {l : List α} {a : α} :
    (∀ x ∈ l ++ [a], P x) ↔ (∀ x ∈ l, P x) ∧ P a := by
  rw [List.forall_mem_append, List.forall_mem_singleton]

/-- The `m`-parts of the patterns' comparisons. -/
theorem pat_c_le {B : ℝ} (hc : ∀ C ∈ Ω, C.c 0 ≤ B) (hP₁ : Real.log P₁ ≤ B) (hP₂ : Real.log P₂ ≤ B)
    (hW₀ : Real.log W₀ ≤ B) (hW₁ : Real.log W₁ ≤ B) (hd : ∀ b : ℝ, 1 ≤ b → -Real.log b ≤ B) (hP₁1 : 1 ≤ P₁)
    (hP₂1 : 1 ≤ P₂) (hW₀1 : 1 ≤ W₀) :
    (∀ C ∈ patB Ω S₀ P₁, C.c 0 ≤ B) ∧ (∀ C ∈ patW Ω S₀ P₁ P₂, C.c 0 ≤ B) ∧
      (∀ C ∈ patM Ω S₀ P₁ P₂ W₀, C.c 0 ≤ B) ∧ (∀ C ∈ patR Ω S₀ P₁ P₂ W₀ W₁, C.c 0 ≤ B) := by
  have d1 : (gDown S₀ P₁ true).c 0 ≤ B := hd P₁ hP₁1
  have d2 : (gDown S₀ P₂ true).c 0 ≤ B := hd P₂ hP₂1
  have d3 : (gDown S₀ W₀ true).c 0 ≤ B := hd W₀ hW₀1
  have u1 : (gUp S₀ P₁ false).c 0 ≤ B := hP₁
  have u2 : (gUp S₀ P₂ false).c 0 ≤ B := hP₂
  have u3 : (gUp S₀ W₀ false).c 0 ≤ B := hW₀
  have u4 : (gUp S₀ W₁ false).c 0 ≤ B := hW₁
  have h1 := forall_append_singleton.2 ⟨hc, d1⟩
  have h2 := forall_append_singleton.2 ⟨h1, d2⟩
  have h3 := forall_append_singleton.2 ⟨h2, d3⟩
  exact ⟨forall_append_singleton.2 ⟨hc, u1⟩, forall_append_singleton.2 ⟨h1, u2⟩,
    forall_append_singleton.2 ⟨h2, u3⟩, forall_append_singleton.2 ⟨h3, u4⟩⟩

/-- What the patterns say, at a tuple with entries at least `1` and `c = ∏_{i∈S₀} rt_i`. -/
theorem pat_holds {x : Fin j → ℕ} (hx : ∀ i, 1 ≤ x i) (h1 : 0 < P₁) (h2 : 0 < P₂) (h3 : 0 < W₀) (h4 : 0 < W₁) :
    ((∀ C ∈ patB Ω S₀ P₁, C.holds 0 x) → (∀ C ∈ Ω, C.holds 0 x) ∧ ∏ i ∈ S₀, (x i : ℝ) ≤ P₁) ∧
    ((∀ C ∈ patW Ω S₀ P₁ P₂, C.holds 0 x) →
      (∀ C ∈ Ω, C.holds 0 x) ∧ P₁ < ∏ i ∈ S₀, (x i : ℝ) ∧ ∏ i ∈ S₀, (x i : ℝ) ≤ P₂) ∧
    ((∀ C ∈ patM Ω S₀ P₁ P₂ W₀, C.holds 0 x) →
      (∀ C ∈ Ω, C.holds 0 x) ∧ P₂ < ∏ i ∈ S₀, (x i : ℝ) ∧ ∏ i ∈ S₀, (x i : ℝ) ≤ W₀) ∧
    ((∀ C ∈ patR Ω S₀ P₁ P₂ W₀ W₁, C.holds 0 x) →
      (∀ C ∈ Ω, C.holds 0 x) ∧ W₀ < ∏ i ∈ S₀, (x i : ℝ) ∧ ∏ i ∈ S₀, (x i : ℝ) ≤ W₁) ∧
    ((∀ C ∈ patA Ω S₀ P₁ P₂ W₀ W₁, C.holds 0 x) → W₁ < ∏ i ∈ S₀, (x i : ℝ)) := by
  have u : ∀ {b : ℝ}, 0 < b → (gUp S₀ b false).holds 0 x → ∏ i ∈ S₀, (x i : ℝ) ≤ b := fun hb h => by
    simpa using (gUp_holds S₀ hb false 0 hx).1 h
  have d : ∀ {b : ℝ}, 0 < b → (gDown S₀ b true).holds 0 x → b < ∏ i ∈ S₀, (x i : ℝ) := fun hb h => by
    simpa using (gDown_holds S₀ hb true 0 hx).1 h
  simp only [patB, patW, patM, patR, patA, forall_append_singleton]
  refine ⟨fun h => ⟨h.1, u h1 h.2⟩, fun h => ⟨h.1.1, d h1 h.1.2, u h2 h.2⟩,
    fun h => ⟨h.1.1.1, d h2 h.1.2, u h3 h.2⟩, fun h => ⟨h.1.1.1.1, d h3 h.1.2, u h4 h.2⟩, fun h => d h4 h.2⟩

end Patterns

/-- The box bounds on `c = ∏_{i∈S₀} rt_i`: `Q^{Σ lo} ≤ c ≤ Q^{Σ hi}`. -/
theorem box_prod {j : ℕ} {Q : ℝ} (hQ : 0 < Q) (S₀ : Finset (Fin j)) {lo hi : Fin j → ℝ} {rt : Fin j → ℕ}
    (h : ∀ i, Q ^ lo i ≤ rt i ∧ (rt i : ℝ) ≤ Q ^ hi i) :
    Q ^ (∑ i ∈ S₀, lo i) ≤ ∏ i ∈ S₀, (rt i : ℝ) ∧ ∏ i ∈ S₀, (rt i : ℝ) ≤ Q ^ (∑ i ∈ S₀, hi i) := by
  rw [Real.rpow_sum_of_pos hQ, Real.rpow_sum_of_pos hQ]
  exact ⟨Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => (h i).1,
    Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ => (h i).2⟩

/-- The bounds of four patterns, added: the two trees' main terms are at most the family's. -/
theorem combine_patterns {Mc Pr SB SM SΩ e₁ e₂ e₃ nB nW nM nR sm : ℝ} (hMc : 0 ≤ Mc) (hPr : 0 ≤ Pr)
    (hS : SB + SM ≤ SΩ) (hB : nB ≤ Mc * (SB * Pr) + sm * e₃ + sm * e₁) (hW : nW ≤ 2 * e₁)
    (hM : nM ≤ Mc * (SM * Pr) + sm * e₃ + sm * e₂) (hR : nR ≤ 2 * e₂) :
    nB + nW + nM + nR ≤ Mc * (SΩ * Pr) + 2 * sm * e₃ + (sm + 2) * e₁ + (sm + 2) * e₂ := by
  have : Mc * (SB * Pr) + Mc * (SM * Pr) ≤ Mc * (SΩ * Pr) := by
    rw [← mul_add, ← add_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hS hPr) hMc
  linarith

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

/-- **A tree pattern.** The multiples of `∏rt` with no prime factor below `z₀`, summed over a family whose products
`c = ∏_{i∈S₀} rt_i` are below `E = A + 1`: by the tree with the rule `E ≤ c∏P` (`SieveP6Tree.tree_chains`), its
leaves are at most `SieveP6TreeLeaves.tree_leaves_le`'s bound and its stops `s_max·q^{L−δ_c}/φ(q)`
(`SieveP6Tree.stops_bound`, with `ChainOK` for the window `(A, B]` and `(A + 1)z₀ ≤ B`). -/
theorem tree_pattern_le {q : ℕ} [NeZero q] {a' : ZMod q} (ha' : IsUnit a') {a b δ' εw Λ₀ Λ₁ C₀ δl δc : ℝ}
    {k J₀ J₀' K₀ Kmax A B : ℕ} (hokL : SieveP6TreeLeaves.LeavesOK q a' L a b δ' εw Λ₀ C₀ δl k J₀ Kmax)
    (hokC : SieveP6Tree.ChainOK q a' εw Λ₁ δc J₀' K₀ A B) {j : ℕ} (Ω : List (GCmp j)) (S₀ : Finset (Fin j))
    (I : ∀ s, Finset (Fin (j + s))) {z₀ smax : ℕ}
    (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hwz : ⌈(q : ℝ) ^ εw⌉₊ ≤ z₀) (hz₀ : z₀ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1)
    (hAB : (A + 1) * z₀ ≤ B) (hsmax : (A : ℝ) + 1 ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax) (hKL : j + smax ≤ Kmax)
    (hKC : j + smax ≤ K₀) (hlenL : Ω.length + smax * smax + 2 * smax + 2 ≤ J₀)
    (hlenC : Ω.length + smax * smax + 2 * smax + 2 ≤ J₀') (hΛ₁ : 0 ≤ Λ₁)
    (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) (hlz : Real.log z₀ ≤ Λ₁ * Real.log q)
    (hlE : Real.log ((A : ℝ) + 1) ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + (j + smax) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hreg : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) → StrictAnti rt ∧ ∀ i, z₀ ≤ rt i)
    (hfam : ∀ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∏ i ∈ S₀, (rt i : ℝ) < (A : ℝ) + 1)
    (hgeo : ∀ s < smax, ∀ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊
        (SieveP6Tree.leafCmps Ω S₀ ((A : ℝ) + 1) ⌈(q : ℝ) ^ εw⌉₊ z₀ s),
      (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) →
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ (I s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤
          (q : ℝ) ^ (L - b))
    (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) :
    ‖∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a' n * (if (∏ i, rt i) ∣ n ∧ rough z₀ n then 1 else 0)‖ ≤
      (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
          ((∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
            ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀, (1 + 1 / (p : ℝ))) +
        smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δl)) + smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δc)) := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hE : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  have hfam' : ∀ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∏ i ∈ S₀, (rt i : ℝ) < (A : ℝ) + 1 ∧ ∀ i, z₀ ≤ rt i :=
    fun rt hrt => ⟨hfam rt hrt, (hreg rt (fun i => (SieveTypeIIU.mem_primesLe.1
      (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hrt).1 i)).2) (Finset.mem_filter.1 hrt).2).2⟩
  rw [SieveP6Tree.tree_chains (Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊) (dw q a') Ω S₀ hE (by omega) hwz hz₀
    hfam']
  refine (norm_add_le _ _).trans ?_
  have hL := SieveP6TreeLeaves.tree_leaves_le ha' hokL Ω S₀ I hE hw2 hwz hz₀ hsmax hKL hlenL hΛ₁ hc hlz hlE hΛ hX
    hN hreg hgeo hC₀ hC hk hk1 hkC ((primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀).card + 1)
  have hS := SieveP6Tree.stops_bound hq1 a' hΛ₁ hokC Ω S₀ (by omega) (Nat.le_ceil _) hwz hAB hsmax hKC hlenC hc hlz
    hlE hreg ((primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀).card + 1)
  linarith

/-- **A tree pattern, with the sizes from the boxes.** `tree_pattern_le`, its leaves split by `Isplit S₁ eIn₁`: for a
family whose tuples have `rt_i ≤ q^{hi_i}` and `A + 1 ≤ 4q^t·∏_{i∈S₀} rt_i`, a leaf's block has `∏y < 4q^t`, so its
two blocks are at most `4q^{D₁}` and `4q^{D₂}` (`D₁ = Σ_{S₁} hi + t·[eIn₁]`, `D₂ = Σ_{S₁ᶜ} hi + t·[¬eIn₁]`), and the
sizes of `leaves_chain` hold once `4·2^{2k+4} ≤ q^{L−1−a−D₁−c}` and `64·2^{2k+4} ≤ q^{L−b−D₁−2D₂−c}`,
`c = (2k + 4)εw`. -/
theorem tree_pattern_ib {q : ℕ} [NeZero q] {a' : ZMod q} (ha' : IsUnit a') {a b δ' εw Λ₀ Λ₁ C₀ δl δc t c : ℝ}
    {k J₀ J₀' K₀ Kmax A B : ℕ} (hokL : SieveP6TreeLeaves.LeavesOK q a' L a b δ' εw Λ₀ C₀ δl k J₀ Kmax)
    (hokC : SieveP6Tree.ChainOK q a' εw Λ₁ δc J₀' K₀ A B) {j : ℕ} (Ω : List (GCmp j)) (S₀ S₁ : Finset (Fin j))
    (eIn₁ : Bool) (hi : Fin j → ℝ) {z₀ smax : ℕ}
    (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hwle : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ≤ 2 * (q : ℝ) ^ εw) (hwz : ⌈(q : ℝ) ^ εw⌉₊ ≤ z₀)
    (hz₀ : z₀ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1) (hAB : (A + 1) * z₀ ≤ B)
    (hsmax : (A : ℝ) + 1 ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax) (hKL : j + smax ≤ Kmax) (hKC : j + smax ≤ K₀)
    (hlenL : Ω.length + smax * smax + 2 * smax + 2 ≤ J₀) (hlenC : Ω.length + smax * smax + 2 * smax + 2 ≤ J₀')
    (hΛ₁ : 0 ≤ Λ₁) (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) (hlz : Real.log z₀ ≤ Λ₁ * Real.log q)
    (hlE : Real.log ((A : ℝ) + 1) ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + (j + smax) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hreg : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, z₀ ≤ rt i) ∧ (∀ i, (rt i : ℝ) ≤ (q : ℝ) ^ hi i) ∧
        (A : ℝ) + 1 ≤ 4 * (q : ℝ) ^ t * ∏ i ∈ S₀, (rt i : ℝ))
    (hfam : ∀ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∏ i ∈ S₀, (rt i : ℝ) < (A : ℝ) + 1)
    (hεwc : (2 * k + 4 : ℝ) * εw = c)
    (hsz₁ : 4 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a - (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) - c))
    (hsz₂ : 64 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - b - (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) -
      2 * (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t)) - c))
    (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) :
    ‖∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a' n * (if (∏ i, rt i) ∣ n ∧ rough z₀ n then 1 else 0)‖ ≤
      (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
          ((∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
            ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀, (1 + 1 / (p : ℝ))) +
        smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δl)) + smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δc)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hw0 : (0 : ℝ) < ⌈(q : ℝ) ^ εw⌉₊ := by exact_mod_cast (by omega : 0 < ⌈(q : ℝ) ^ εw⌉₊)
  have hz0 : (0 : ℝ) < z₀ := by exact_mod_cast (by omega : 0 < z₀)
  have hE : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  have hwpow : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ 2 ^ (2 * k + 4) * (q : ℝ) ^ c := by
    calc (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (2 * (q : ℝ) ^ εw) ^ (2 * k + 4) :=
          pow_le_pow_left₀ hw0.le hwle _
      _ = 2 ^ (2 * k + 4) * (q : ℝ) ^ c := by
          rw [mul_pow, ← Real.rpow_natCast ((q : ℝ) ^ εw), ← Real.rpow_mul hq0.le, ← hεwc]
          push_cast
          ring_nf
  refine tree_pattern_le ha' hokL hokC Ω S₀ (Isplit S₁ eIn₁) hw2 hwz hz₀ hAB hsmax hKL hKC hlenL hlenC hΛ₁ hc hlz
    hlE hΛ hX hN (fun rt hp hΩ => ⟨(hreg rt hp hΩ).1, (hreg rt hp hΩ).2.1⟩) hfam ?_ hC₀ hC hk hk1 hkC
  intro s _ x hx _
  have hx1 := SieveP6Tree.one_le_of_mem_RTg hx
  obtain ⟨hΩ1, -, halive⟩ := (SieveP6Tree.leafCmps_holds Ω S₀ hE hw0 hz0 hx1).1 (Finset.mem_filter.1 hx).2
  have hprime : ∀ i, (x i).Prime := fun i =>
    (SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx).1 i)).2
  obtain ⟨-, -, hbox, hAc⟩ := hreg _ (fun i => hprime _) hΩ1
  rw [SieveP6Tree.prod_idxAll] at halive
  have hcpos : 0 < ∏ i ∈ S₀, (x (Fin.castAdd s i) : ℝ) := Finset.prod_pos fun i _ => by exact_mod_cast hx1 _
  have hy : ∏ u, (x (Fin.natAdd j u) : ℝ) ≤ 4 * (q : ℝ) ^ t := by
    have h1 : (∏ i ∈ S₀, (x (Fin.castAdd s i) : ℝ)) * ∏ u, (x (Fin.natAdd j u) : ℝ) <
        (∏ i ∈ S₀, (x (Fin.castAdd s i) : ℝ)) * (4 * (q : ℝ) ^ t) := by
      calc _ < (A : ℝ) + 1 := halive
        _ ≤ 4 * (q : ℝ) ^ t * ∏ i ∈ S₀, (x (Fin.castAdd s i) : ℝ) := hAc
        _ = _ := by ring
    exact (lt_of_mul_lt_mul_left h1 hcpos.le).le
  obtain ⟨hI, hIc⟩ := leaf_blocks_le S₁ eIn₁ hx1 hq0 hi hbox hy
  have hqt : 0 ≤ (q : ℝ) ^ t := by positivity
  have hI' : ∏ i ∈ Isplit S₁ eIn₁ s, (x i : ℝ) ≤ 4 * (q : ℝ) ^ (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) := by
    refine hI.trans ?_
    have hS : 0 ≤ (q : ℝ) ^ (∑ i ∈ S₁, hi i) := by positivity
    cases eIn₁
    · simp only [Bool.false_eq_true, ite_false, mul_one, add_zero]
      linarith
    · simp only [ite_true]
      rw [Real.rpow_add hq0]
      linarith
  have hIc' : ∏ i ∈ (Isplit S₁ eIn₁ s)ᶜ, (x i : ℝ) ≤
      4 * (q : ℝ) ^ (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t)) := by
    refine hIc.trans ?_
    have hS : 0 ≤ (q : ℝ) ^ (∑ i ∈ S₁ᶜ, hi i) := by positivity
    cases eIn₁
    · simp only [Bool.false_eq_true, ite_false]
      rw [Real.rpow_add hq0]
      linarith
    · simp only [ite_true, mul_one, add_zero]
      linarith
  push_cast
  exact leaf_sizes_num hq0 (Finset.prod_nonneg fun i _ => Nat.cast_nonneg _) hI' hIc' hw0.le hwpow hsz₁ hsz₂

/-! ### A family in a window, of any length -/

/-- `SieveP6Tree.root_bound` for families of any length (with no tuple when there is no index). -/
theorem root_bound' {q : ℕ} (hq : 1 ≤ q) (a : ZMod q) {e₀ Λ₁ δ : ℝ} (hΛ₁ : 0 ≤ Λ₁) {J₀ K₀ A B : ℕ} (hA : 1 ≤ A)
    (hok : SieveP6Tree.ChainOK q a e₀ Λ₁ δ J₀ K₀ A B) {j : ℕ} (hj : j ≤ K₀) (S : Finset (Fin j))
    (Ω : List (GCmp j)) (hΩ : Ω.length + 2 ≤ J₀) (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) {z₀ : ℕ} (hz₀ : 1 ≤ z₀)
    (hz₀q : (q : ℝ) ^ e₀ ≤ z₀)
    (hreg : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, z₀ ≤ rt i) ∧ A < ∏ i ∈ S, rt i ∧ ∏ i ∈ S, rt i ≤ B) :
    ‖∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a n * (if (∏ i, rt i) ∣ n ∧ rough z₀ n then 1 else 0)‖ ≤
      2 * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)) := by
  cases j with
  | zero =>
    have hempty : RTg 0 ⌊2 * (q : ℝ) ^ L⌋₊ Ω = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun rt hrt => ?_
      obtain ⟨-, -, hlt, -⟩ := hreg rt (fun i => i.elim0) (Finset.mem_filter.1 hrt).2
      rw [Finset.eq_empty_of_isEmpty S, Finset.prod_empty] at hlt
      omega
    rw [hempty, Finset.sum_empty, norm_zero]
    positivity
  | succ k' => exact SieveP6Tree.root_bound hq a hΛ₁ hok (by omega) S Ω hΩ hc hz₀ hz₀q hreg

/-! ### The windows -/

/-- **The lower window's stops fit**: `(⌈x^{w₁L}⌉ + 1)⌈x^{a₀}⌉ ≤ ⌊x^{w₂L}⌋` once `128 ≤ x^{(w₂−w₁)L − a₀}`. -/
theorem win_lo [RouteOK] {x : ℝ} (hx : 1 ≤ x) {a₀ : ℝ} (ha₀ : 0 ≤ a₀) (h : 128 ≤ x ^ ((w₂ - w₁) * L - a₀)) :
    (⌈x ^ (w₁ * L)⌉₊ + 1) * ⌈x ^ a₀⌉₊ ≤ ⌊x ^ (w₂ * L)⌋₊ := by
  have hx0 : 0 < x := by linarith
  have h1 : (1 : ℝ) ≤ x ^ (w₁ * L) := Real.one_le_rpow hx (by route_num)
  have h2 : (1 : ℝ) ≤ x ^ a₀ := Real.one_le_rpow hx ha₀
  have hc1 : (⌈x ^ (w₁ * L)⌉₊ : ℝ) ≤ x ^ (w₁ * L) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hc2 : (⌈x ^ a₀⌉₊ : ℝ) ≤ x ^ a₀ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hsplit : x ^ (w₂ * L) = x ^ ((w₂ - w₁) * L - a₀) * (x ^ (w₁ * L) * x ^ a₀) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
    ring_nf
  have hprod : (1 : ℝ) ≤ x ^ (w₁ * L) * x ^ a₀ := one_le_mul_of_one_le_of_one_le h1 h2
  apply Nat.le_floor
  push_cast
  calc ((⌈x ^ (w₁ * L)⌉₊ : ℝ) + 1) * ⌈x ^ a₀⌉₊ ≤ (x ^ (w₁ * L) + 2) * (x ^ a₀ + 1) :=
        mul_le_mul (by linarith) hc2 (Nat.cast_nonneg _) (by positivity)
    _ ≤ (3 * x ^ (w₁ * L)) * (2 * x ^ a₀) := by gcongr <;> linarith
    _ = 6 * (x ^ (w₁ * L) * x ^ a₀) := by ring
    _ ≤ 128 * (x ^ (w₁ * L) * x ^ a₀) := by linarith
    _ ≤ x ^ ((w₂ - w₁) * L - a₀) * (x ^ (w₁ * L) * x ^ a₀) := by gcongr
    _ = x ^ (w₂ * L) := hsplit.symm

/-- **The reflected window**, with `W₀ = ⌈N₂/x^{w₂L}⌉` and `W₁ = ⌊N₁/⌈x^{w₁L}⌉⌋`: its stops fit,
`(W₀ + 1)⌈x^{a₀}⌉ ≤ W₁`; `W₁ ≤ N₁`; the conditions of `SieveChainR.chainTR_bound`; and `W₁ ≥ x^{L−w₁L}/8`. -/
theorem win_hi [RouteOK] {x : ℝ} (hx : 1 ≤ x) {a₀ : ℝ} (ha₀ : 0 ≤ a₀) (h : 128 ≤ x ^ ((w₂ - w₁) * L - a₀))
    (h16 : 16 ≤ x ^ (L - w₁ * L)) :
    (⌈(⌊2 * x ^ L⌋₊ : ℝ) / x ^ (w₂ * L)⌉₊ + 1) * ⌈x ^ a₀⌉₊ ≤ ⌊x ^ L⌋₊ / ⌈x ^ (w₁ * L)⌉₊ ∧
      ⌊x ^ L⌋₊ / ⌈x ^ (w₁ * L)⌉₊ ≤ ⌊x ^ L⌋₊ ∧
      x ^ (w₁ * L) ≤ ((⌊x ^ L⌋₊ / (⌊x ^ L⌋₊ / ⌈x ^ (w₁ * L)⌉₊) : ℕ) : ℝ) ∧
      ((⌊2 * x ^ L⌋₊ / (⌈(⌊2 * x ^ L⌋₊ : ℝ) / x ^ (w₂ * L)⌉₊ + 1) : ℕ) : ℝ) ≤ x ^ (w₂ * L) ∧
      x ^ (L - w₁ * L) / 8 ≤ ((⌊x ^ L⌋₊ / ⌈x ^ (w₁ * L)⌉₊ : ℕ) : ℝ) := by
  have hx0 : 0 < x := by linarith
  set N₁ := ⌊x ^ L⌋₊ with hN₁
  set N₂ := ⌊2 * x ^ L⌋₊ with hN₂
  set P₁ := ⌈x ^ (w₁ * L)⌉₊ with hP₁
  set W₀ := ⌈(N₂ : ℝ) / x ^ (w₂ * L)⌉₊ with hW₀
  set W₁ := N₁ / P₁ with hW₁
  have h1 : (1 : ℝ) ≤ x ^ (w₁ * L) := Real.one_le_rpow hx (by route_num)
  have h2 : (1 : ℝ) ≤ x ^ a₀ := Real.one_le_rpow hx ha₀
  have h3 : (1 : ℝ) ≤ x ^ (L - w₂ * L) := Real.one_le_rpow hx (by route_num)
  have hP₁r : (P₁ : ℝ) ≤ x ^ (w₁ * L) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hP₁0 : 0 < P₁ := Nat.ceil_pos.2 (by linarith)
  have hxL : x ^ L = x ^ (L - w₁ * L) * x ^ (w₁ * L) := by rw [← Real.rpow_add hx0]; ring_nf
  have hxL2 : x ^ L = x ^ (L - w₂ * L) * x ^ (w₂ * L) := by rw [← Real.rpow_add hx0]; ring_nf
  have hN₁r : x ^ L - 1 < (N₁ : ℝ) := Nat.sub_one_lt_floor _
  have hN₂r : (N₂ : ℝ) ≤ 2 * x ^ L := Nat.floor_le (by positivity)
  have hw2 : 0 < x ^ (w₂ * L) := by positivity
  -- `W₁ ≥ x^{L−w₁L}/8`
  have hW₁lo : x ^ (L - w₁ * L) / 8 ≤ (W₁ : ℝ) := by
    have hdiv : (N₁ : ℝ) < ((W₁ : ℝ) + 1) * P₁ := by
      have := Nat.lt_div_mul_add (a := N₁) hP₁0
      have h' : N₁ < (W₁ + 1) * P₁ := by rw [hW₁]; nlinarith [Nat.div_mul_le_self N₁ P₁]
      exact_mod_cast h'
    have hA : x ^ (L - w₁ * L) * x ^ (w₁ * L) - 1 < ((W₁ : ℝ) + 1) * (2 * x ^ (w₁ * L)) := by
      rw [← hxL]
      calc x ^ L - 1 < (N₁ : ℝ) := hN₁r
        _ < ((W₁ : ℝ) + 1) * P₁ := hdiv
        _ ≤ ((W₁ : ℝ) + 1) * (2 * x ^ (w₁ * L)) := by gcongr; linarith
    nlinarith
  refine ⟨?_, Nat.div_le_self _ _, ?_, ?_, hW₁lo⟩
  · -- `(W₀ + 1)z₀ ≤ W₁`
    have hW₀r : (W₀ : ℝ) ≤ (N₂ : ℝ) / x ^ (w₂ * L) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hW₀2 : (N₂ : ℝ) / x ^ (w₂ * L) ≤ 2 * x ^ (L - w₂ * L) := by
      rw [div_le_iff₀ hw2]
      calc (N₂ : ℝ) ≤ 2 * x ^ L := hN₂r
        _ = 2 * x ^ (L - w₂ * L) * x ^ (w₂ * L) := by rw [hxL2]; ring
    have hz : (⌈x ^ a₀⌉₊ : ℝ) ≤ 2 * x ^ a₀ := by
      have := (Nat.ceil_lt_add_one (show 0 ≤ x ^ a₀ by positivity)).le
      linarith
    have hsplit : x ^ (L - w₁ * L) = x ^ ((w₂ - w₁) * L - a₀) * (x ^ (L - w₂ * L) * x ^ a₀) := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      ring_nf
    have hprod : (1 : ℝ) ≤ x ^ (L - w₂ * L) * x ^ a₀ := one_le_mul_of_one_le_of_one_le h3 h2
    have hlhs : ((W₀ : ℝ) + 1) * ⌈x ^ a₀⌉₊ ≤ 16 * (x ^ (L - w₂ * L) * x ^ a₀) := by
      calc ((W₀ : ℝ) + 1) * ⌈x ^ a₀⌉₊ ≤ (4 * x ^ (L - w₂ * L)) * (2 * x ^ a₀) := by
            gcongr
            linarith
        _ = 8 * (x ^ (L - w₂ * L) * x ^ a₀) := by ring
        _ ≤ 16 * (x ^ (L - w₂ * L) * x ^ a₀) := by linarith
    have hrhs : 16 * (x ^ (L - w₂ * L) * x ^ a₀) ≤ x ^ (L - w₁ * L) / 8 := by
      rw [hsplit, le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
      nlinarith
    have : (((W₀ + 1) * ⌈x ^ a₀⌉₊ : ℕ) : ℝ) ≤ W₁ := by push_cast; linarith
    exact_mod_cast this
  · -- `x^{w₁L} ≤ ⌊N₁/W₁⌋`
    have hW₁0 : 0 < W₁ := by
      have : (0 : ℝ) < W₁ := lt_of_lt_of_le (by positivity) hW₁lo
      exact_mod_cast this
    have : P₁ ≤ N₁ / W₁ := (Nat.le_div_iff_mul_le hW₁0).2 (by rw [hW₁, mul_comm]; exact Nat.div_mul_le_self N₁ P₁)
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast this)
  · -- `⌊N₂/(W₀ + 1)⌋ ≤ x^{w₂L}`
    have hW₀ge : (N₂ : ℝ) / x ^ (w₂ * L) ≤ W₀ := Nat.le_ceil _
    have hpos : (0 : ℝ) < (W₀ : ℝ) + 1 := by positivity
    calc ((N₂ / (W₀ + 1) : ℕ) : ℝ) ≤ (N₂ : ℝ) / ((W₀ : ℝ) + 1) := by
          have := Nat.cast_div_le (α := ℝ) (m := N₂) (n := W₀ + 1)
          push_cast at this
          exact this
      _ ≤ (N₂ : ℝ) / ((N₂ : ℝ) / x ^ (w₂ * L)) := by
          rcases Nat.eq_zero_or_pos N₂ with h0 | h0
          · rw [h0]; simp
          · have : (0 : ℝ) < (N₂ : ℝ) / x ^ (w₂ * L) := by positivity
            exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) this (by linarith)
      _ ≤ x ^ (w₂ * L) := by
          rcases Nat.eq_zero_or_pos N₂ with h0 | h0
          · rw [h0]; simp; positivity
          · rw [div_div_cancel₀ (by positivity)]

/-- **Below the window, a leaf's block is small**: `⌈Q^{w₁L}⌉ + 1 ≤ 4Q^t·c` once `Q^s ≤ c` and `w₁L − s ≤ t`. -/
theorem alive_lo [RouteOK] {Q : ℝ} (hQ : 1 ≤ Q) {t s c : ℝ} (hc : Q ^ s ≤ c) (hlo : w₁ * L - s ≤ t) :
    (⌈Q ^ (w₁ * L)⌉₊ : ℝ) + 1 ≤ 4 * Q ^ t * c := by
  have hQ0 : 0 < Q := by linarith
  have h1 : (1 : ℝ) ≤ Q ^ (w₁ * L) := Real.one_le_rpow hQ (by route_num)
  have hP : (⌈Q ^ (w₁ * L)⌉₊ : ℝ) ≤ Q ^ (w₁ * L) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have h2 : Q ^ (w₁ * L) ≤ Q ^ t * c :=
    calc Q ^ (w₁ * L) ≤ Q ^ (t + s) := Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
      _ = Q ^ t * Q ^ s := Real.rpow_add hQ0 _ _
      _ ≤ Q ^ t * c := mul_le_mul_of_nonneg_left hc (by positivity)
  linarith

/-- `⌈N₂/Q^{w₂L}⌉ + 1 ≤ 4Q^{L−w₂L}` once `N₂ ≤ 2Q^L`. -/
theorem W₀_le [RouteOK] {Q : ℝ} (hQ : 1 ≤ Q) {N₂ : ℕ} (hN₂ : (N₂ : ℝ) ≤ 2 * Q ^ L) :
    (⌈(N₂ : ℝ) / Q ^ (w₂ * L)⌉₊ : ℝ) + 1 ≤ 4 * Q ^ (L - w₂ * L) := by
  have hQ0 : 0 < Q := by linarith
  have hw2 : 0 < Q ^ (w₂ * L) := by positivity
  have h3 : (1 : ℝ) ≤ Q ^ (L - w₂ * L) := Real.one_le_rpow hQ (by route_num)
  have hW : (⌈(N₂ : ℝ) / Q ^ (w₂ * L)⌉₊ : ℝ) ≤ (N₂ : ℝ) / Q ^ (w₂ * L) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hxL2 : Q ^ L = Q ^ (L - w₂ * L) * Q ^ (w₂ * L) := by rw [← Real.rpow_add hQ0]; ring_nf
  have hdiv : (N₂ : ℝ) / Q ^ (w₂ * L) ≤ 2 * Q ^ (L - w₂ * L) := by
    rw [div_le_iff₀ hw2]
    calc (N₂ : ℝ) ≤ 2 * Q ^ L := hN₂
      _ = 2 * Q ^ (L - w₂ * L) * Q ^ (w₂ * L) := by rw [hxL2]; ring
  linarith

/-- **Between the windows, a leaf's block is small**: `⌈N₂/Q^{w₂L}⌉ + 1 ≤ 4Q^t·c` once `Q^{w₂L} < c`, `Q^s ≤ c` and
`L − w₂L − max(w₂L, s) ≤ t`. -/
theorem alive_mid [RouteOK] {Q : ℝ} (hQ : 1 ≤ Q) {t s c : ℝ} {N₂ : ℕ} (hN₂ : (N₂ : ℝ) ≤ 2 * Q ^ L)
    (hc₁ : Q ^ (w₂ * L) < c) (hc₂ : Q ^ s ≤ c) (hmid : L - w₂ * L - max (w₂ * L) s ≤ t) :
    (⌈(N₂ : ℝ) / Q ^ (w₂ * L)⌉₊ : ℝ) + 1 ≤ 4 * Q ^ t * c := by
  have hQ0 : 0 < Q := by linarith
  have hmax : Q ^ (max (w₂ * L) s) ≤ c := by
    rcases le_total (w₂ * L) s with h | h
    · rw [max_eq_right h]; exact hc₂
    · rw [max_eq_left h]; exact hc₁.le
  have h2 : Q ^ (L - w₂ * L) ≤ Q ^ t * c :=
    calc Q ^ (L - w₂ * L) ≤ Q ^ (t + max (w₂ * L) s) := Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
      _ = Q ^ t * Q ^ (max (w₂ * L) s) := Real.rpow_add hQ0 _ _
      _ ≤ Q ^ t * c := mul_le_mul_of_nonneg_left hmax (by positivity)
  linarith [W₀_le hQ hN₂]

/-! ### Proposition 6 with the bilinear estimate, for given windows -/

set_option maxHeartbeats 1600000 in
/-- **Proposition 6 with the bilinear estimate, at one `q`, for given windows.** The family split into its five
patterns by `c = ∏_{i∈S₀} rt_i` against the windows `(P₁, P₂]` and `(W₀, W₁]`: below the first (a tree,
`tree_pattern_ib` with `ChainOK` there, its blocks small by `hB`), in it (`root_bound'`), between the two (a tree,
`tree_pattern_ib` with `ChainOK` there, its blocks small by `hM`), in the second (`root_bound'`), and above it (empty,
by `hA`). -/
theorem prop6ib_core {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {j : ℕ} (Ω : List (GCmp j))
    (S₀ S₁ : Finset (Fin j)) (eIn₁ : Bool) (lo hi : Fin j → ℝ) {t aL bL δ' εw c Λ₀ Λ₁ C₀ δ₁ δ₂ δ₃ : ℝ}
    {k J₀C K₀ Kmax smax P₁ P₂ W₀ W₁ z₀ : ℕ}
    (hokL : SieveP6TreeLeaves.LeavesOK q a L aL bL δ' εw Λ₀ C₀ δ₃ k J₀C Kmax)
    (hokTL : SieveP6Tree.ChainOK q a εw Λ₁ δ₁ J₀C K₀ P₁ P₂) (hokTR : SieveP6Tree.ChainOK q a εw Λ₁ δ₂ J₀C K₀ W₀ W₁)
    (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hwle : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ≤ 2 * (q : ℝ) ^ εw) (hwz : ⌈(q : ℝ) ^ εw⌉₊ ≤ z₀)
    (hz₀ : z₀ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1) (hz₀q : (q : ℝ) ^ εw ≤ z₀) (hΛ₁ : 0 ≤ Λ₁)
    (hlz : Real.log z₀ ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + (j + smax) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hJ : Ω.length + 4 + smax * smax + 2 * smax + 2 ≤ J₀C) (hK : j + smax + 1 ≤ K₀) (hKm : j + smax ≤ Kmax)
    (hP₁ : 1 ≤ P₁) (hP₂ : 1 ≤ P₂) (hW₀ : 1 ≤ W₀) (hW₁ : 1 ≤ W₁) (hAB₁ : (P₁ + 1) * z₀ ≤ P₂)
    (hAB₂ : (W₀ + 1) * z₀ ≤ W₁) (hsm₁ : (P₁ : ℝ) + 1 ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax)
    (hsm₂ : (W₀ : ℝ) + 1 ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax) (hl₁ : Real.log ((P₁ : ℝ) + 1) ≤ Λ₁ * Real.log q)
    (hl₂ : Real.log (P₂ : ℝ) ≤ Λ₁ * Real.log q) (hl₃ : Real.log ((W₀ : ℝ) + 1) ≤ Λ₁ * Real.log q)
    (hl₄ : Real.log (W₁ : ℝ) ≤ Λ₁ * Real.log q)
    (hB : ∀ s : ℝ, (q : ℝ) ^ (∑ i ∈ S₀, lo i) ≤ s → (P₁ : ℝ) + 1 ≤ 4 * (q : ℝ) ^ t * s)
    (hM : ∀ s : ℝ, (q : ℝ) ^ (∑ i ∈ S₀, lo i) ≤ s → s ≤ (q : ℝ) ^ (∑ i ∈ S₀, hi i) → (P₂ : ℝ) + 1 ≤ s →
      (W₀ : ℝ) + 1 ≤ 4 * (q : ℝ) ^ t * s)
    (hA : (q : ℝ) ^ (∑ i ∈ S₀, hi i) ≤ W₁) (hεwc : (2 * k + 4 : ℝ) * εw = c)
    (hsz₁ : 4 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - aL - (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) - c))
    (hsz₂ : 64 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - bL - (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) -
      2 * (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t)) - c))
    (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) (hΩc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q)
    (hΩ : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, z₀ ≤ rt i) ∧ ∀ i, (q : ℝ) ^ lo i ≤ rt i ∧ (rt i : ℝ) ≤ (q : ℝ) ^ hi i) :
    ‖∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a n * (if (∏ i, rt i) ∣ n ∧ rough z₀ n then 1 else 0)‖ ≤
      (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
          ((∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
            ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀, (1 + 1 / (p : ℝ))) +
        2 * smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₃)) +
        (smax + 2) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₁)) +
        (smax + 2) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₂)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqn : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hP₁0 : (0 : ℝ) < P₁ := by exact_mod_cast hP₁
  have hP₂0 : (0 : ℝ) < P₂ := by exact_mod_cast hP₂
  have hW₀0 : (0 : ℝ) < W₀ := by exact_mod_cast hW₀
  have hW₁0 : (0 : ℝ) < W₁ := by exact_mod_cast hW₁
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hqn)
  have hd : ∀ b : ℝ, 1 ≤ b → -Real.log b ≤ Λ₁ * Real.log q := fun b hb => by
    have := Real.log_nonneg hb
    have := mul_nonneg hΛ₁ hlogq
    linarith
  have hlP₁ : Real.log (P₁ : ℝ) ≤ Λ₁ * Real.log q := (Real.log_le_log hP₁0 (by linarith)).trans hl₁
  have hlW₀ : Real.log (W₀ : ℝ) ≤ Λ₁ * Real.log q := (Real.log_le_log hW₀0 (by linarith)).trans hl₃
  obtain ⟨hcB, hcW, hcM, hcR⟩ := pat_c_le (Ω := Ω) (S₀ := S₀) hΩc hlP₁ hl₂ hlW₀ hl₄ hd (by exact_mod_cast hP₁)
    (by exact_mod_cast hP₂) (by exact_mod_cast hW₀)
  have hprime : ∀ {Ω' : List (GCmp j)} {rt : Fin j → ℕ}, rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω' → ∀ i, (rt i).Prime :=
    fun hrt i => (SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hrt).1 i)).2
  -- the pattern above the windows is empty
  have hAe : RTg j ⌊2 * (q : ℝ) ^ L⌋₊ (patA Ω S₀ P₁ P₂ W₀ W₁) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun rt hrt => ?_
    have hh := (Finset.mem_filter.1 hrt).2
    have hlt := (pat_holds (Ω := Ω) (S₀ := S₀) (SieveP6Tree.one_le_of_mem_RTg hrt) hP₁0 hP₂0 hW₀0 hW₁0).2.2.2.2 hh
    simp only [patA, forall_append_singleton] at hh
    have := (box_prod hq0 S₀ (hΩ rt (hprime hrt) hh.1.1.1.1).2.2).2
    linarith
  rw [sum_patterns Ω S₀ hP₁0 hP₂0 hW₀0 hW₁0 (fun rt => ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
    dw q a n * (if (∏ i, rt i) ∣ n ∧ rough z₀ n then 1 else 0)), hAe, Finset.sum_empty, add_zero]
  -- below the window: a tree
  have hBb := tree_pattern_ib ha hokL hokTL (patB Ω S₀ P₁) S₀ S₁ eIn₁ hi hw2 hwle hwz hz₀ hAB₁ hsm₁ hKm
    (by omega) (by rw [length_patB]; omega) (by rw [length_patB]; omega) hΛ₁ hcB hlz hl₁ hΛ hX hN
    (fun rt hp hh => by
      obtain ⟨hΩ', -⟩ := (pat_holds (Ω := Ω) (S₀ := S₀) (W₁ := (W₁ : ℝ)) (fun i => (hp i).one_lt.le) hP₁0 hP₂0
        hW₀0 hW₁0).1 hh
      obtain ⟨hsa, hz, hb⟩ := hΩ rt hp hΩ'
      exact ⟨hsa, hz, fun i => (hb i).2, hB _ (box_prod hq0 S₀ hb).1⟩)
    (fun rt hrt => by
      have := ((pat_holds (Ω := Ω) (S₀ := S₀) (W₁ := (W₁ : ℝ)) (SieveP6Tree.one_le_of_mem_RTg hrt) hP₁0 hP₂0 hW₀0
        hW₁0).1 (Finset.mem_filter.1 hrt).2).2
      linarith)
    hεwc hsz₁ hsz₂ hC₀ hC hk hk1 hkC
  -- in the window
  have hWb := root_bound' hqn a hΛ₁ hP₁ hokTL (by omega) S₀ (patW Ω S₀ P₁ P₂) (by rw [length_patW]; omega) hcW
    (by omega) hz₀q (fun rt hp hh => by
      obtain ⟨hΩ', hlt, hle⟩ := (pat_holds (Ω := Ω) (S₀ := S₀) (W₀ := (W₀ : ℝ)) (W₁ := (W₁ : ℝ))
        (fun i => (hp i).one_lt.le) hP₁0 hP₂0 hW₀0 hW₁0).2.1 hh
      obtain ⟨hsa, hz, -⟩ := hΩ rt hp hΩ'
      exact ⟨hsa, hz, by exact_mod_cast hlt, by exact_mod_cast hle⟩)
  -- between the windows: a tree
  have hMb := tree_pattern_ib ha hokL hokTR (patM Ω S₀ P₁ P₂ W₀) S₀ S₁ eIn₁ hi hw2 hwle hwz hz₀ hAB₂ hsm₂ hKm
    (by omega) (by rw [length_patM]; omega) (by rw [length_patM]; omega) hΛ₁ hcM hlz hl₃ hΛ hX hN
    (fun rt hp hh => by
      obtain ⟨hΩ', hlt, -⟩ := (pat_holds (Ω := Ω) (S₀ := S₀) (W₁ := (W₁ : ℝ)) (fun i => (hp i).one_lt.le) hP₁0
        hP₂0 hW₀0 hW₁0).2.2.1 hh
      obtain ⟨hsa, hz, hb⟩ := hΩ rt hp hΩ'
      obtain ⟨hl, hu⟩ := box_prod hq0 S₀ hb
      have h1 : P₂ + 1 ≤ ∏ i ∈ S₀, rt i := by exact_mod_cast hlt
      have h2 : (P₂ : ℝ) + 1 ≤ ∏ i ∈ S₀, (rt i : ℝ) := by exact_mod_cast h1
      exact ⟨hsa, hz, fun i => (hb i).2, hM _ hl hu h2⟩)
    (fun rt hrt => by
      have := ((pat_holds (Ω := Ω) (S₀ := S₀) (W₁ := (W₁ : ℝ)) (SieveP6Tree.one_le_of_mem_RTg hrt) hP₁0 hP₂0 hW₀0
        hW₁0).2.2.1 (Finset.mem_filter.1 hrt).2).2.2
      linarith)
    hεwc hsz₁ hsz₂ hC₀ hC hk hk1 hkC
  -- in the reflected window
  have hRb := root_bound' hqn a hΛ₁ hW₀ hokTR (by omega) S₀ (patR Ω S₀ P₁ P₂ W₀ W₁) (by rw [length_patR]; omega)
    hcR (by omega) hz₀q (fun rt hp hh => by
      obtain ⟨hΩ', hlt, hle⟩ := (pat_holds (Ω := Ω) (S₀ := S₀) (fun i => (hp i).one_lt.le) hP₁0 hP₂0 hW₀0
        hW₁0).2.2.2.1 hh
      obtain ⟨hsa, hz, -⟩ := hΩ rt hp hΩ'
      exact ⟨hsa, hz, by exact_mod_cast hlt, by exact_mod_cast hle⟩)
  -- the trees' families are parts of the family
  have hS := sum_patterns Ω S₀ hP₁0 hP₂0 hW₀0 hW₁0 (Y := ⌊2 * (q : ℝ) ^ L⌋₊) (fun rt => 1 / ((∏ i, rt i : ℕ) : ℝ))
  have hnn : ∀ Ω' : List (GCmp j), 0 ≤ ∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω', 1 / ((∏ i, rt i : ℕ) : ℝ) :=
    fun Ω' => Finset.sum_nonneg fun rt _ => by positivity
  have hSle : (∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ (patB Ω S₀ P₁), 1 / ((∏ i, rt i : ℕ) : ℝ)) +
      ∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ (patM Ω S₀ P₁ P₂ W₀), 1 / ((∏ i, rt i : ℕ) : ℝ) ≤
      ∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ) := by
    rw [hS]
    linarith [hnn (patW Ω S₀ P₁ P₂), hnn (patR Ω S₀ P₁ P₂ W₀ W₁), hnn (patA Ω S₀ P₁ P₂ W₀ W₁)]
  have hMc : 0 ≤ 2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ') := by
    have hN' : (0 : ℝ) ≤ (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊ := by
      have : (⌊(q : ℝ) ^ L⌋₊ : ℝ) ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := by exact_mod_cast hN
      linarith
    have hlw : 0 ≤ Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := Real.log_nonneg (Nat.one_le_cast.2 (by omega))
    exact add_nonneg (mul_nonneg (mul_nonneg zero_le_two (SieveProp6.zeta_nonneg hC₀ k))
      (div_nonneg hN' (mul_nonneg (Nat.cast_nonneg _) hlw)))
      (mul_nonneg (mul_nonneg zero_le_two (SieveProp6.rem_nonneg _ _ k)) (Real.rpow_nonneg hq0.le _))
  have hPr : 0 ≤ ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀, (1 + 1 / (p : ℝ)) :=
    Finset.prod_nonneg fun p _ => by positivity
  exact norm_add₄_le.trans (combine_patterns hMc hPr hSle hBb hWb hMb hRb)

/-! ### Proposition 6 with the bilinear estimate, at one `q` -/

set_option maxHeartbeats 1600000 in
/-- **Proposition 6 with the bilinear estimate, at one `q`.** The family split into its five patterns by
`c = ∏_{i∈S₀} rt_i`: below the window `(P₁, P₂]` (a tree, `tree_pattern_ib` with `ChainOK` there), in it
(`root_bound'`), between it and the reflected window `(W₀, W₁]` (a tree, `tree_pattern_ib` with `ChainOK` there), in
the reflection (`root_bound'`), and above it (empty). -/
theorem prop6ib_at [RouteOK] {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {j : ℕ} (Ω : List (GCmp j))
    (S₀ S₁ : Finset (Fin j)) (eIn₁ : Bool) (lo hi : Fin j → ℝ) {t a₀ aL bL δ' εw c Λ₀ Λ₁ C₀ δ₁ δ₂ δ₃ : ℝ}
    {k J₀C K₀ Kmax smax : ℕ}
    (hokL : SieveP6TreeLeaves.LeavesOK q a L aL bL δ' εw Λ₀ C₀ δ₃ k J₀C Kmax)
    (hokTL : SieveP6Tree.ChainOK q a εw Λ₁ δ₁ J₀C K₀ ⌈(q : ℝ) ^ (w₁ * L)⌉₊ ⌊(q : ℝ) ^ (w₂ * L)⌋₊)
    (hokTR : SieveP6Tree.ChainOK q a εw Λ₁ δ₂ J₀C K₀ ⌈(⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) / (q : ℝ) ^ (w₂ * L)⌉₊
      (⌊(q : ℝ) ^ L⌋₊ / ⌈(q : ℝ) ^ (w₁ * L)⌉₊))
    (hx3 : (3 : ℝ) ≤ q) (hxw : 2 ≤ (q : ℝ) ^ εw) (hεwa : εw ≤ a₀) (ha₀ : 0 < a₀)
    (ha₀L : a₀ ≤ L) (h128 : 128 ≤ (q : ℝ) ^ ((w₂ - w₁) * L - a₀)) (h16 : 16 ≤ (q : ℝ) ^ (L - w₁ * L))
    (h8 : 8 ≤ (q : ℝ) ^ (L - w₁ * L - ∑ i ∈ S₀, hi i)) (hsm : L + 2 ≤ εw * smax) (hΛ₁L : L + 2 ≤ Λ₁)
    (hΛ₀ : Λ₁ + (j + smax) * (L + 1) ≤ Λ₀) (hδ'L : δ' ≤ L - 1)
    (hJ : Ω.length + 4 + smax * smax + 2 * smax + 2 ≤ J₀C) (hK : j + smax + 1 ≤ K₀) (hKm : j + smax ≤ Kmax)
    (hlo : w₁ * L - ∑ i ∈ S₀, lo i ≤ t)
    (hmid : w₂ * L < ∑ i ∈ S₀, hi i → L - w₂ * L - max (w₂ * L) (∑ i ∈ S₀, lo i) ≤ t)
    (hεwc : (2 * k + 4 : ℝ) * εw = c)
    (hsz₁ : 4 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - aL - (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) - c))
    (hsz₂ : 64 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - bL - (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) -
      2 * (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t)) - c))
    (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) (hΩc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q)
    (hΩ : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, ⌈(q : ℝ) ^ a₀⌉₊ ≤ rt i) ∧ ∀ i, (q : ℝ) ^ lo i ≤ rt i ∧ (rt i : ℝ) ≤ (q : ℝ) ^ hi i) :
    ‖∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a n * (if (∏ i, rt i) ∣ n ∧ rough ⌈(q : ℝ) ^ a₀⌉₊ n then 1 else 0)‖ ≤
      (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
          ((∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
            ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ ⌈(q : ℝ) ^ a₀⌉₊, (1 + 1 / (p : ℝ))) +
        2 * smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₃)) +
        (smax + 2) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₁)) +
        (smax + 2) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₂)) := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hq1' : (1 : ℝ) < q := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos hq1'
  have hxL1 : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow hq1 L_pos.le
  have hΛ₁0 : 0 ≤ Λ₁ := by linarith [L_pos]
  -- sizes against `x^{Λ₁}` and `w^{s_max}`
  have h4L : 4 * (q : ℝ) ^ L ≤ (q : ℝ) ^ (L + 2) := by
    have h9 : (4 : ℝ) ≤ (q : ℝ) ^ (2 : ℝ) := by rw [Real.rpow_two]; nlinarith
    calc 4 * (q : ℝ) ^ L ≤ (q : ℝ) ^ (2 : ℝ) * (q : ℝ) ^ L := mul_le_mul_of_nonneg_right h9 (by positivity)
      _ = (q : ℝ) ^ (L + 2) := by rw [Real.rpow_add hq0]; ring
  have hlogA : ∀ A : ℝ, 0 < A → A ≤ 4 * (q : ℝ) ^ L → Real.log A ≤ Λ₁ * Real.log q := fun A hA h => by
    rw [← Real.log_rpow hq0]
    exact Real.log_le_log hA (h.trans (h4L.trans (Real.rpow_le_rpow_of_exponent_le hq1 hΛ₁L)))
  have hw : (q : ℝ) ^ εw ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := Nat.le_ceil _
  have hsmA : ∀ A : ℝ, A ≤ 4 * (q : ℝ) ^ L → A ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax := fun A h =>
    calc A ≤ (q : ℝ) ^ (L + 2) := h.trans h4L
      _ ≤ (q : ℝ) ^ (εw * smax) := Real.rpow_le_rpow_of_exponent_le hq1 hsm
      _ = ((q : ℝ) ^ εw) ^ smax := by rw [Real.rpow_mul hq0.le, Real.rpow_natCast]
      _ ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax := pow_le_pow_left₀ (by positivity) hw _
  -- `w` and `z₀`
  have hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊ := by
    have : (2 : ℝ) ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := hxw.trans hw
    exact_mod_cast this
  have hwle : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ≤ 2 * (q : ℝ) ^ εw := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (q : ℝ) ^ εw by positivity)
    linarith
  have hza : (q : ℝ) ^ εw ≤ (q : ℝ) ^ a₀ := Real.rpow_le_rpow_of_exponent_le hq1 hεwa
  have hwz : ⌈(q : ℝ) ^ εw⌉₊ ≤ ⌈(q : ℝ) ^ a₀⌉₊ := Nat.ceil_mono hza
  have hz0r : (⌈(q : ℝ) ^ a₀⌉₊ : ℝ) < (q : ℝ) ^ a₀ + 1 := Nat.ceil_lt_add_one (by positivity)
  have haL : (q : ℝ) ^ a₀ ≤ (q : ℝ) ^ L := Real.rpow_le_rpow_of_exponent_le hq1 ha₀L
  have hz₀ : ⌈(q : ℝ) ^ a₀⌉₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1 :=
    (Nat.ceil_mono (by linarith : (q : ℝ) ^ a₀ ≤ 2 * (q : ℝ) ^ L)).trans (Nat.ceil_le_floor_add_one _)
  have hz₀q : (q : ℝ) ^ εw ≤ (⌈(q : ℝ) ^ a₀⌉₊ : ℝ) := hza.trans (Nat.le_ceil _)
  have hz1 : (0 : ℝ) < (⌈(q : ℝ) ^ a₀⌉₊ : ℝ) := zero_lt_one.trans_le (Nat.one_le_cast.2 (by omega))
  have hlz := hlogA _ hz1 (by linarith)
  -- `N₁` and `N₂`
  have hN₂r : (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) ≤ 2 * (q : ℝ) ^ L := Nat.floor_le (by positivity)
  have hN₂1 : 1 ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hN₂0 : (0 : ℝ) < ⌊2 * (q : ℝ) ^ L⌋₊ := zero_lt_one.trans_le (Nat.one_le_cast.2 hN₂1)
  have hN₁r : (⌊(q : ℝ) ^ L⌋₊ : ℝ) ≤ (q : ℝ) ^ L := Nat.floor_le (by positivity)
  have hΛ : Λ₁ * Real.log q + (j + smax) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q := by
    have hlN : Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ (L + 1) * Real.log q := by
      rw [← Real.log_rpow hq0]
      refine Real.log_le_log hN₂0 (hN₂r.trans ?_)
      calc 2 * (q : ℝ) ^ L ≤ (q : ℝ) * (q : ℝ) ^ L := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = (q : ℝ) ^ (L + 1) := by rw [Real.rpow_add hq0, Real.rpow_one]; ring
    have h1 := mul_le_mul_of_nonneg_left hlN (by positivity : (0 : ℝ) ≤ (j : ℝ) + smax)
    have h2 := mul_le_mul_of_nonneg_right hΛ₀ hlogq.le
    linarith
  have hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ') := Real.one_le_rpow hq1 (by linarith)
  have hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := Nat.floor_mono (by linarith)
  -- the windows
  have hAB₁ := win_lo hq1 ha₀.le h128
  obtain ⟨hAB₂, hW₁N, -, -, hW₁lo⟩ := win_hi hq1 ha₀.le h128 h16
  have hw₁1 : (1 : ℝ) ≤ (q : ℝ) ^ (w₁ * L) := Real.one_le_rpow hq1 (by route_num)
  have hw₂1 : (1 : ℝ) ≤ (q : ℝ) ^ (w₂ * L) := Real.one_le_rpow hq1 (by route_num)
  have hw₁L : (q : ℝ) ^ (w₁ * L) ≤ (q : ℝ) ^ L := Real.rpow_le_rpow_of_exponent_le hq1 (by route_num)
  have hw₂L : (q : ℝ) ^ (w₂ * L) ≤ (q : ℝ) ^ L := Real.rpow_le_rpow_of_exponent_le hq1 (by route_num)
  have hLw₂ : (q : ℝ) ^ (L - w₂ * L) ≤ (q : ℝ) ^ L := Real.rpow_le_rpow_of_exponent_le hq1 (by route_num)
  have hP₁r : (⌈(q : ℝ) ^ (w₁ * L)⌉₊ : ℝ) < (q : ℝ) ^ (w₁ * L) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hP₂r : (⌊(q : ℝ) ^ (w₂ * L)⌋₊ : ℝ) ≤ (q : ℝ) ^ (w₂ * L) := Nat.floor_le (by positivity)
  have hW₀4 := W₀_le hq1 hN₂r
  have hW₁r : ((⌊(q : ℝ) ^ L⌋₊ / ⌈(q : ℝ) ^ (w₁ * L)⌉₊ : ℕ) : ℝ) ≤ (q : ℝ) ^ L :=
    (Nat.cast_le.2 hW₁N).trans hN₁r
  have hW₁2 : (2 : ℝ) ≤ ((⌊(q : ℝ) ^ L⌋₊ / ⌈(q : ℝ) ^ (w₁ * L)⌉₊ : ℕ) : ℝ) := by linarith
  have hP₁1 : 1 ≤ ⌈(q : ℝ) ^ (w₁ * L)⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hP₂1 : 1 ≤ ⌊(q : ℝ) ^ (w₂ * L)⌋₊ := Nat.le_floor (by exact_mod_cast hw₂1)
  have hW₀1 : 1 ≤ ⌈(⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) / (q : ℝ) ^ (w₂ * L)⌉₊ :=
    Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (div_pos hN₂0 (by positivity))).ne'
  have hW₁1 : 1 ≤ ⌊(q : ℝ) ^ L⌋₊ / ⌈(q : ℝ) ^ (w₁ * L)⌉₊ := by
    have : (1 : ℝ) ≤ ((⌊(q : ℝ) ^ L⌋₊ / ⌈(q : ℝ) ^ (w₁ * L)⌉₊ : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  -- above the reflected window: `c ≤ x^{Σ_{S₀} hi} ≤ x^{L−w₁L}/8 ≤ W₁`
  have hA : (q : ℝ) ^ (∑ i ∈ S₀, hi i) ≤ ((⌊(q : ℝ) ^ L⌋₊ / ⌈(q : ℝ) ^ (w₁ * L)⌉₊ : ℕ) : ℝ) := by
    have he : (q : ℝ) ^ (L - w₁ * L) =
        (q : ℝ) ^ (L - w₁ * L - ∑ i ∈ S₀, hi i) * (q : ℝ) ^ (∑ i ∈ S₀, hi i) := by
      rw [← Real.rpow_add hq0]; congr 1; ring
    have := mul_le_mul_of_nonneg_right h8 (Real.rpow_nonneg hq0.le (∑ i ∈ S₀, hi i))
    linarith
  refine prop6ib_core ha Ω S₀ S₁ eIn₁ lo hi hokL hokTL hokTR hw2 hwle hwz hz₀ hz₀q hΛ₁0 hlz hΛ hX hN hJ hK hKm
    hP₁1 hP₂1 hW₀1 hW₁1 hAB₁ hAB₂ (hsmA _ (by linarith)) (hsmA _ (by linarith))
    (hlogA _ (by positivity) (by linarith)) (hlogA _ (zero_lt_one.trans_le (Nat.one_le_cast.2 hP₂1)) (by linarith))
    (hlogA _ (by positivity) (by linarith)) (hlogA _ (by linarith) (by linarith))
    (fun s hs => alive_lo hq1 hs hlo) (fun s hl hu hP => ?_) hA hεwc hsz₁ hsz₂ hC₀ hC hk hk1 hkC hΩc hΩ
  -- between the windows: `c > x^{w₂L}`, so `w₂L < Σ_{S₀} hi` and `hmid` applies
  have h1 : (q : ℝ) ^ (w₂ * L) < s := (Nat.lt_floor_add_one _).trans_le hP
  exact alive_mid hq1 hN₂r h1 hl (hmid ((Real.rpow_lt_rpow_left_iff hq1').1 (h1.trans_le hu)))

/-! ### Proposition 6 with the bilinear estimate -/

set_option maxHeartbeats 1600000 in
/-- **Proposition 6 with the bilinear estimate.** Assume `RouteOK` and the route's Type II estimate (`hII`). Fix `j`,
`J₀`, `Λ₁ ≥ 0`, the exponent `0 < a₀ < (w₂ − w₁)L` of `z₀ = ⌈q^{a₀}⌉`, boxes `[q^{lo_i}, q^{hi_i}]` for the tuples'
entries, a subset `S₀` whose product `c` meets the windows, a leaf split `(S₁, eIn₁)`, a growth `t` and `η > 0`, with
`w₁L − Σ_{S₀} lo ≤ t`, `w₂L < Σ_{S₀} hi → L − w₂L − max(w₂L, Σ_{S₀} lo) ≤ t`, `Σ_{S₀} hi < L − w₁L`, `D₁ < L − 1` and
`D₁ + 2D₂ < L`, where `D₁ = Σ_{S₁} hi + t·[eIn₁]` and `D₂ = Σ_{S₁ᶜ} hi + t·[¬eIn₁]`. There are `δ > 0` and `q₀` such
that for `q ≥ q₀` and a unit `a` mod `q`: let `rt` run over the `j`-tuples of primes up to `⌊2q^L⌋` that satisfy at
most `J₀` comparisons `Ω` (taken at `m = 0`, with `m`-parts `c(0)` at most `Λ₁ log q`) forcing `rt` strictly
decreasing, every `rt_i ≥ z₀` and `q^{lo_i} ≤ rt_i ≤ q^{hi_i}`. Then `Σ_{rt}(S(A_r, z₀) − S(B_r, z₀)/φ(q))`,
`r = ∏rt`, is at most `η q^L/(φ(q) log q) + q^{L−δ}/φ(q)` in absolute value. -/
theorem prop6ib [RouteOK] (hII : TypeIIAt) (j J₀ : ℕ) {Λ₁ a₀ : ℝ} (hΛ₁ : 0 ≤ Λ₁) (ha₀ : 0 < a₀)
    (ha₀W : a₀ < (w₂ - w₁) * L) (lo hi : Fin j → ℝ) (S₀ S₁ : Finset (Fin j)) (eIn₁ : Bool) {t : ℝ}
    (hlo : w₁ * L - ∑ i ∈ S₀, lo i ≤ t)
    (hmid : w₂ * L < ∑ i ∈ S₀, hi i → L - w₂ * L - max (w₂ * L) (∑ i ∈ S₀, lo i) ≤ t)
    (hhi : ∑ i ∈ S₀, hi i < L - w₁ * L) (hD₁ : ∑ i ∈ S₁, hi i + (if eIn₁ then t else 0) < L - 1)
    (hD₂ : ∑ i ∈ S₁, hi i + (if eIn₁ then t else 0) + 2 * (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t)) < L)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ Ω : List (GCmp j), Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      (∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
        StrictAnti rt ∧ (∀ i, ⌈(q : ℝ) ^ a₀⌉₊ ≤ rt i) ∧ ∀ i, (q : ℝ) ^ lo i ≤ rt i ∧ (rt i : ℝ) ≤ (q : ℝ) ^ hi i) →
      ‖∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
          dw q a n * (if (∏ i, rt i) ∣ n ∧ rough ⌈(q : ℝ) ^ a₀⌉₊ n then 1 else 0)‖ ≤
        η * (q : ℝ) ^ L / (q.totient * Real.log q) + (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  have hL2 := two_lt_L
  obtain ⟨C₀, hC₀1, hC⟩ := SieveRanges.rng_sum_le
  have hC₀ : 0 ≤ C₀ := by linarith
  -- the leaves' two blocks, and their margins
  obtain ⟨D₁, hD₁def⟩ : ∃ D₁ : ℝ, D₁ = ∑ i ∈ S₁, hi i + (if eIn₁ then t else 0) := ⟨_, rfl⟩
  obtain ⟨D₂, hD₂def⟩ : ∃ D₂ : ℝ, D₂ = ∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t) := ⟨_, rfl⟩
  rw [← hD₁def] at hD₁ hD₂
  rw [← hD₂def] at hD₂
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ,
      c = min (1 / 16) (min ((L - 2) / 16) (min ((L - 1 - D₁) / 16) ((L - (D₁ + 2 * D₂)) / 16))) := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hcdef]
    exact lt_min (by norm_num) (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  have hc16 : c ≤ 1 / 16 := by rw [hcdef]; exact min_le_left _ _
  have hcL : c ≤ (L - 2) / 16 := by rw [hcdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hc₁ : c ≤ (L - 1 - D₁) / 16 := by
    rw [hcdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc₂ : c ≤ (L - (D₁ + 2 * D₂)) / 16 := by
    rw [hcdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the sums of `1/d`, and `k` and `ε_w`
  have ha₀L : a₀ ≤ L := by nlinarith [w₁_pos, w₁_lt_w₂, w₂_lt_one, L_pos]
  have ha₀L1 : a₀ ≤ L + 1 := by linarith
  obtain ⟨K₁, hK₁def⟩ : ∃ K₁ : ℝ, K₁ = (Real.log (L + 1) - Real.log a₀ + 1) ^ j := ⟨_, rfl⟩
  have hlogpos : 0 ≤ Real.log (L + 1) - Real.log a₀ + 1 := by
    have := Real.log_le_log ha₀ ha₀L1
    linarith
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁def]; exact pow_nonneg hlogpos j
  obtain ⟨k, hkev, hk2, hkC, hζε, hca⟩ := SieveProp6.exists_k hC₀
    (ε := η * c ^ 2 / (4 * Real.exp 1 * (K₁ + 1) * a₀)) (c := c) (by positivity) ha₀
  have hk4 : (0 : ℝ) < ((2 * k + 4 : ℕ) : ℝ) := by positivity
  obtain ⟨εw, hεw⟩ : ∃ εw : ℝ, εw = c / ((2 * k + 4 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hεw0 : 0 < εw := by rw [hεw]; exact div_pos hc0 hk4
  have hεwa : εw < a₀ := by rw [hεw, div_lt_iff₀ hk4]; linarith
  have hεw7 : εw * ((2 * k + 7 : ℕ) : ℝ) ≤ 2 * c := by
    rw [hεw, div_mul_eq_mul_div, div_le_iff₀ hk4]
    push_cast
    nlinarith
  have hεwc : (2 * k + 4 : ℝ) * εw = c := by
    rw [hεw]
    push_cast
    field_simp
  -- the tree's depth, the comparisons' bound, and the chains' and leaves' `δ`
  obtain ⟨smax, hsmdef⟩ : ∃ smax : ℕ, smax = ⌈(L + 2) / εw⌉₊ := ⟨_, rfl⟩
  have hsm : L + 2 ≤ εw * smax := by
    have := Nat.le_ceil ((L + 2) / εw)
    rw [← hsmdef, div_le_iff₀ hεw0] at this
    linarith
  obtain ⟨Λ₁', hΛ₁'⟩ : ∃ Λ₁' : ℝ, Λ₁' = Λ₁ + L + 2 := ⟨_, rfl⟩
  have hΛ₁'0 : 0 ≤ Λ₁' := by rw [hΛ₁']; linarith
  obtain ⟨Λ₀, hΛ₀⟩ : ∃ Λ₀ : ℝ, Λ₀ = Λ₁' + (j + smax) * (L + 1) := ⟨_, rfl⟩
  have hΛ₀0 : 0 ≤ Λ₀ := by
    have : (0 : ℝ) ≤ (j + smax) * (L + 1) := mul_nonneg (by positivity) (by linarith)
    rw [hΛ₀]; linarith
  obtain ⟨δ₁, hδ₁, q₁, hq₁⟩ :=
    SieveP6Tree.chainOK_TL hII hεw0 (j + smax + 1) (J₀ + 4 + smax * smax + 2 * smax + 2) hΛ₁'0
  obtain ⟨δ₂, hδ₂, q₂, hq₂⟩ :=
    SieveP6Tree.chainOK_TR hII hεw0 (j + smax + 1) (J₀ + 4 + smax * smax + 2 * smax + 2) hΛ₁'0
  obtain ⟨δ₃, hδ₃, q₃, hq₃⟩ := SieveP6TreeLeaves.leavesOK_of two_lt_L (a := 8 * c) (b := 8 * c) (δ' := 4 * c)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hεw0 hΛ₀0 (j + smax)
    (J₀ + 4 + smax * smax + 2 * smax + 2) hC₀ hC hkev (by omega) hkC (by rw [hεwc]; exact hc16)
  -- the remainder's constant and the final `δ`
  obtain ⟨Mrem, hMrem⟩ : ∃ Mrem : ℝ, Mrem = 24 * 2 ^ (2 * k + 7) * (K₁ * (Real.exp 1 * a₀ / εw)) := ⟨_, rfl⟩
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀ : ℝ, δ₀ = min (min c δ₁) (min δ₂ δ₃) / 2 := ⟨_, rfl⟩
  have hδ₀0 : 0 < δ₀ := by rw [hδ₀]; exact half_pos (lt_min (lt_min hc0 hδ₁) (lt_min hδ₂ hδ₃))
  have hm : 2 * δ₀ ≤ c ∧ 2 * δ₀ ≤ δ₁ ∧ 2 * δ₀ ≤ δ₂ ∧ 2 * δ₀ ≤ δ₃ := by
    have h1 := min_le_left (min c δ₁) (min δ₂ δ₃)
    have h2 := min_le_right (min c δ₁) (min δ₂ δ₃)
    have h3 := min_le_left c δ₁
    have h4 := min_le_right c δ₁
    have h5 := min_le_left δ₂ δ₃
    have h6 := min_le_right δ₂ δ₃
    rw [hδ₀]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  -- the conditions that hold for large `q`
  have hev : ∀ᶠ x : ℝ in Filter.atTop, 3 ≤ x ∧ 2 ≤ x ^ εw ∧
      ∑ p ∈ SieveRough.primesIn (x ^ εw) (x ^ a₀), 1 / (p : ℝ) ≤ Real.log a₀ - Real.log εw + 1 ∧
      ∑ p ∈ SieveRough.primesIn (x ^ a₀) (x ^ (L + 1 : ℝ)), 1 / (p : ℝ) ≤ Real.log (L + 1) - Real.log a₀ + 1 ∧
      Mrem ≤ x ^ c ∧ 4 * (smax : ℝ) + 5 ≤ x ^ δ₀ ∧ 128 ≤ x ^ ((w₂ - w₁) * L - a₀) ∧ 16 ≤ x ^ (L - w₁ * L) ∧
      8 ≤ x ^ (L - w₁ * L - ∑ i ∈ S₀, hi i) ∧ 4 * 2 ^ (2 * k + 4) ≤ x ^ (L - 1 - 8 * c - D₁ - c) ∧
      64 * 2 ^ (2 * k + 4) ≤ x ^ (L - 8 * c - D₁ - 2 * D₂ - c) :=
    (Filter.eventually_ge_atTop 3).and (((tendsto_rpow_atTop hεw0).eventually_ge_atTop _).and
      ((SieveRough.evLe_sum_inv hεw0 hεwa.le 1 one_pos).and ((SieveRough.evLe_sum_inv ha₀ ha₀L1 1 one_pos).and
      (((tendsto_rpow_atTop hc0).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop hδ₀0).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop (by linarith)).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop (by route_num)).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop (by linarith)).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop (by linarith)).eventually_ge_atTop _).and
      ((tendsto_rpow_atTop (by linarith)).eventually_ge_atTop _))))))))))
  obtain ⟨q₄, hq₄⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨δ₀, hδ₀0, max (max q₁ q₂) (max q₃ q₄), ?_⟩
  intro q _ hq a ha Ω hΩlen hΩc hΩ
  have hq12 := le_trans (le_max_left _ _) hq
  have hq34 := le_trans (le_max_right _ _) hq
  obtain ⟨hx3, hxw, hM1, hM2, hMrem', hδ2, h128, h16, h8, hsz₁, hsz₂⟩ := hq₄ q (le_trans (le_max_right _ _) hq34)
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  have hΩc' : ∀ C ∈ Ω, C.c 0 ≤ Λ₁' * Real.log q := fun C hC =>
    (hΩc C hC).trans (mul_le_mul_of_nonneg_right (by rw [hΛ₁']; linarith) hlogq.le)
  -- the windows' chains and the leaves
  obtain ⟨-, hW₁N, hP₁W, hP₂W, -⟩ := win_hi hq1 ha₀.le h128 h16
  have hokTL := hq₁ q (le_trans (le_max_left _ _) hq12) a ha ⌈(q : ℝ) ^ (w₁ * L)⌉₊ ⌊(q : ℝ) ^ (w₂ * L)⌋₊
    (Nat.le_ceil _) (Nat.floor_le (by positivity))
  have hokTR := hq₂ q (le_trans (le_max_right _ _) hq12) a ha _ _ hW₁N hP₁W hP₂W
  have hokL := hq₃ q (le_trans (le_max_left _ _) hq34) a ha
  have H := prop6ib_at ha Ω S₀ S₁ eIn₁ lo hi hokL hokTL hokTR hx3 hxw hεwa.le ha₀ ha₀L h128 h16 h8 hsm
    (by rw [hΛ₁']; linarith) hΛ₀.symm.le (by linarith) (by omega) le_rfl le_rfl hlo hmid hεwc
    (by rw [← hD₁def]; exact hsz₁) (by rw [← hD₁def, ← hD₂def]; exact hsz₂) hC₀ hC hkev (by omega) hkC hΩc' hΩ
  -- the sums of `1/d` and of `1/p`
  have hprime : ∀ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∀ i, rt i ≤ ⌊2 * (q : ℝ) ^ L⌋₊ ∧ (rt i).Prime :=
    fun rt hrt i => SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hrt).1 i)
  have hsRT : ∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ) ≤ K₁ := by
    refine (SieveProp6.sum_RT_inv_le (s := SieveRough.primesIn ((q : ℝ) ^ a₀) ((q : ℝ) ^ (L + 1 : ℝ))) ?_).trans ?_
    · intro rt hrt
      rw [Fintype.mem_piFinset]
      intro i
      obtain ⟨-, hz, -⟩ := hΩ rt (fun i => (hprime rt hrt i).2) (Finset.mem_filter.1 hrt).2
      rw [SieveRough.mem_primesIn]
      refine ⟨(hprime rt hrt i).2, le_trans (Nat.le_ceil _) (by exact_mod_cast hz i), ?_⟩
      have h1 : (rt i : ℝ) ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := by exact_mod_cast (hprime rt hrt i).1
      have h2 : (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) ≤ 2 * (q : ℝ) ^ L := Nat.floor_le (by positivity)
      have h3 : 2 * (q : ℝ) ^ L < (q : ℝ) ^ (L + 1 : ℝ) := by
        have hX0 : 0 < (q : ℝ) ^ L := by positivity
        rw [Real.rpow_add hq0, Real.rpow_one]
        nlinarith
      linarith
    · rw [hK₁def]
      exact pow_le_pow_left₀ (Finset.sum_nonneg fun p _ => by positivity) hM2 j
  have hsP : ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ ⌈(q : ℝ) ^ a₀⌉₊, (1 + 1 / (p : ℝ)) ≤ Real.exp 1 * a₀ / εw := by
    refine (SieveBrun.prod_one_add_le_exp _ _ fun p _ => by positivity).trans ?_
    have h : ∑ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ ⌈(q : ℝ) ^ a₀⌉₊, 1 / (p : ℝ) ≤ Real.log a₀ - Real.log εw + 1 := hM1
    calc Real.exp (∑ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ ⌈(q : ℝ) ^ a₀⌉₊, 1 / (p : ℝ)) ≤
          Real.exp (Real.log a₀ - Real.log εw + 1) := Real.exp_le_exp.2 h
      _ = Real.exp 1 * a₀ / εw := by
          rw [Real.exp_add, Real.exp_sub, Real.exp_log ha₀, Real.exp_log hεw0]
          ring
  have hsd : (∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
      ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ ⌈(q : ℝ) ^ a₀⌉₊, (1 + 1 / (p : ℝ)) ≤ K₁ * (Real.exp 1 * a₀ / εw) :=
    mul_le_mul hsRT hsP (Finset.prod_nonneg fun p _ => by positivity) hK₁0
  -- `w`
  have hw : (q : ℝ) ^ εw ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := Nat.le_ceil _
  have hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊ := by
    have : (2 : ℝ) ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := hxw.trans hw
    exact_mod_cast this
  have hw1 : (1 : ℝ) ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := Nat.one_le_cast.2 (by omega)
  have hwle : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ≤ 2 * (q : ℝ) ^ εw := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (q : ℝ) ^ εw by positivity)
    linarith
  have hlogw : εw * Real.log q ≤ Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := by
    rw [← Real.log_rpow hq0]
    exact Real.log_le_log (by positivity) hw
  have hlogw0 : 0 < Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := lt_of_lt_of_le (mul_pos hεw0 hlogq) hlogw
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have hφq : (q.totient : ℝ) ≤ q := Nat.cast_le.2 (Nat.totient_le q)
  have hK0 : 0 ≤ K₁ * (Real.exp 1 * a₀ / εw) := by positivity
  have hζ := SieveProp6.zeta_nonneg hC₀ k
  -- the main term
  have hX1 : 1 ≤ (q : ℝ) ^ L := Real.one_le_rpow hq1 L_pos.le
  have hNN : ((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) ≤ (q : ℝ) ^ L + 1 := by
    have h1 : (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) ≤ 2 * (q : ℝ) ^ L := Nat.floor_le (by positivity)
    have h2 : (q : ℝ) ^ L - 1 < (⌊(q : ℝ) ^ L⌋₊ : ℝ) := Nat.sub_one_lt_floor _
    linarith
  have hN0 : (0 : ℝ) ≤ (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊ := by
    have : (⌊(q : ℝ) ^ L⌋₊ : ℝ) ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := by exact_mod_cast Nat.floor_mono (by linarith)
    linarith
  have hmain : 2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
      (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) * (K₁ * (Real.exp 1 * a₀ / εw)) ≤
      η * (q : ℝ) ^ L / (q.totient * Real.log q) := by
    refine le_trans ?_ (SieveProp6.main_term hζ hX1 hφ hK₁0 (Real.exp_pos 1) ha₀ hεw0 hlogq hlogw
      (SieveProp6.main_coef (Real.exp_pos 1) hK₁0 ha₀ hc0 hη hεw hζε))
    have hdiv := div_le_div_of_nonneg_right hNN (mul_pos hφ hlogw0).le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv (by linarith)) hK0
  -- the remainder
  have hJ := SieveProp6.Jw_spec hw2
  have hrem : 2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k *
      (q : ℝ) ^ (L - 1 - 4 * c) * (K₁ * (Real.exp 1 * a₀ / εw)) ≤ (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - c : ℝ) :=
    SieveProp6.rem_term hq1 hw1 hwle hεw7 le_rfl (by positivity) hK0 hJ.2.1 hJ.2.2 hMrem hMrem' hφ hφq (by ring)
      (SieveProp6.rem_le hw1 _ k)
  -- the errors
  have hle : ∀ d : ℝ, 2 * δ₀ ≤ d → (q : ℝ) ^ (L - d) ≤ (q : ℝ) ^ (L - 2 * δ₀) :=
    fun d hd => Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hfin : (4 * (smax : ℝ) + 5) * (q : ℝ) ^ (L - 2 * δ₀) ≤ (q : ℝ) ^ (L - δ₀) := by
    have e : (q : ℝ) ^ (L - δ₀) = (q : ℝ) ^ δ₀ * (q : ℝ) ^ (L - 2 * δ₀) := by
      rw [← Real.rpow_add hq0]; ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_right hδ2 (by positivity)
  exact final_bound H hsd (mul_nonneg (mul_nonneg zero_le_two hζ) (div_nonneg hN0 (mul_pos hφ hlogw0).le))
    (mul_nonneg (mul_nonneg zero_le_two (SieveProp6.rem_nonneg _ _ k)) (Real.rpow_nonneg hq0.le _)) hmain hrem
    (by positivity) (by positivity) (hle c hm.1) (hle δ₁ hm.2.1) (hle δ₂ hm.2.2.1) (hle δ₃ hm.2.2.2) hfin

end SieveP6ib
