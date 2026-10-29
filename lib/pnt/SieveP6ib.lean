/-
# Proposition 6 with the bilinear estimate

Plain statements. `GCmp`, `RTg` are `SieveChain`'s; `gUp`, `gDown` are `SieveP6Chain`'s; `ChainOK` is `SieveP6Tree`'s
and `LeavesOK` `SieveP6TreeLeaves`'s; `rough z n` and `primesIco w z` are `SieveTree`'s; `zeta`, `rem` and `Jw` are
`SieveProp6`'s. `N₁ = ⌊q^L⌋`, `N₂ = ⌊2q^L⌋` and `w = ⌈q^{εw}⌉`.

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


end SieveP6ib
