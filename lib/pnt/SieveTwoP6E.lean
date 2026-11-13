/-
# The comparison in two variables with the leaves of a box cut in three

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveTwoP6` is Harman's comparison with stops in two variables, its leaves by the paper's Lemma 4.3 on the wider
region. This file is the same with the leaves of a box that straddles the paper's region cut in three
(`SieveLeafSplit.tree_leaves_le3`): two parts by the paper's lemma with their own exponents, and the third by the
estimate in two variables (`SieveLeafTwo.LeavesE`).

Plain statements. `L` is a route's exponent (`SieveRoute.Route`).

* `tree_pattern2_le3`: `SieveTwoP6.tree_pattern2_le` with `tree_leaves_le3` for the leaves.
* `tree_pattern2_ib3`: the same with the sizes from the boxes, for a box whose leaves are cut at `d₁ ≤ q^{pA}` and
  `d₂ ≤ q^{th}`: `LeavesOK` with `pA` for `d₁` on the first part and `th` for `d₂` on the second, `LeavesE` on the third.
* `prop6_two_core3`: `SieveTwoP6.prop6_two_core` with `tree_pattern2_ib3`.

The file imports `SieveTwoP6.lean`, `SieveLeafSplit.lean` and `SieveLeafTwo.lean`.
-/
import SieveTwoP6
import SieveLeafSplit
import SieveLeafTwo

open Real Finset SieveFamily SieveTree SieveChain SieveRoute SieveP6Chain SieveP6Tree SieveP6ib SieveTwoP6

namespace SieveTwoP6E

open Classical

variable [Route]

/-- **A tree pattern with each size of leaves by the paper's lemma or cut in three.** `SieveTwoP6.tree_pattern2_le`
with `SieveLeafSplit.tree_leaves_le3` for the leaves: `LeavesOK` at `(a, b)` and `(a₂, b₂)`, and at each size either
the paper's sizes at one of them or `SieveLeafSplit.Split3`. -/
theorem tree_pattern2_le3 {q : ℕ} [NeZero q] {a' : ZMod q} (ha' : IsUnit a') {a b a₂ b₂ δ' εw Λ₀ Λ₁ C₀ δl δc : ℝ}
    {k J₀ J₀' K₀ Kmax A B Ar Br : ℕ} (hokL : SieveP6TreeLeaves.LeavesOK q a' L a b δ' εw Λ₀ C₀ δl k J₀ Kmax)
    (hokL₂ : SieveP6TreeLeaves.LeavesOK q a' L a₂ b₂ δ' εw Λ₀ C₀ δl k J₀ Kmax)
    (hokC : ChainOK2 q a' εw Λ₁ δc J₀' K₀ A B Ar Br) {j : ℕ} (Ω : List (GCmp j)) (S₀ Sr : Finset (Fin j))
    (hdisj : Disjoint S₀ Sr) (hSr : Sr.Nonempty)
    (I : ∀ s, Finset (Fin (j + s))) {z₀ smax : ℕ}
    (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hwz : ⌈(q : ℝ) ^ εw⌉₊ ≤ z₀) (hz₀ : z₀ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1)
    (hAB : (A + 1) * z₀ ≤ B) (hsmax : (A : ℝ) + 1 ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax) (hKL : j + smax ≤ Kmax)
    (hKC : j + smax ≤ K₀) (hlenL : Ω.length + smax * smax + 2 * smax + 4 ≤ J₀)
    (hlenC : Ω.length + smax * smax + 2 * smax + 2 ≤ J₀') (hΛ₁ : 0 ≤ Λ₁)
    (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) (hlz : Real.log z₀ ≤ Λ₁ * Real.log q)
    (hlE : Real.log ((A : ℝ) + 1) ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + (j + smax) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hreg : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, z₀ ≤ rt i) ∧ Ar < ∏ i ∈ Sr, rt i ∧ ∏ i ∈ Sr, rt i ≤ Br)
    (hfam : ∀ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∏ i ∈ S₀, (rt i : ℝ) < (A : ℝ) + 1)
    (hcase : ∀ s < smax, (∀ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊
        (SieveP6Tree.leafCmps Ω S₀ ((A : ℝ) + 1) ⌈(q : ℝ) ^ εw⌉₊ z₀ s),
      (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) →
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ (I s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤
          (q : ℝ) ^ (L - b)) ∨ (∀ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊
        (SieveP6Tree.leafCmps Ω S₀ ((A : ℝ) + 1) ⌈(q : ℝ) ^ εw⌉₊ z₀ s),
      (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) →
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a₂) ∧
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ (I s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤
          (q : ℝ) ^ (L - b₂)) ∨
      SieveLeafSplit.Split3 q a' L a b a₂ b₂ δ' εw Λ₁ δl k Ω S₀ I ((A : ℝ) + 1) z₀ s)
    (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) :
    ‖∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a' n * (if (∏ i, rt i) ∣ n ∧ rough z₀ n then 1 else 0)‖ ≤
      (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
          ((∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
            ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀, (1 + 1 / (p : ℝ))) +
        smax * (3 * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δl))) + smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δc)) := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hE : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  have hreg' : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) → StrictAnti rt ∧ ∀ i, z₀ ≤ rt i :=
    fun rt hp hΩ => ⟨(hreg rt hp hΩ).1, (hreg rt hp hΩ).2.1⟩
  have hfam' : ∀ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∏ i ∈ S₀, (rt i : ℝ) < (A : ℝ) + 1 ∧ ∀ i, z₀ ≤ rt i :=
    fun rt hrt => ⟨hfam rt hrt, (hreg' rt (fun i => (SieveTypeIIU.mem_primesLe.1
      (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hrt).1 i)).2) (Finset.mem_filter.1 hrt).2).2⟩
  rw [SieveP6Tree.tree_chains (Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊) (dw q a') Ω S₀ hE (by omega) hwz hz₀
    hfam']
  refine (norm_add_le _ _).trans ?_
  have hL := SieveLeafSplit.tree_leaves_le3 ha' hokL hokL₂ Ω S₀ I hE hw2 hwz hz₀ hsmax hKL hlenL hΛ₁ hc hlz hlE hΛ
    hX hN hreg' hcase hC₀ hC hk hk1 hkC ((primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀).card + 1)
  have hS := SieveTwoP6.stops_bound2 hq1 a' hΛ₁ hokC Ω S₀ Sr hdisj hSr (by omega) (Nat.le_ceil _) hwz hAB hsmax hKC hlenC hc
    hlz hlE hreg ((primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀).card + 1)
  linarith


/-! ### A box of leaves cut in three, with the sizes from the boxes -/

omit [Route] in
/-- **The bounds of a leaf from the boxes.** A leaf `x = (rt, y)` of a family whose chains satisfy `hreg`: its entries
at least `w`, and its two blocks at most `4q^{D₁}` and `4q^{D₂}`, `D₁ = Σ_{S₁} hi + t·[eIn₁]`,
`D₂ = Σ_{S₁ᶜ} hi + t·[¬eIn₁]`. -/
theorem leaf_bounds {q : ℕ} [NeZero q] {εw t : ℝ} {j : ℕ} {Ω : List (GCmp j)} {S₀ Sr S₁ : Finset (Fin j)}
    {eIn₁ : Bool} {hi : Fin j → ℝ} {A Ar Br z₀ : ℕ} (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hwz : ⌈(q : ℝ) ^ εw⌉₊ ≤ z₀)
    (hreg : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, z₀ ≤ rt i) ∧ (∀ i, (rt i : ℝ) ≤ (q : ℝ) ^ hi i) ∧
        (A : ℝ) + 1 ≤ 4 * (q : ℝ) ^ t * ∏ i ∈ S₀, (rt i : ℝ) ∧ Ar < ∏ i ∈ Sr, rt i ∧ ∏ i ∈ Sr, rt i ≤ Br)
    {s : ℕ} {x : Fin (j + s) → ℕ} (hprime : ∀ i, (x i).Prime)
    (hholds : ∀ C ∈ SieveP6Tree.leafCmps Ω S₀ ((A : ℝ) + 1) ⌈(q : ℝ) ^ εw⌉₊ z₀ s, C.holds 0 x) :
    (∀ i, ⌈(q : ℝ) ^ εw⌉₊ ≤ x i) ∧
    ∏ i ∈ Isplit S₁ eIn₁ s, (x i : ℝ) ≤ 4 * (q : ℝ) ^ (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) ∧
    ∏ i ∈ (Isplit S₁ eIn₁ s)ᶜ, (x i : ℝ) ≤ 4 * (q : ℝ) ^ (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hw0 : (0 : ℝ) < ⌈(q : ℝ) ^ εw⌉₊ := by exact_mod_cast (by omega : 0 < ⌈(q : ℝ) ^ εw⌉₊)
  have hz0 : (0 : ℝ) < z₀ := by exact_mod_cast (by omega : 0 < z₀)
  have hE : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  have hx1 : ∀ i, 1 ≤ x i := fun i => (hprime i).one_lt.le
  obtain ⟨hΩ1, ⟨-, hblk⟩, halive⟩ := (leafCmps_holds Ω S₀ hE hw0 hz0 hx1).1 hholds
  obtain ⟨-, hz, hbox, hAc, -⟩ := hreg _ (fun i => hprime _) hΩ1
  refine ⟨fun i => ?_, ?_⟩
  · induction i using Fin.addCases with
    | left i => exact le_trans hwz (hz i)
    | right u => exact_mod_cast (hblk u).2
  rw [prod_idxAll] at halive
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
  refine ⟨hI.trans ?_, hIc.trans ?_⟩
  · have hS : 0 ≤ (q : ℝ) ^ (∑ i ∈ S₁, hi i) := by positivity
    cases eIn₁
    · simp only [Bool.false_eq_true, ite_false, mul_one, add_zero]
      linarith
    · simp only [ite_true]
      rw [Real.rpow_add hq0]
      linarith
  · have hS : 0 ≤ (q : ℝ) ^ (∑ i ∈ S₁ᶜ, hi i) := by positivity
    cases eIn₁
    · simp only [Bool.false_eq_true, ite_false]
      rw [Real.rpow_add hq0]
      linarith
    · simp only [ite_true, mul_one, add_zero]
      linarith

/-- **A tree pattern with a box of leaves cut in three, with the sizes from the boxes.** `SieveTwoP6.tree_pattern2_ib`
for a box whose leaves straddle the paper's region: at each size the leaves are cut at `d₁ ≤ q^{pA}` and then
`d₂ ≤ q^{th}`; the first part by `LeavesOK` at `(a, b)` with the sizes of the box with `pA` for `d₁`, the second by
`LeavesOK` at `(a₂, b₂)` with `th` for `d₂`, and the third by `LeavesE` on the boxes `(AE, BE]` of `d₁` and
`(ArE, BrE]` of `d₂`, `AE ≤ q^{pA}`, `4q^{D₁} < BE + 1`, `ArE ≤ q^{th}` and `4q^{D₂} < BrE + 1`. -/
theorem tree_pattern2_ib3 {q : ℕ} [NeZero q] {a' : ZMod q} (ha' : IsUnit a')
    {a b a₂ b₂ δ' εw Λ₀ Λ₁ C₀ δl δc t c pA th : ℝ} {k J₀ J₀' J₀E K₀ K₀E Kmax A B Ar Br AE BE ArE BrE : ℕ}
    (hokL : SieveP6TreeLeaves.LeavesOK q a' L a b δ' εw Λ₀ C₀ δl k J₀ Kmax)
    (hokL₂ : SieveP6TreeLeaves.LeavesOK q a' L a₂ b₂ δ' εw Λ₀ C₀ δl k J₀ Kmax)
    (hokE : SieveLeafTwo.LeavesE q a' L Λ₁ δl J₀E K₀E ⌈(q : ℝ) ^ εw⌉₊ AE BE ArE BrE)
    (hokC : ChainOK2 q a' εw Λ₁ δc J₀' K₀ A B Ar Br) {j : ℕ} (Ω : List (GCmp j)) (S₀ Sr : Finset (Fin j))
    (hdisj : Disjoint S₀ Sr) (hSr : Sr.Nonempty) (S₁ : Finset (Fin j))
    (eIn₁ : Bool) (hi : Fin j → ℝ) {z₀ smax : ℕ}
    (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hwle : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ≤ 2 * (q : ℝ) ^ εw) (hwz : ⌈(q : ℝ) ^ εw⌉₊ ≤ z₀)
    (hz₀ : z₀ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1) (hAB : (A + 1) * z₀ ≤ B)
    (hsmax : (A : ℝ) + 1 ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax) (hKL : j + smax ≤ Kmax) (hKC : j + smax ≤ K₀)
    (hKE : j + smax ≤ K₀E)
    (hlenL : Ω.length + smax * smax + 2 * smax + 4 ≤ J₀) (hlenC : Ω.length + smax * smax + 2 * smax + 2 ≤ J₀')
    (hlenE : Ω.length + smax * smax + 2 * smax + 4 ≤ J₀E)
    (hΛ₁ : 0 ≤ Λ₁) (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) (hlz : Real.log z₀ ≤ Λ₁ * Real.log q)
    (hlE : Real.log ((A : ℝ) + 1) ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + (j + smax) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hreg : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, z₀ ≤ rt i) ∧ (∀ i, (rt i : ℝ) ≤ (q : ℝ) ^ hi i) ∧
        (A : ℝ) + 1 ≤ 4 * (q : ℝ) ^ t * ∏ i ∈ S₀, (rt i : ℝ) ∧ Ar < ∏ i ∈ Sr, rt i ∧ ∏ i ∈ Sr, rt i ≤ Br)
    (hfam : ∀ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∏ i ∈ S₀, (rt i : ℝ) < (A : ℝ) + 1)
    (hεwc : (2 * k + 4 : ℝ) * εw = c) (hpA : 0 ≤ pA) (hpAΛ : pA ≤ Λ₁) (hth : 0 ≤ th) (hthΛ : th ≤ Λ₁)
    (hszA₁ : 4 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a - pA - c))
    (hszA₂ : 64 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - b - pA -
      2 * (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t)) - c))
    (hszB₁ : 4 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a₂ - (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) - c))
    (hszB₂ : 64 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - b₂ - (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) - 2 * th - c))
    (hAE : (AE : ℝ) ≤ (q : ℝ) ^ pA) (hBE : 4 * (q : ℝ) ^ (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) < BE + 1)
    (hArE : (ArE : ℝ) ≤ (q : ℝ) ^ th) (hBrE : 4 * (q : ℝ) ^ (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t)) < BrE + 1)
    (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) :
    ‖∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a' n * (if (∏ i, rt i) ∣ n ∧ rough z₀ n then 1 else 0)‖ ≤
      (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
          ((∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
            ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀, (1 + 1 / (p : ℝ))) +
        smax * (3 * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δl))) + smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δc)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hw0 : (0 : ℝ) < ⌈(q : ℝ) ^ εw⌉₊ := by exact_mod_cast (by omega : 0 < ⌈(q : ℝ) ^ εw⌉₊)
  have hw1 : (1 : ℝ) ≤ ⌈(q : ℝ) ^ εw⌉₊ := by exact_mod_cast (by omega : 1 ≤ ⌈(q : ℝ) ^ εw⌉₊)
  have hE : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  have hwpow : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ 2 ^ (2 * k + 4) * (q : ℝ) ^ c := by
    calc (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (2 * (q : ℝ) ^ εw) ^ (2 * k + 4) :=
          pow_le_pow_left₀ hw0.le hwle _
      _ = 2 ^ (2 * k + 4) * (q : ℝ) ^ c := by
          rw [mul_pow, ← Real.rpow_natCast ((q : ℝ) ^ εw), ← Real.rpow_mul hq0.le, ← hεwc]
          push_cast
          ring_nf
  have hX₁ : (1 : ℝ) ≤ (q : ℝ) ^ pA := Real.one_le_rpow hq1 hpA
  have hX₂ : (1 : ℝ) ≤ (q : ℝ) ^ th := Real.one_le_rpow hq1 hth
  refine tree_pattern2_le3 ha' hokL hokL₂ hokC Ω S₀ Sr hdisj hSr (Isplit S₁ eIn₁) hw2 hwz hz₀ hAB hsmax hKL hKC
    hlenL hlenC hΛ₁ hc hlz hlE hΛ hX hN
    (fun rt hp hΩ => ⟨(hreg rt hp hΩ).1, (hreg rt hp hΩ).2.1, (hreg rt hp hΩ).2.2.2.2⟩) hfam ?_ hC₀ hC hk hk1 hkC
  intro s hs
  -- the first part's sizes, `d₁ ≤ q^{pA}`, and the second's, `d₂ ≤ q^{th}`
  have hA : ∀ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ (SieveP6Tree.leafCmps Ω S₀ ((A : ℝ) + 1) ⌈(q : ℝ) ^ εw⌉₊ z₀ s),
      (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) → ∏ i ∈ Isplit S₁ eIn₁ s, (x i : ℝ) ≤ (q : ℝ) ^ pA →
        ((∏ i ∈ Isplit S₁ eIn₁ s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
        ((∏ i ∈ Isplit S₁ eIn₁ s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) *
          ((∏ i ∈ (Isplit S₁ eIn₁ s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) ^ (L - b) := by
    intro x hx _ hle
    have hprime : ∀ i, (x i).Prime := fun i =>
      (SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx).1 i)).2
    obtain ⟨-, -, hIc'⟩ := leaf_bounds (S₁ := S₁) (eIn₁ := eIn₁) (hi := hi) (Sr := Sr) (Ar := Ar) (Br := Br) hw2 hwz
      hreg hprime (Finset.mem_filter.1 hx).2
    push_cast
    exact leaf_sizes_num hq0 (Finset.prod_nonneg fun i _ => Nat.cast_nonneg _) (by linarith) hIc' hw0.le hwpow
      hszA₁ hszA₂
  have hB : ∀ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ (SieveP6Tree.leafCmps Ω S₀ ((A : ℝ) + 1) ⌈(q : ℝ) ^ εw⌉₊ z₀ s),
      (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) → ∏ i ∈ (Isplit S₁ eIn₁ s)ᶜ, (x i : ℝ) ≤ (q : ℝ) ^ th →
        ((∏ i ∈ Isplit S₁ eIn₁ s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a₂) ∧
        ((∏ i ∈ Isplit S₁ eIn₁ s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) *
          ((∏ i ∈ (Isplit S₁ eIn₁ s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) ^ (L - b₂) := by
    intro x hx _ hle
    have hprime : ∀ i, (x i).Prime := fun i =>
      (SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx).1 i)).2
    obtain ⟨-, hI', -⟩ := leaf_bounds (S₁ := S₁) (eIn₁ := eIn₁) (hi := hi) (Sr := Sr) (Ar := Ar) (Br := Br) hw2 hwz
      hreg hprime (Finset.mem_filter.1 hx).2
    push_cast
    exact leaf_sizes_num hq0 (Finset.prod_nonneg fun i _ => Nat.cast_nonneg _) hI' (by linarith) hw0.le hwpow
      hszB₁ hszB₂
  -- a side of the leaves with no prime: all of them in the first part, or all in the second
  by_cases h1 : (Isplit S₁ eIn₁ s).Nonempty
  swap
  · left
    intro x hx hlt
    refine hA x hx hlt ?_
    rw [Finset.not_nonempty_iff_eq_empty.1 h1, Finset.prod_empty]
    exact hX₁
  by_cases h2 : (Isplit S₁ eIn₁ s)ᶜ.Nonempty
  swap
  · right
    left
    intro x hx hlt
    refine hB x hx hlt ?_
    rw [Finset.not_nonempty_iff_eq_empty.1 h2, Finset.prod_empty]
    exact hX₂
  right
  right
  refine ⟨h1, h2, (q : ℝ) ^ pA, (q : ℝ) ^ th, hX₁, hX₂, ?_, ?_, fun x hx hlt hle => hA x hx hlt hle,
    fun x hx hlt _ hle => hB x hx hlt hle, ?_⟩
  · rw [Real.log_rpow hq0]
    exact mul_le_mul_of_nonneg_right hpAΛ hlogq
  · rw [Real.log_rpow hq0]
    exact mul_le_mul_of_nonneg_right hthΛ hlogq
  · -- the third part, by `LeavesE`
    have hlen : ((SieveP6Tree.leafCmps Ω S₀ ((A : ℝ) + 1) ⌈(q : ℝ) ^ εw⌉₊ z₀ s ++
        [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]) ++
        [gDown (Isplit S₁ eIn₁ s) ((q : ℝ) ^ pA) true, gDown (Isplit S₁ eIn₁ s)ᶜ ((q : ℝ) ^ th) true]).length ≤
        J₀E := by
      have h1 := length_Pblock_le j s (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (z₀ : ℝ)
      have h2 : s * s + 2 * s ≤ smax * smax + 2 * smax := by nlinarith
      simp only [SieveP6Tree.leafCmps, List.length_append, List.length_map, List.length_cons, List.length_nil]
      omega
    have hcΩ := SieveP6TreeLeaves.leafCmps_c_le (j := j) (Ω := Ω) (S₀ := S₀) (E := (A : ℝ) + 1)
      (w := (⌈(q : ℝ) ^ εw⌉₊ : ℝ)) (z₀ := (z₀ : ℝ)) (X := (q : ℝ) ^ (L - 1 - δ')) (s := s) (B := Λ₁ * Real.log q)
      (by positivity) hc hlz hlE hw1 hX
    refine hokE (j + s) (by omega) (Isplit S₁ eIn₁ s) (Isplit S₁ eIn₁ s)ᶜ _ disjoint_compl_right
      h2 hlen ?_ ?_
    · intro C hC
      rcases List.mem_append.1 hC with h | h
      · exact hcΩ C h
      · have h0 : 0 ≤ Λ₁ * Real.log q := by positivity
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
        rcases h with rfl | rfl
        · show -Real.log ((q : ℝ) ^ pA) ≤ _
          have := Real.log_nonneg hX₁
          linarith
        · show -Real.log ((q : ℝ) ^ th) ≤ _
          have := Real.log_nonneg hX₂
          linarith
    · intro x hprime hholds
      have hx1 : ∀ i, 1 ≤ x i := fun i => (hprime i).one_lt.le
      simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
        and_true] at hholds
      obtain ⟨⟨hleaf, -⟩, hcut₁, hcut₂⟩ := hholds
      obtain ⟨hwx, hI', hIc'⟩ := leaf_bounds (S₁ := S₁) (eIn₁ := eIn₁) (hi := hi) (Sr := Sr) (Ar := Ar) (Br := Br)
        hw2 hwz hreg hprime hleaf
      rw [gDown_holds _ (by linarith) true 0 hx1] at hcut₁ hcut₂
      simp only [ite_true] at hcut₁ hcut₂
      refine ⟨hwx, ?_, ?_, ?_, ?_⟩
      · have : (AE : ℝ) < ((∏ i ∈ Isplit S₁ eIn₁ s, x i : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
      · have : ((∏ i ∈ Isplit S₁ eIn₁ s, x i : ℕ) : ℝ) < (BE : ℝ) + 1 := by push_cast; linarith
        exact Nat.lt_succ_iff.1 (by exact_mod_cast this)
      · have : (ArE : ℝ) < ((∏ i ∈ (Isplit S₁ eIn₁ s)ᶜ, x i : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
      · have : ((∏ i ∈ (Isplit S₁ eIn₁ s)ᶜ, x i : ℕ) : ℝ) < (BrE : ℝ) + 1 := by push_cast; linarith
        exact Nat.lt_succ_iff.1 (by exact_mod_cast this)

/-! ### The comparison at one `q` -/

set_option maxHeartbeats 1600000 in
/-- **Harman's comparison with stops in two variables, at one `q`, with a box of leaves cut in three.**
`SieveTwoP6.prop6_two_core` with `tree_pattern2_ib3` for the part of the family at most `P₁`: its leaves cut at
`d₁ ≤ q^{pA}` and `d₂ ≤ q^{th}`, by `LeavesOK` at `(aL, bL)` and `(aL₂, bL₂)` and by `LeavesE`. -/
theorem prop6_two_core3 {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {j : ℕ} (Ω : List (GCmp j))
    (S₀ Sr S₁ : Finset (Fin j)) (hdisj : Disjoint S₀ Sr) (hSr : Sr.Nonempty) (eIn₁ : Bool) (lo hi : Fin j → ℝ)
    {t aL bL aL₂ bL₂ δ' εw c Λ₀ Λ₁ C₀ δ₁ δ₃ pA th : ℝ} {k J₀C K₀ Kmax smax P₁ P₂ Ar Br z₀ AE BE ArE BrE : ℕ}
    (hokL : SieveP6TreeLeaves.LeavesOK q a L aL bL δ' εw Λ₀ C₀ δ₃ k J₀C Kmax)
    (hokL₂ : SieveP6TreeLeaves.LeavesOK q a L aL₂ bL₂ δ' εw Λ₀ C₀ δ₃ k J₀C Kmax)
    (hokE : SieveLeafTwo.LeavesE q a L Λ₁ δ₃ J₀C Kmax ⌈(q : ℝ) ^ εw⌉₊ AE BE ArE BrE)
    (hokC : ChainOK2 q a εw Λ₁ δ₁ J₀C K₀ P₁ P₂ Ar Br)
    (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hwle : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ≤ 2 * (q : ℝ) ^ εw) (hwz : ⌈(q : ℝ) ^ εw⌉₊ ≤ z₀)
    (hz₀ : z₀ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1) (hz₀q : (q : ℝ) ^ εw ≤ z₀) (hΛ₁ : 0 ≤ Λ₁)
    (hlz : Real.log z₀ ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + (j + smax) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hJ : Ω.length + 1 + smax * smax + 2 * smax + 4 ≤ J₀C) (hK : j + smax + 1 ≤ K₀) (hKm : j + smax ≤ Kmax)
    (hP₁ : 1 ≤ P₁) (hAB : (P₁ + 1) * z₀ ≤ P₂) (hsm : (P₁ : ℝ) + 1 ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax)
    (hl₁ : Real.log ((P₁ : ℝ) + 1) ≤ Λ₁ * Real.log q)
    (hB : ∀ s : ℝ, (q : ℝ) ^ (∑ i ∈ S₀, lo i) ≤ s → (P₁ : ℝ) + 1 ≤ 4 * (q : ℝ) ^ t * s)
    (hA : (q : ℝ) ^ (∑ i ∈ S₀, hi i) ≤ P₂) (hεwc : (2 * k + 4 : ℝ) * εw = c)
    (hpA : 0 ≤ pA) (hpAΛ : pA ≤ Λ₁) (hth : 0 ≤ th) (hthΛ : th ≤ Λ₁)
    (hszA₁ : 4 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - aL - pA - c))
    (hszA₂ : 64 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - bL - pA -
      2 * (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t)) - c))
    (hszB₁ : 4 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - aL₂ - (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) - c))
    (hszB₂ : 64 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - bL₂ - (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) - 2 * th - c))
    (hAE : (AE : ℝ) ≤ (q : ℝ) ^ pA) (hBE : 4 * (q : ℝ) ^ (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) < BE + 1)
    (hArE : (ArE : ℝ) ≤ (q : ℝ) ^ th) (hBrE : 4 * (q : ℝ) ^ (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t)) < BrE + 1)
    (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) (hΩc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q)
    (hΩ : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, z₀ ≤ rt i) ∧ (∀ i, (q : ℝ) ^ lo i ≤ rt i ∧ (rt i : ℝ) ≤ (q : ℝ) ^ hi i) ∧
        Ar < ∏ i ∈ Sr, rt i ∧ ∏ i ∈ Sr, rt i ≤ Br) :
    ‖∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a n * (if (∏ i, rt i) ∣ n ∧ rough z₀ n then 1 else 0)‖ ≤
      (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
          ((∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
            ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀, (1 + 1 / (p : ℝ))) +
        smax * (3 * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₃))) +
        (smax + 2) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₁)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqn : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hP₁0 : (0 : ℝ) < P₁ := by exact_mod_cast hP₁
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hqn)
  have hlP₁ : Real.log (P₁ : ℝ) ≤ Λ₁ * Real.log q := (Real.log_le_log hP₁0 (by linarith)).trans hl₁
  -- the two patterns' comparisons
  have hcB : ∀ C ∈ Ω ++ [gUp S₀ (P₁ : ℝ) false], C.c 0 ≤ Λ₁ * Real.log q := by
    intro C hC
    rcases List.mem_append.1 hC with h | h
    · exact hΩc C h
    · rw [List.mem_singleton] at h
      rw [h]
      exact hlP₁
  have hcW : ∀ C ∈ Ω ++ [gDown S₀ (P₁ : ℝ) true], C.c 0 ≤ Λ₁ * Real.log q := by
    intro C hC
    rcases List.mem_append.1 hC with h | h
    · exact hΩc C h
    · rw [List.mem_singleton] at h
      rw [h]
      show -Real.log (P₁ : ℝ) ≤ Λ₁ * Real.log q
      have h1 : 0 ≤ Real.log (P₁ : ℝ) := Real.log_nonneg (by exact_mod_cast hP₁)
      have h2 := mul_nonneg hΛ₁ hlogq
      linarith
  have hpatB : ∀ {rt : Fin j → ℕ}, (∀ i, 1 ≤ rt i) → ((∀ C ∈ Ω ++ [gUp S₀ (P₁ : ℝ) false], C.holds 0 rt) ↔
      (∀ C ∈ Ω, C.holds 0 rt) ∧ ∏ i ∈ S₀, (rt i : ℝ) ≤ P₁) := by
    intro rt h1
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
      and_true, gUp_holds _ hP₁0 false 0 h1, Bool.false_eq_true, ite_false]
  have hpatW : ∀ {rt : Fin j → ℕ}, (∀ i, 1 ≤ rt i) → ((∀ C ∈ Ω ++ [gDown S₀ (P₁ : ℝ) true], C.holds 0 rt) ↔
      (∀ C ∈ Ω, C.holds 0 rt) ∧ (P₁ : ℝ) < ∏ i ∈ S₀, (rt i : ℝ)) := by
    intro rt h1
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
      and_true, gDown_holds _ hP₁0 true 0 h1, ite_true]
  rw [sum_RTg_cmp Ω S₀ hP₁0 (fun rt => ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
    dw q a n * (if (∏ i, rt i) ∣ n ∧ rough z₀ n then 1 else 0))]
  -- at most `P₁`: a tree
  have hBb := tree_pattern2_ib3 ha hokL hokL₂ hokE hokC (Ω ++ [gUp S₀ (P₁ : ℝ) false]) S₀ Sr hdisj hSr S₁
    eIn₁ hi hw2 hwle hwz hz₀ hAB hsm hKm (by omega) hKm (by rw [List.length_append, List.length_singleton]; omega)
    (by rw [List.length_append, List.length_singleton]; omega)
    (by rw [List.length_append, List.length_singleton]; omega) hΛ₁ hcB hlz hl₁ hΛ hX hN
    (fun rt hp hh => by
      obtain ⟨hΩ', -⟩ := (hpatB (fun i => (hp i).one_lt.le)).1 hh
      obtain ⟨hsa, hz, hb, hrl, hrh⟩ := hΩ rt hp hΩ'
      exact ⟨hsa, hz, fun i => (hb i).2, hB _ (box_prod hq0 S₀ hb).1, hrl, hrh⟩)
    (fun rt hrt => by
      have := ((hpatB (one_le_of_mem_RTg hrt)).1 (Finset.mem_filter.1 hrt).2).2
      linarith)
    hεwc hpA hpAΛ hth hthΛ hszA₁ hszA₂ hszB₁ hszB₂ hAE hBE hArE hBrE hC₀ hC hk hk1 hkC
  -- above `P₁`: in the window
  have hWb := SieveTwoP6.root_bound2' hqn a hΛ₁ hokC (by omega) S₀ Sr hdisj hSr (Ω ++ [gDown S₀ (P₁ : ℝ) true])
    (by rw [List.length_append, List.length_singleton]; omega) hcW (by omega) hz₀q
    (fun rt hp hh => by
      obtain ⟨hΩ', hlt⟩ := (hpatW (fun i => (hp i).one_lt.le)).1 hh
      obtain ⟨hsa, hz, hb, hrl, hrh⟩ := hΩ rt hp hΩ'
      have hle : ∏ i ∈ S₀, (rt i : ℝ) ≤ P₂ := (box_prod hq0 S₀ hb).2.trans hA
      have hlt' : (P₁ : ℝ) < ((∏ i ∈ S₀, rt i : ℕ) : ℝ) := by push_cast; exact hlt
      have hle' : ((∏ i ∈ S₀, rt i : ℕ) : ℝ) ≤ P₂ := by push_cast; exact hle
      exact ⟨hsa, hz, by exact_mod_cast hlt', by exact_mod_cast hle', hrl, hrh⟩)
  -- the tree's family is a part of the family
  have hS := sum_RTg_cmp (Y := ⌊2 * (q : ℝ) ^ L⌋₊) Ω S₀ hP₁0 (fun rt => 1 / ((∏ i, rt i : ℕ) : ℝ))
  have hnn : ∀ Ω' : List (GCmp j), 0 ≤ ∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω', 1 / ((∏ i, rt i : ℕ) : ℝ) :=
    fun Ω' => Finset.sum_nonneg fun rt _ => by positivity
  have hSle : ∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ (Ω ++ [gUp S₀ (P₁ : ℝ) false]), 1 / ((∏ i, rt i : ℕ) : ℝ) ≤
      ∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ) := by
    rw [hS]
    linarith [hnn (Ω ++ [gDown S₀ (P₁ : ℝ) true])]
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
  refine (norm_add_le _ _).trans ?_
  have hmono := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hSle hPr) hMc
  linarith


end SieveTwoP6E
