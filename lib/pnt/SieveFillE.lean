/-
# The comparison with the rest among the tree's primes, the leaves cut in three, at one modulus

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveFill` is Harman's comparison in two variables with the rest among the primes of Buchstab's tree, at one `q`;
its leaves are by the paper's Lemma 4.3. This file is the same with the leaves of a box that straddles the paper's
region cut in three (`SieveLeafFam3`): two parts by the paper's lemma with their own exponents, the third by the
estimate in two variables (`SieveLeafTwo.LeavesE`).

Plain statements. `L` is a route's exponent (`SieveRoute.Route`).

* `leaves_last_le3`: `SieveFill.leaves_last_le` with each size of leaves by `SieveLeafFam3.family_leaves_le3`.
* `last_pattern_le3`: `SieveFill.last_pattern_le` with `leaves_last_le3`.
* `blocks4`: a leaf's two blocks at most `4q^{D₁}` and `4q^{D₂}`.
* `fill_below_ib3`: `SieveFill.fill_below_ib` with `tree_leaves_le3` for the first tree and `last_pattern_le3` for the
  trees below its stops.
* `fill_window_ib3`: `SieveFill.fill_window_ib` with `SieveLeafSplit.tree_leaves_le3`, each size's three cases from
  the leaves' bounds (`SieveLeafFam3.cases3_of_bounds`).

The file imports `SieveFill.lean` and `SieveLeafFam3.lean`.
-/
import SieveFill
import SieveLeafFam3

open Real Finset SieveFamily SieveTree SieveChain SieveRoute SieveP6Chain SieveP6Tree SieveP6ib SieveTwoP6
  SieveFillTree SieveFill

namespace SieveFillE

open Classical

variable [Route]

set_option maxHeartbeats 1600000 in
/-- **The leaves of the tree below the last entry, each size by the paper's lemma or cut in three.**
`SieveFill.leaves_last_le` with each size by `SieveLeafFam3.family_leaves_le3`: the error term is `3s_max·q^{L−δ}/φ(q)`. -/
theorem leaves_last_le3 {q : ℕ} [NeZero q] {a' : ZMod q} (ha' : IsUnit a') {a b a₂ b₂ δ' εw Λ₀ Λ₁ C₀ δ E : ℝ}
    {k J₀ Kmax : ℕ} (hok : SieveP6TreeLeaves.LeavesOK q a' L a b δ' εw Λ₀ C₀ δ k J₀ Kmax)
    (hok₂ : SieveP6TreeLeaves.LeavesOK q a' L a₂ b₂ δ' εw Λ₀ C₀ δ k J₀ Kmax) {k' : ℕ}
    (Ω : List (GCmp (k' + 1))) (I : ∀ s, Finset (Fin (k' + 1 + s))) {smax : ℕ} (hE : 1 < E)
    (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hwY : ⌈(q : ℝ) ^ εw⌉₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1)
    (hsmax : E ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax) (hK : k' + 1 + smax ≤ Kmax)
    (hlen : Ω.length + smax * smax + 3 * smax + 4 ≤ J₀) (hΛ₁ : 0 ≤ Λ₁)
    (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q)
    (hlZ : Real.log ((⌊2 * (q : ℝ) ^ L⌋₊ + 1 : ℕ) : ℝ) ≤ Λ₁ * Real.log q)
    (hlE : Real.log E ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + ((k' + 1 + smax : ℕ) : ℝ) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hreg : ∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ ∀ i, ⌈(q : ℝ) ^ εw⌉₊ ≤ rt i)
    (hcase : ∀ s < smax, (∀ x ∈ RTg (k' + 1 + s) ⌊2 * (q : ℝ) ^ L⌋₊
        (leafCmpsL Ω E ⌈(q : ℝ) ^ εw⌉₊ ((⌊2 * (q : ℝ) ^ L⌋₊ + 1 : ℕ) : ℝ) s),
      (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) →
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ (I s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤
          (q : ℝ) ^ (L - b)) ∨
      (∀ x ∈ RTg (k' + 1 + s) ⌊2 * (q : ℝ) ^ L⌋₊
        (leafCmpsL Ω E ⌈(q : ℝ) ^ εw⌉₊ ((⌊2 * (q : ℝ) ^ L⌋₊ + 1 : ℕ) : ℝ) s),
      (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) →
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a₂) ∧
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ (I s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤
          (q : ℝ) ^ (L - b₂)) ∨
      SieveLeafFam3.Split3F q a' L a b a₂ b₂ δ' εw Λ₁ δ k (leafCmpsL Ω E ⌈(q : ℝ) ^ εw⌉₊ ((⌊2 * (q : ℝ) ^ L⌋₊ + 1 : ℕ) : ℝ) s) (I s))
    (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) (N : ℕ) :
    ‖∑ s ∈ range N, (-1 : ℂ) ^ s *
        ∑ x ∈ RTg (k' + 1 + s) ⌊2 * (q : ℝ) ^ L⌋₊
            (leafCmpsL Ω E ⌈(q : ℝ) ^ εw⌉₊ ((⌊2 * (q : ℝ) ^ L⌋₊ + 1 : ℕ) : ℝ) s),
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
            dw q a' n * (if (∏ i, x i) ∣ n ∧ rough ⌈(q : ℝ) ^ εw⌉₊ n then 1 else 0)‖ ≤
      (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
          ((∑ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
            ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ (⌊2 * (q : ℝ) ^ L⌋₊ + 1), (1 + 1 / (p : ℝ))) +
        smax * (3 * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ))) := by
  set N₂ := ⌊2 * (q : ℝ) ^ L⌋₊ with hN₂
  set w := ⌈(q : ℝ) ^ εw⌉₊ with hwdef
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqn : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hqn)
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast (by omega : 1 ≤ w)
  have hZ0 : (0 : ℝ) < ((N₂ + 1 : ℕ) : ℝ) := by positivity
  have hE0 : (0 : ℝ) < E := by linarith
  have hB : 0 ≤ Λ₁ * Real.log q := mul_nonneg hΛ₁ hlogq
  obtain ⟨Mc, hMcdef⟩ : ∃ Mc : ℝ, Mc = 2 * SieveProp6.zeta C₀ k * (((N₂ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
      (q.totient * Real.log (w : ℝ))) +
        2 * SieveProp6.rem (w : ℝ) (SieveProp6.Jw w) k * (q : ℝ) ^ (L - 1 - δ') := ⟨_, rfl⟩
  have hMc : 0 ≤ Mc := by
    rw [hMcdef]
    have hN' : (0 : ℝ) ≤ (N₂ : ℝ) - ⌊(q : ℝ) ^ L⌋₊ := by
      have : (⌊(q : ℝ) ^ L⌋₊ : ℝ) ≤ N₂ := by exact_mod_cast hN
      linarith
    have hlw : 0 ≤ Real.log (w : ℝ) := Real.log_nonneg hw1
    exact add_nonneg (mul_nonneg (mul_nonneg zero_le_two (SieveProp6.zeta_nonneg hC₀ k))
      (div_nonneg hN' (mul_nonneg (Nat.cast_nonneg _) hlw)))
      (mul_nonneg (mul_nonneg zero_le_two (SieveProp6.rem_nonneg _ _ k)) (Real.rpow_nonneg hq0.le _))
  rw [← hMcdef]
  have he : 0 ≤ 3 * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)) := by positivity
  -- the members of a family of leaves
  have hmem : ∀ s, ∀ x ∈ RTg (k' + 1 + s) N₂ (leafCmpsL Ω E w ((N₂ + 1 : ℕ) : ℝ) s),
      (StrictAnti x ∧ ∀ i, w ≤ x i) ∧ ∏ u : Fin s, (x (Fin.natAdd (k' + 1) u) : ℝ) < E ∧
        ∀ u : Fin s, (w : ℝ) ≤ x (Fin.natAdd (k' + 1) u) := by
    intro s x hx
    have hx1 := one_le_of_mem_RTg hx
    have hprime : ∀ i, (x i).Prime := fun i =>
      (SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx).1 i)).2
    obtain ⟨⟨hΩ1, ⟨hanti, hblk⟩, hlt⟩, hbelow⟩ :=
      (leafCmpsL_holds Ω hE0 hw0 hZ0 hx1).1 (Finset.mem_filter.1 hx).2
    obtain ⟨ha, hent⟩ := hreg _ (fun i => hprime _) hΩ1
    refine ⟨⟨strictAnti_chainL ha hanti hbelow, fun i => ?_⟩, hlt, fun u => (hblk u).2⟩
    induction i using Fin.addCases with
    | left i => exact hent i
    | right u => exact_mod_cast (hblk u).2
  -- each size
  have hsize : ∀ s < smax, ‖∑ x ∈ RTg (k' + 1 + s) N₂ (leafCmpsL Ω E w ((N₂ + 1 : ℕ) : ℝ) s),
      ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ N₂, dw q a' n * (if (∏ i, x i) ∣ n ∧ rough w n then 1 else 0)‖ ≤
        Mc * ∑ x ∈ RTg (k' + 1 + s) N₂ (leafCmpsL Ω E w ((N₂ + 1 : ℕ) : ℝ) s), 1 / ((∏ i, x i : ℕ) : ℝ) +
          3 * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)) := by
    intro s hs
    have hss : s * s + 3 * s ≤ smax * smax + 3 * smax := by nlinarith
    have hlen' := length_leafCmpsL_le Ω E (w : ℝ) ((N₂ + 1 : ℕ) : ℝ) s
    have hΛs : Λ₁ * Real.log q + ((k' + 1 + s : ℕ) : ℝ) * Real.log (N₂ : ℝ) ≤ Λ₀ * Real.log q := by
      have h1 : ((k' + 1 + s : ℕ) : ℝ) ≤ ((k' + 1 + smax : ℕ) : ℝ) := by exact_mod_cast (by omega)
      have h2 : 0 ≤ Real.log (N₂ : ℝ) := Real.log_natCast_nonneg N₂
      have := mul_le_mul_of_nonneg_right h1 h2
      linarith
    rw [hMcdef]
    exact SieveLeafFam3.family_leaves_le3 ha' hok hok₂ (leafCmpsL Ω E w ((N₂ + 1 : ℕ) : ℝ) s) (I s) hw2
      (by omega) (by omega) hΛ₁ (leafCmpsL_c_le hB hc hlZ hlE hw1) hΛs hX hN (fun x hx => (hmem s x hx).1)
      (hcase s hs) hC₀ hC hk hk1 hkC
  refine (SieveP6TreeLeaves.norm_sum_sizes_le'
    (b := fun s => Mc * ∑ x ∈ RTg (k' + 1 + s) N₂ (leafCmpsL Ω E w ((N₂ + 1 : ℕ) : ℝ) s),
      1 / ((∏ i, x i : ℕ) : ℝ) + 3 * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)))
    (fun s => by simp) (fun s => add_nonneg (mul_nonneg hMc (Finset.sum_nonneg fun x _ => by positivity)) he)
    hsize (fun s hs => ?_)).trans ?_
  · refine Finset.sum_eq_zero fun x hx => ?_
    exfalso
    obtain ⟨-, hlt, hge⟩ := hmem s x hx
    have h2 : (w : ℝ) ^ s ≤ ∏ u : Fin s, (x (Fin.natAdd (k' + 1) u) : ℝ) := by
      calc (w : ℝ) ^ s = ∏ _u : Fin s, (w : ℝ) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hw0.le) fun u _ => hge u
    have h3 : (w : ℝ) ^ smax ≤ (w : ℝ) ^ s := pow_le_pow_right₀ hw1 hs
    linarith
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hsub : ∑ s ∈ range smax, ∑ x ∈ RTg (k' + 1 + s) N₂ (leafCmpsL Ω E w ((N₂ + 1 : ℕ) : ℝ) s),
        1 / ((∏ i, x i : ℕ) : ℝ) ≤
          (∑ rt ∈ RTg (k' + 1) N₂ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
            ∏ p ∈ primesIco w (N₂ + 1), (1 + 1 / (p : ℝ)) := by
      refine le_trans (Finset.sum_le_sum fun s _ => ?_)
        (SieveP6TreeLeaves.sum_leaves_inv_le Ω ∅ E (by omega) hwY le_rfl smax)
      rw [leafCmpsL, RTg_append]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun x _ _ => by positivity
    have := mul_le_mul_of_nonneg_left hsub hMc
    linarith

set_option maxHeartbeats 1600000 in
/-- **A family sifted at its last entry, the leaves cut in three.** `SieveFill.last_pattern_le` with
`leaves_last_le3`. -/
theorem last_pattern_le3 {q : ℕ} [NeZero q] {a' : ZMod q} (ha' : IsUnit a') {a b a₂ b₂ δ' εw Λ₀ Λ₁ C₀ δl δc : ℝ}
    {k J₀ J₀' K₀ Kmax A B Ar Br : ℕ} (hokL : SieveP6TreeLeaves.LeavesOK q a' L a b δ' εw Λ₀ C₀ δl k J₀ Kmax)
    (hokL₂ : SieveP6TreeLeaves.LeavesOK q a' L a₂ b₂ δ' εw Λ₀ C₀ δl k J₀ Kmax)
    (hokC : ChainOK2 q a' εw Λ₁ δc J₀' K₀ A B Ar Br) {k' : ℕ} (Ω : List (GCmp (k' + 1)))
    (S : Finset (Fin (k' + 1))) (I : ∀ s, Finset (Fin (k' + 1 + s))) {zb smax : ℕ}
    (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hwY : ⌈(q : ℝ) ^ εw⌉₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1)
    (hAB : (Ar + 1) * zb ≤ Br) (hAr : 1 ≤ Ar) (hsmax : (Ar : ℝ) + 1 ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax)
    (hKL : k' + 1 + smax ≤ Kmax) (hKC : k' + 1 + smax ≤ K₀)
    (hlenL : Ω.length + smax * smax + 3 * smax + 4 ≤ J₀) (hlenC : Ω.length + smax * smax + 3 * smax + 2 ≤ J₀')
    (hΛ₁ : 0 ≤ Λ₁) (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q)
    (hlZ : Real.log ((⌊2 * (q : ℝ) ^ L⌋₊ + 1 : ℕ) : ℝ) ≤ Λ₁ * Real.log q)
    (hlA : Real.log ((Ar : ℝ) + 1) ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + ((k' + 1 + smax : ℕ) : ℝ) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hreg : ∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, ⌈(q : ℝ) ^ εw⌉₊ ≤ rt i) ∧ rt (Fin.last k') ≤ zb ∧ A < ∏ i ∈ S, rt i ∧
        ∏ i ∈ S, rt i ≤ B)
    (hcase : ∀ s < smax, (∀ x ∈ RTg (k' + 1 + s) ⌊2 * (q : ℝ) ^ L⌋₊
        (leafCmpsL Ω ((Ar : ℝ) + 1) ⌈(q : ℝ) ^ εw⌉₊ ((⌊2 * (q : ℝ) ^ L⌋₊ + 1 : ℕ) : ℝ) s),
      (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) →
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ (I s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤
          (q : ℝ) ^ (L - b)) ∨
      (∀ x ∈ RTg (k' + 1 + s) ⌊2 * (q : ℝ) ^ L⌋₊
        (leafCmpsL Ω ((Ar : ℝ) + 1) ⌈(q : ℝ) ^ εw⌉₊ ((⌊2 * (q : ℝ) ^ L⌋₊ + 1 : ℕ) : ℝ) s),
      (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) →
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a₂) ∧
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ (I s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤
          (q : ℝ) ^ (L - b₂)) ∨
      SieveLeafFam3.Split3F q a' L a b a₂ b₂ δ' εw Λ₁ δl k (leafCmpsL Ω ((Ar : ℝ) + 1) ⌈(q : ℝ) ^ εw⌉₊ ((⌊2 * (q : ℝ) ^ L⌋₊ + 1 : ℕ) : ℝ) s) (I s))
    (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) :
    ‖∑ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a' n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0)‖ ≤
      (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
          ((∑ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
            ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ (⌊2 * (q : ℝ) ^ L⌋₊ + 1), (1 + 1 / (p : ℝ))) +
        smax * (3 * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δl))) + smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δc)) := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hE : (1 : ℝ) < (Ar : ℝ) + 1 := by
    have : (1 : ℝ) ≤ Ar := by exact_mod_cast hAr
    linarith
  have hfam : ∀ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ L⌋₊ Ω, StrictAnti rt ∧ ⌈(q : ℝ) ^ εw⌉₊ ≤ rt (Fin.last k') :=
    fun rt hrt => by
      obtain ⟨h1, h2, -⟩ := hreg rt (fun i => (SieveTypeIIU.mem_primesLe.1
        (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hrt).1 i)).2) (Finset.mem_filter.1 hrt).2
      exact ⟨h1, h2 _⟩
  rw [tree_last (Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊) (dw q a') Ω hE (by omega) hwY hfam]
  refine (norm_add_le _ _).trans ?_
  have hL := leaves_last_le3 ha' hokL hokL₂ Ω I hE hw2 hwY hsmax hKL hlenL hΛ₁ hc hlZ hlA hΛ hX hN
    (fun rt hp hΩ => ⟨(hreg rt hp hΩ).1, (hreg rt hp hΩ).2.1⟩) hcase hC₀ hC hk hk1 hkC
    ((primesIco ⌈(q : ℝ) ^ εw⌉₊ (⌊2 * (q : ℝ) ^ L⌋₊ + 1)).card + 1)
  have hS := stops_last_le hq1 a' hΛ₁ hokC Ω S (by omega) (Nat.le_ceil _) hAB hsmax hKC hlenC hc hlZ hlA hreg
    ((primesIco ⌈(q : ℝ) ^ εw⌉₊ (⌊2 * (q : ℝ) ^ L⌋₊ + 1)).card + 1)
  linarith

omit [Route] in
/-- The bounds of a leaf's two blocks (`SieveP6ib.leaf_blocks_le`, `SieveFill.leaf_blocks2_le`) as `4q^D`. -/
theorem blocks4 {q : ℕ} (hq0 : (0 : ℝ) < q) {K : ℕ} (I : Finset (Fin K)) (x : Fin K → ℕ) {j : ℕ}
    (S₁ : Finset (Fin j)) (eIn₁ : Bool) (hi : Fin j → ℝ) {T : ℝ}
    (hI : ∏ i ∈ I, (x i : ℝ) ≤ (q : ℝ) ^ (∑ i ∈ S₁, hi i) * (if eIn₁ then 4 * (q : ℝ) ^ T else 1))
    (hIc : ∏ i ∈ Iᶜ, (x i : ℝ) ≤ (q : ℝ) ^ (∑ i ∈ S₁ᶜ, hi i) * (if eIn₁ then 1 else 4 * (q : ℝ) ^ T)) :
    ∏ i ∈ I, (x i : ℝ) ≤ 4 * (q : ℝ) ^ (∑ i ∈ S₁, hi i + (if eIn₁ then T else 0)) ∧
      ∏ i ∈ Iᶜ, (x i : ℝ) ≤ 4 * (q : ℝ) ^ (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else T)) := by
  have hqT : 0 ≤ (q : ℝ) ^ T := by positivity
  constructor
  · refine hI.trans ?_
    have hS : 0 ≤ (q : ℝ) ^ (∑ i ∈ S₁, hi i) := by positivity
    cases eIn₁
    · simp only [Bool.false_eq_true, ite_false, mul_one, add_zero]
      linarith
    · simp only [ite_true]
      rw [Real.rpow_add hq0]
      linarith
  · refine hIc.trans ?_
    have hS : 0 ≤ (q : ℝ) ^ (∑ i ∈ S₁ᶜ, hi i) := by positivity
    cases eIn₁
    · simp only [Bool.false_eq_true, ite_false]
      rw [Real.rpow_add hq0]
      linarith
    · simp only [ite_true, mul_one, add_zero]
      linarith

set_option maxHeartbeats 1600000 in
/-- **A family in the window, the leaves cut in three.** `SieveFill.fill_window_ib` with the leaves of each size by
the paper's lemma at `(a, b)` for `(pA, D₂)` or at `(a₂, b₂)` for `(D₁, th)`, or cut in three at `q^{pA}` and
`q^{th}` with the third part by `LeavesE` (`SieveLeafFam3.cases3_of_bounds`). -/
theorem fill_window_ib3 {q : ℕ} [NeZero q] {a' : ZMod q} (ha' : IsUnit a')
    {a b a₂ b₂ δ' εw Λ₀ Λ₁ C₀ δl δc T c pA th : ℝ} {k J₀ J₀' J₀E K₀ K₀E Kmax A B Ar Br AE BE ArE BrE : ℕ}
    (hokL : SieveP6TreeLeaves.LeavesOK q a' L a b δ' εw Λ₀ C₀ δl k J₀ Kmax)
    (hokL₂ : SieveP6TreeLeaves.LeavesOK q a' L a₂ b₂ δ' εw Λ₀ C₀ δl k J₀ Kmax)
    (hokE : SieveLeafTwo.LeavesE q a' L Λ₁ δl J₀E K₀E ⌈(q : ℝ) ^ εw⌉₊ AE BE ArE BrE)
    (hokC : ChainOK2 q a' εw Λ₁ δc J₀' K₀ A B Ar Br) {j : ℕ} (Ω : List (GCmp j)) (S₀ S₁ : Finset (Fin j))
    (eIn₁ : Bool) (hi : Fin j → ℝ) {z₀ smax : ℕ}
    (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hwle : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ≤ 2 * (q : ℝ) ^ εw) (hwz : ⌈(q : ℝ) ^ εw⌉₊ ≤ z₀)
    (hz₀ : z₀ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1) (hArB : (Ar + 1) * z₀ ≤ Br) (hAr : 1 ≤ Ar)
    (hsmr : (Ar : ℝ) + 1 ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax) (hKL : j + smax ≤ Kmax) (hKC : j + smax ≤ K₀)
    (hKE : j + smax ≤ K₀E) (hlenL : Ω.length + smax * smax + 2 * smax + 4 ≤ J₀)
    (hlenC : Ω.length + smax * smax + 2 * smax + 2 ≤ J₀') (hlenE : Ω.length + smax * smax + 2 * smax + 4 ≤ J₀E)
    (hΛ₁ : 0 ≤ Λ₁) (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) (hlz : Real.log z₀ ≤ Λ₁ * Real.log q)
    (hlA : Real.log ((Ar : ℝ) + 1) ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + ((j : ℝ) + smax) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hreg : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, z₀ ≤ rt i) ∧ (∀ i, (rt i : ℝ) ≤ (q : ℝ) ^ hi i) ∧ A < ∏ i ∈ S₀, rt i ∧
        ∏ i ∈ S₀, rt i ≤ B)
    (hT : (Ar : ℝ) + 1 ≤ 4 * (q : ℝ) ^ T) (hεwc : (2 * k + 4 : ℝ) * εw = c)
    (hpA : 0 ≤ pA) (hpAΛ : pA ≤ Λ₁) (hth : 0 ≤ th) (hthΛ : th ≤ Λ₁)
    (hszA₁ : 4 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a - pA - c))
    (hszA₂ : 64 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - b - pA - 2 * (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else T)) - c))
    (hszB₁ : 4 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a₂ - (∑ i ∈ S₁, hi i + (if eIn₁ then T else 0)) - c))
    (hszB₂ : 64 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - b₂ - (∑ i ∈ S₁, hi i + (if eIn₁ then T else 0)) - 2 * th - c))
    (hAE : (AE : ℝ) ≤ (q : ℝ) ^ pA) (hBE : 4 * (q : ℝ) ^ (∑ i ∈ S₁, hi i + (if eIn₁ then T else 0)) < BE + 1)
    (hArE : (ArE : ℝ) ≤ (q : ℝ) ^ th) (hBrE : 4 * (q : ℝ) ^ (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else T)) < BrE + 1)
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
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hw0 : (0 : ℝ) < ⌈(q : ℝ) ^ εw⌉₊ := by exact_mod_cast (by omega : 0 < ⌈(q : ℝ) ^ εw⌉₊)
  have hz0 : (0 : ℝ) < z₀ := by exact_mod_cast (by omega : 0 < z₀)
  have hE : (0 : ℝ) < (Ar : ℝ) + 1 := by positivity
  have hwpow : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ 2 ^ (2 * k + 4) * (q : ℝ) ^ c := by
    calc (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (2 * (q : ℝ) ^ εw) ^ (2 * k + 4) :=
          pow_le_pow_left₀ hw0.le hwle _
      _ = 2 ^ (2 * k + 4) * (q : ℝ) ^ c := by
          rw [mul_pow, ← Real.rpow_natCast ((q : ℝ) ^ εw), ← Real.rpow_mul hq0.le, ← hεwc]
          push_cast
          ring_nf
  have hreg' : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) → StrictAnti rt ∧ ∀ i, z₀ ≤ rt i :=
    fun rt hp hΩ => ⟨(hreg rt hp hΩ).1, (hreg rt hp hΩ).2.1⟩
  have hfam' : ∀ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω,
      ∏ i ∈ (∅ : Finset (Fin j)), (rt i : ℝ) < (Ar : ℝ) + 1 ∧ ∀ i, z₀ ≤ rt i := fun rt hrt => by
    refine ⟨?_, (hreg' rt (fun i => (SieveTypeIIU.mem_primesLe.1
      (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hrt).1 i)).2) (Finset.mem_filter.1 hrt).2).2⟩
    rw [Finset.prod_empty]
    have : (1 : ℝ) ≤ Ar := by exact_mod_cast hAr
    linarith
  rw [tree_chains (Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊) (dw q a') Ω ∅ hE (by omega) hwz hz₀ hfam']
  refine (norm_add_le _ _).trans ?_
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
  have hw1 : (1 : ℝ) ≤ ⌈(q : ℝ) ^ εw⌉₊ := by exact_mod_cast (by omega : 1 ≤ ⌈(q : ℝ) ^ εw⌉₊)
  have hLv := SieveLeafSplit.tree_leaves_le3 ha' hokL hokL₂ Ω ∅ (Isplit S₁ eIn₁) hE hw2 hwz hz₀ hsmr hKL hlenL hΛ₁
    hc hlz hlA hΛ hX hN hreg' (fun s hs => by
      have hcl : ∀ C ∈ SieveP6Tree.leafCmps Ω ∅ ((Ar : ℝ) + 1) ⌈(q : ℝ) ^ εw⌉₊ z₀ s, C.c 0 ≤ Λ₁ * Real.log q :=
        fun C hC => SieveP6TreeLeaves.leafCmps_c_le (X := (q : ℝ) ^ (L - 1 - δ')) (mul_nonneg hΛ₁ hlogq) hc hlz hlA
          hw1 hX C (List.mem_append_left _ hC)
      have hlen' : (SieveP6Tree.leafCmps Ω ∅ ((Ar : ℝ) + 1) ⌈(q : ℝ) ^ εw⌉₊ z₀ s).length + 3 ≤ J₀E := by
        have h1 := length_Pblock_le j s (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (z₀ : ℝ)
        have h2 : s * s + 2 * s ≤ smax * smax + 2 * smax := by nlinarith
        simp only [SieveP6Tree.leafCmps, List.length_append, List.length_map, List.length_cons, List.length_nil]
        omega
      exact SieveLeafFam3.cases3_of_bounds hokE _ (Isplit S₁ eIn₁ s) (by omega) hlen' hΛ₁ hcl hX
        (fun x hprime hholds => by
          have hx1 : ∀ i, 1 ≤ x i := fun i => (hprime i).one_lt.le
          obtain ⟨hΩ1, ⟨-, hblk⟩, halive⟩ := (leafCmps_holds Ω ∅ hE hw0 hz0 hx1).1 hholds
          obtain ⟨-, hz, hbox, -⟩ := hreg _ (fun i => hprime _) hΩ1
          rw [prod_idxAll, Finset.prod_empty, one_mul] at halive
          obtain ⟨hI, hIc⟩ := leaf_blocks_le S₁ eIn₁ hx1 hq0 hi hbox (halive.le.trans hT)
          obtain ⟨hI', hIc'⟩ := SieveFillE.blocks4 hq0 _ x S₁ eIn₁ hi hI hIc
          refine ⟨fun i => ?_, hI', hIc'⟩
          induction i using Fin.addCases with
          | left i => exact hwz.trans (hz i)
          | right u => exact_mod_cast (hblk u).2)
        hwpow hpA hpAΛ hth hthΛ hszA₁ hszA₂ hszB₁ hszB₂ hAE hBE hArE hBrE) hC₀ hC hk hk1 hkC
    ((primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀).card + 1)
  have hSt := stops_rest_le hq1 a' hΛ₁ hokC Ω S₀ (by omega) (Nat.le_ceil _) hwz hArB hsmr hKC hlenC hc hlz hlA
    (fun rt hp hΩ => ⟨(hreg rt hp hΩ).1, (hreg rt hp hΩ).2.1, (hreg rt hp hΩ).2.2.2⟩)
    ((primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀).card + 1)
  linarith

set_option maxHeartbeats 3200000 in
/-- **A family below the window, the leaves cut in three.** `SieveFill.fill_below_ib` with the leaves of its first
tree by `SieveLeafSplit.tree_leaves_le3` and those of the trees below its stops by `last_pattern_le3`, each size's three
cases from the leaves' bounds (`SieveLeafFam3.cases3_of_bounds`). -/
theorem fill_below_ib3 {q : ℕ} [NeZero q] {a' : ZMod q} (ha' : IsUnit a')
    {a b a₂ b₂ δ' εw Λ₀ Λ₁ C₀ δl δc t T c pA th : ℝ} {k J₀ J₀' J₀E K₀ K₀E Kmax A B Ar Br AE BE ArE BrE : ℕ}
    (hokL : SieveP6TreeLeaves.LeavesOK q a' L a b δ' εw Λ₀ C₀ δl k J₀ Kmax)
    (hokL₂ : SieveP6TreeLeaves.LeavesOK q a' L a₂ b₂ δ' εw Λ₀ C₀ δl k J₀ Kmax)
    (hokE : SieveLeafTwo.LeavesE q a' L Λ₁ δl J₀E K₀E ⌈(q : ℝ) ^ εw⌉₊ AE BE ArE BrE)
    (hokC : ChainOK2 q a' εw Λ₁ δc J₀' K₀ A B Ar Br) {j : ℕ} (Ω : List (GCmp j)) (S₀ S₁ : Finset (Fin j))
    (eIn₁ : Bool) (hi : Fin j → ℝ) {z₀ smax : ℕ}
    (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hwle : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ≤ 2 * (q : ℝ) ^ εw) (hwz : ⌈(q : ℝ) ^ εw⌉₊ ≤ z₀)
    (hz₀ : z₀ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1) (hAB : (A + 1) * z₀ ≤ B) (hArB : (Ar + 1) * z₀ ≤ Br) (hAr : 1 ≤ Ar)
    (hsmax : (A : ℝ) + 1 ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax)
    (hsmr : (Ar : ℝ) + 1 ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax) (hKL : j + 2 * smax ≤ Kmax) (hKC : j + 2 * smax ≤ K₀)
    (hKE : j + 2 * smax ≤ K₀E) (hlenL : Ω.length + 2 * (smax * smax) + 5 * smax + 6 ≤ J₀)
    (hlenE : Ω.length + 2 * (smax * smax) + 5 * smax + 6 ≤ J₀E)
    (hlenC : Ω.length + 2 * (smax * smax) + 5 * smax + 4 ≤ J₀') (hΛ₁ : 0 ≤ Λ₁)
    (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) (hlz : Real.log z₀ ≤ Λ₁ * Real.log q)
    (hlZ : Real.log ((⌊2 * (q : ℝ) ^ L⌋₊ + 1 : ℕ) : ℝ) ≤ Λ₁ * Real.log q)
    (hlE : Real.log ((A : ℝ) + 1) ≤ Λ₁ * Real.log q) (hlA : Real.log ((Ar : ℝ) + 1) ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + ((j + 2 * smax : ℕ) : ℝ) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hreg : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, z₀ ≤ rt i) ∧ (∀ i, (rt i : ℝ) ≤ (q : ℝ) ^ hi i) ∧
        (A : ℝ) + 1 ≤ 4 * (q : ℝ) ^ t * ∏ i ∈ S₀, (rt i : ℝ))
    (hfam : ∀ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∏ i ∈ S₀, (rt i : ℝ) < (A : ℝ) + 1)
    (hT : 4 * (q : ℝ) ^ t * z₀ * ((Ar : ℝ) + 1) ≤ 4 * (q : ℝ) ^ T) (hεwc : (2 * k + 4 : ℝ) * εw = c)
    (hpA : 0 ≤ pA) (hpAΛ : pA ≤ Λ₁) (hth : 0 ≤ th) (hthΛ : th ≤ Λ₁)
    (hszA₁ : 4 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a - pA - c))
    (hszA₂ : 64 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - b - pA - 2 * (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else T)) - c))
    (hszB₁ : 4 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a₂ - (∑ i ∈ S₁, hi i + (if eIn₁ then T else 0)) - c))
    (hszB₂ : 64 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - b₂ - (∑ i ∈ S₁, hi i + (if eIn₁ then T else 0)) - 2 * th - c))
    (hAE : (AE : ℝ) ≤ (q : ℝ) ^ pA) (hBE : 4 * (q : ℝ) ^ (∑ i ∈ S₁, hi i + (if eIn₁ then T else 0)) < BE + 1)
    (hArE : (ArE : ℝ) ≤ (q : ℝ) ^ th) (hBrE : 4 * (q : ℝ) ^ (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else T)) < BrE + 1)
    (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) :
    ‖∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a' n * (if (∏ i, rt i) ∣ n ∧ rough z₀ n then 1 else 0)‖ ≤
      (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
          (((∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
            ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀, (1 + 1 / (p : ℝ))) *
            (1 + ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ (⌊2 * (q : ℝ) ^ L⌋₊ + 1), (1 + 1 / (p : ℝ)))) +
        (smax + smax * smax) * (3 * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δl))) +
        smax * smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δc)) := by
  set N₂ := ⌊2 * (q : ℝ) ^ L⌋₊ with hN₂
  set w := ⌈(q : ℝ) ^ εw⌉₊ with hwdef
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqn : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hqn)
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast (by omega : 1 ≤ w)
  have hz0 : (0 : ℝ) < z₀ := by exact_mod_cast (by omega : 0 < z₀)
  have hz1 : (1 : ℝ) ≤ z₀ := by exact_mod_cast (by omega : 1 ≤ z₀)
  have hwz' : (w : ℝ) ≤ z₀ := by exact_mod_cast hwz
  have hZ0 : (0 : ℝ) < ((N₂ + 1 : ℕ) : ℝ) := by positivity
  have hE : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  have hEB : (0 : ℝ) < (Ar : ℝ) + 1 := by positivity
  have hAr1 : (1 : ℝ) ≤ (Ar : ℝ) + 1 := by linarith [(Nat.cast_nonneg Ar : (0 : ℝ) ≤ Ar)]
  have hBnn : 0 ≤ Λ₁ * Real.log q := mul_nonneg hΛ₁ hlogq
  have hlogN : 0 ≤ Real.log (N₂ : ℝ) := Real.log_natCast_nonneg N₂
  have hqt : 0 < (q : ℝ) ^ t := by positivity
  have hwY : w ≤ N₂ + 1 := hwz.trans hz₀
  have hwpow : (w : ℝ) ^ (2 * k + 4) ≤ 2 ^ (2 * k + 4) * (q : ℝ) ^ c := by
    calc (w : ℝ) ^ (2 * k + 4) ≤ (2 * (q : ℝ) ^ εw) ^ (2 * k + 4) := pow_le_pow_left₀ hw0.le hwle _
      _ = 2 ^ (2 * k + 4) * (q : ℝ) ^ c := by
          rw [mul_pow, ← Real.rpow_natCast ((q : ℝ) ^ εw), ← Real.rpow_mul hq0.le, ← hεwc]
          push_cast
          ring_nf
  have htT : 4 * (q : ℝ) ^ t ≤ 4 * (q : ℝ) ^ T := by
    refine le_trans ?_ hT
    have h1 : 4 * (q : ℝ) ^ t * 1 ≤ 4 * (q : ℝ) ^ t * z₀ := mul_le_mul_of_nonneg_left hz1 (by positivity)
    have h2 : 4 * (q : ℝ) ^ t * z₀ * 1 ≤ 4 * (q : ℝ) ^ t * z₀ * ((Ar : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hAr1 (by positivity)
    linarith
  have hreg' : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) → StrictAnti rt ∧ ∀ i, z₀ ≤ rt i :=
    fun rt hp hΩ => ⟨(hreg rt hp hΩ).1, (hreg rt hp hΩ).2.1⟩
  have hfam' : ∀ rt ∈ RTg j N₂ Ω, ∏ i ∈ S₀, (rt i : ℝ) < (A : ℝ) + 1 ∧ ∀ i, z₀ ≤ rt i :=
    fun rt hrt => ⟨hfam rt hrt, (hreg' rt (fun i => (SieveTypeIIU.mem_primesLe.1
      (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hrt).1 i)).2) (Finset.mem_filter.1 hrt).2).2⟩
  obtain ⟨Mc, hMcdef⟩ : ∃ Mc : ℝ, Mc = 2 * SieveProp6.zeta C₀ k * (((N₂ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
      (q.totient * Real.log (w : ℝ))) +
        2 * SieveProp6.rem (w : ℝ) (SieveProp6.Jw w) k * (q : ℝ) ^ (L - 1 - δ') := ⟨_, rfl⟩
  have hMc : 0 ≤ Mc := by
    rw [hMcdef]
    have hN' : (0 : ℝ) ≤ (N₂ : ℝ) - ⌊(q : ℝ) ^ L⌋₊ := by
      have : (⌊(q : ℝ) ^ L⌋₊ : ℝ) ≤ N₂ := by exact_mod_cast hN
      linarith
    have hlw : 0 ≤ Real.log (w : ℝ) := Real.log_nonneg hw1
    exact add_nonneg (mul_nonneg (mul_nonneg zero_le_two (SieveProp6.zeta_nonneg hC₀ k))
      (div_nonneg hN' (mul_nonneg (Nat.cast_nonneg _) hlw)))
      (mul_nonneg (mul_nonneg zero_le_two (SieveProp6.rem_nonneg _ _ k)) (Real.rpow_nonneg hq0.le _))
  rw [← hMcdef]
  obtain ⟨el, hel⟩ : ∃ el : ℝ, el = 3 * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δl)) := ⟨_, rfl⟩
  obtain ⟨ec, hec⟩ : ∃ ec : ℝ, ec = (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δc) := ⟨_, rfl⟩
  have hel0 : 0 ≤ el := by rw [hel]; positivity
  have hec0 : 0 ≤ ec := by rw [hec]; positivity
  rw [← hel, ← hec]
  obtain ⟨PN, hPN⟩ : ∃ PN : ℝ, PN = ∏ p ∈ primesIco w (N₂ + 1), (1 + 1 / (p : ℝ)) := ⟨_, rfl⟩
  have hPN0 : 0 ≤ PN := by rw [hPN]; exact Finset.prod_nonneg fun p _ => by positivity
  rw [← hPN]
  rw [tree_chains (Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ N₂) (dw q a') Ω S₀ hE (by omega) hwz hz₀ hfam']
  refine (norm_add_le _ _).trans ?_
  -- the leaves of the first tree
  have hΛA : Λ₁ * Real.log q + ((j : ℝ) + smax) * Real.log (N₂ : ℝ) ≤ Λ₀ * Real.log q := by
    have h1 : (j : ℝ) + smax ≤ ((j + 2 * smax : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg smax : (0 : ℝ) ≤ smax)]
    have := mul_le_mul_of_nonneg_right h1 hlogN
    linarith
  have hLv := SieveLeafSplit.tree_leaves_le3 ha' hokL hokL₂ Ω S₀ (Isplit S₁ eIn₁) hE hw2 hwz hz₀ hsmax (by omega)
    (by nlinarith) hΛ₁ hc hlz hlE hΛA hX hN hreg' (fun s hs => by
      have hcl : ∀ C ∈ SieveP6Tree.leafCmps Ω S₀ ((A : ℝ) + 1) w z₀ s, C.c 0 ≤ Λ₁ * Real.log q :=
        fun C hC => SieveP6TreeLeaves.leafCmps_c_le (X := (q : ℝ) ^ (L - 1 - δ')) hBnn hc hlz hlE hw1 hX C
          (List.mem_append_left _ hC)
      have hlen' : (SieveP6Tree.leafCmps Ω S₀ ((A : ℝ) + 1) w z₀ s).length + 3 ≤ J₀E := by
        have h1 := length_Pblock_le j s (w : ℝ) (z₀ : ℝ)
        have h2 : s * s + 2 * s ≤ smax * smax + 2 * smax := by nlinarith
        simp only [SieveP6Tree.leafCmps, List.length_append, List.length_map, List.length_cons, List.length_nil]
        nlinarith
      exact SieveLeafFam3.cases3_of_bounds hokE _ (Isplit S₁ eIn₁ s) (by omega) hlen' hΛ₁ hcl hX
        (fun x hprime hholds => by
          have hx1 : ∀ i, 1 ≤ x i := fun i => (hprime i).one_lt.le
          obtain ⟨hΩ1, ⟨-, hblk⟩, halive⟩ := (leafCmps_holds Ω S₀ hE hw0 hz0 hx1).1 hholds
          obtain ⟨-, hz, hbox, hAc⟩ := hreg _ (fun i => hprime _) hΩ1
          rw [prod_idxAll] at halive
          have hcpos : 0 < ∏ i ∈ S₀, (x (Fin.castAdd s i) : ℝ) :=
            Finset.prod_pos fun i _ => by exact_mod_cast hx1 _
          have hy : ∏ u, (x (Fin.natAdd j u) : ℝ) ≤ 4 * (q : ℝ) ^ T := by
            have h1 : (∏ i ∈ S₀, (x (Fin.castAdd s i) : ℝ)) * ∏ u, (x (Fin.natAdd j u) : ℝ) <
                (∏ i ∈ S₀, (x (Fin.castAdd s i) : ℝ)) * (4 * (q : ℝ) ^ t) := by
              calc _ < (A : ℝ) + 1 := halive
                _ ≤ 4 * (q : ℝ) ^ t * ∏ i ∈ S₀, (x (Fin.castAdd s i) : ℝ) := hAc
                _ = _ := by ring
            exact (lt_of_mul_lt_mul_left h1 hcpos.le).le.trans htT
          obtain ⟨hI, hIc⟩ := leaf_blocks_le S₁ eIn₁ hx1 hq0 hi hbox hy
          obtain ⟨hI', hIc'⟩ := blocks4 hq0 _ x S₁ eIn₁ hi hI hIc
          refine ⟨fun i => ?_, hI', hIc'⟩
          induction i using Fin.addCases with
          | left i => exact hwz.trans (hz i)
          | right u => exact_mod_cast (hblk u).2)
        hwpow hpA hpAΛ hth hthΛ hszA₁ hszA₂ hszB₁ hszB₂ hAE hBE hArE hBrE) hC₀ hC hk hk1 hkC
    ((primesIco w z₀).card + 1)
  rw [← hMcdef, ← hel] at hLv
  -- the stops of the first tree, each by the tree below its last prime
  have hSt : ‖∑ s ∈ range ((primesIco w z₀).card + 1), (-1 : ℂ) ^ (s + 1) *
      ∑ x ∈ RTg (j + (s + 1)) N₂ (stopCmps Ω S₀ ((A : ℝ) + 1) w z₀ s),
        ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ N₂,
          dw q a' n * (if (∏ i, x i) ∣ n ∧ rough (x (Fin.natAdd j (Fin.last s))) n then 1 else 0)‖ ≤
      Mc * (((∑ rt ∈ RTg j N₂ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) * ∏ p ∈ primesIco w z₀, (1 + 1 / (p : ℝ))) * PN) +
        smax * (smax * el + smax * ec) := by
    refine (SieveP6TreeLeaves.norm_sum_sizes_le' (smax := smax)
      (b := fun s => Mc * ((∑ x ∈ RTg (j + (s + 1)) N₂ (stopCmps Ω S₀ ((A : ℝ) + 1) w z₀ s),
        1 / ((∏ i, x i : ℕ) : ℝ)) * PN) + (smax * el + smax * ec))
      (fun s => by simp) (fun s => add_nonneg (mul_nonneg hMc (mul_nonneg
        (Finset.sum_nonneg fun x _ => by positivity) hPN0))
        (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hel0) (mul_nonneg (Nat.cast_nonneg _) hec0)))
      (fun s hs => ?_) (fun s hs => ?_)).trans ?_
    · have hss : (s + 1) * (s + 1) + 2 * (s + 1) ≤ smax * smax + 2 * smax := by nlinarith
      have hlen1 : (stopCmps Ω S₀ ((A : ℝ) + 1) (w : ℝ) (z₀ : ℝ) s).length ≤
          Ω.length + smax * smax + 2 * smax + 2 := by
        have h1 := length_Pblock_le j (s + 1) (w : ℝ) (z₀ : ℝ)
        simp only [stopCmps, List.length_append, List.length_map, List.length_cons, List.length_nil]
        omega
      have hΛs : Λ₁ * Real.log q + ((j + s + 1 + smax : ℕ) : ℝ) * Real.log (N₂ : ℝ) ≤ Λ₀ * Real.log q := by
        have h1 : ((j + s + 1 + smax : ℕ) : ℝ) ≤ ((j + 2 * smax : ℕ) : ℝ) := by exact_mod_cast (by omega)
        have := mul_le_mul_of_nonneg_right h1 hlogN
        linarith
      have hcS : ∀ C ∈ stopCmps Ω S₀ ((A : ℝ) + 1) (w : ℝ) (z₀ : ℝ) s, C.c 0 ≤ Λ₁ * Real.log q := by
        intro C hC
        simp only [stopCmps, List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hC
        rcases hC with (⟨C', hC', rfl⟩ | hC) | rfl | rfl
        · exact hc C' hC'
        · exact Pblock_c_le (j := j) (s := s + 1) hBnn hlz hw1 C hC
        · exact hlE
        · show -Real.log ((A : ℝ) + 1) ≤ Λ₁ * Real.log q
          have : 0 ≤ Real.log ((A : ℝ) + 1) :=
            Real.log_nonneg (by linarith [(Nat.cast_nonneg A : (0 : ℝ) ≤ A)])
          linarith
      have H := last_pattern_le3 ha' hokL hokL₂ hokC (k' := j + s) (stopCmps Ω S₀ ((A : ℝ) + 1) w z₀ s)
        (idxAll S₀ (s + 1)) (fun sB => Isplit (Isplit S₁ eIn₁ (s + 1)) eIn₁ sB) (zb := z₀) hw2 hwY hArB hAr
        hsmr (by omega) (by omega) (by omega) (by omega) hΛ₁ hcS
        hlZ hlA hΛs hX hN
        (fun x hx hΩ => by
          have hx1 : ∀ i, 1 ≤ x i := fun i => (hx i).one_lt.le
          obtain ⟨hΩ1, ⟨hanti, hblk⟩, hlo, hhi⟩ := (stopCmps_holds Ω S₀ hE hw0 hz0 hx1).1 hΩ
          obtain ⟨ha, hz, -, -⟩ := hreg _ (fun i => hx _) hΩ1
          have hcast : ∀ I : Finset (Fin (j + (s + 1))), ((∏ i ∈ I, x i : ℕ) : ℝ) = ∏ i ∈ I, (x i : ℝ) :=
            fun I => Nat.cast_prod _ _
          have hent : ∀ i : Fin (j + (s + 1)), w ≤ x i := fun i => by
            induction i using Fin.addCases with
            | left i => exact hwz.trans (hz i)
            | right u => exact_mod_cast (hblk u).2
          have hlastb : x (Fin.natAdd j (Fin.last s)) ≤ z₀ := by
            have h1 : (x (Fin.natAdd j (Fin.last s)) : ℝ) < z₀ := (hblk (Fin.last s)).1
            have h2 : x (Fin.natAdd j (Fin.last s)) < z₀ := by exact_mod_cast h1
            omega
          refine ⟨strictAnti_chain (j := j) (t := s + 1) ha hanti (fun i => by exact_mod_cast hz i)
            (fun u => (hblk u).1), hent, hlastb, ?_, ?_⟩
          · have : (A : ℝ) + 1 ≤ ((∏ i ∈ idxAll S₀ (s + 1), x i : ℕ) : ℝ) := by rw [hcast]; exact hhi
            have : A + 1 ≤ ∏ i ∈ idxAll S₀ (s + 1), x i := by exact_mod_cast this
            exact Nat.lt_of_succ_le this
          · have hlast : (x (Fin.natAdd j (Fin.last s)) : ℝ) < z₀ := (hblk (Fin.last s)).1
            have hpos : (0 : ℝ) ≤ ∏ i ∈ idxInit S₀ s, (x i : ℝ) :=
              Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
            have h1 : ∏ i ∈ idxAll S₀ (s + 1), (x i : ℝ) < ((A : ℝ) + 1) * z₀ := by
              rw [prod_idxAll_succ]
              calc (∏ i ∈ idxInit S₀ s, (x i : ℝ)) * x (Fin.natAdd j (Fin.last s))
                  ≤ (∏ i ∈ idxInit S₀ s, (x i : ℝ)) * z₀ := mul_le_mul_of_nonneg_left hlast.le hpos
                _ < ((A : ℝ) + 1) * z₀ := mul_lt_mul_of_pos_right hlo hz0
            have h2 : (((A + 1) * z₀ : ℕ) : ℝ) ≤ B := by exact_mod_cast hAB
            push_cast at h2
            have h3 : ((∏ i ∈ idxAll S₀ (s + 1), x i : ℕ) : ℝ) < B + 1 := by rw [hcast]; linarith
            have : ∏ i ∈ idxAll S₀ (s + 1), x i < B + 1 := by exact_mod_cast h3
            exact Nat.lt_succ_iff.1 this)
        (fun sB hsB => by
          have hcl := leafCmpsL_c_le (k' := j + s) (Ω := stopCmps Ω S₀ ((A : ℝ) + 1) (w : ℝ) (z₀ : ℝ) s)
            (E := (Ar : ℝ) + 1) (w := (w : ℝ)) (Z := ((N₂ + 1 : ℕ) : ℝ)) (s := sB) hBnn hcS hlZ hlA hw1
          have hlen' : (leafCmpsL (stopCmps Ω S₀ ((A : ℝ) + 1) (w : ℝ) (z₀ : ℝ) s) ((Ar : ℝ) + 1) (w : ℝ)
              ((N₂ + 1 : ℕ) : ℝ) sB).length + 3 ≤ J₀E := by
            have h1 := length_leafCmpsL_le (stopCmps Ω S₀ ((A : ℝ) + 1) (w : ℝ) (z₀ : ℝ) s) ((Ar : ℝ) + 1) (w : ℝ)
              ((N₂ + 1 : ℕ) : ℝ) sB
            have h2 : sB * sB + 3 * sB ≤ smax * smax + 3 * smax := by nlinarith
            omega
          exact SieveLeafFam3.cases3_of_bounds hokE _ (Isplit (Isplit S₁ eIn₁ (s + 1)) eIn₁ sB) (by omega) hlen'
            hΛ₁ hcl hX (fun x hprime hholds => by
            have hx1 : ∀ i, 1 ≤ x i := fun i => (hprime i).one_lt.le
            obtain ⟨⟨hΩs, ⟨-, hblk2⟩, hlt2⟩, -⟩ :=
              (leafCmpsL_holds (k' := j + s) (stopCmps Ω S₀ ((A : ℝ) + 1) w z₀ s) hEB hw0 hZ0 hx1).1 hholds
            have hx1' : ∀ i : Fin (j + (s + 1)), 1 ≤ x (Fin.castAdd sB i) := fun i => hx1 _
            obtain ⟨hΩ1, ⟨-, hblk1⟩, hlo, -⟩ := (stopCmps_holds Ω S₀ hE hw0 hz0 hx1').1 hΩs
            obtain ⟨-, hz, hbox, hAc⟩ := hreg _ (fun i => hprime _) hΩ1
            rw [prod_idxInit] at hlo
            have hcpos : 0 < ∏ i ∈ S₀, (x (Fin.castAdd sB (Fin.castAdd (s + 1) i)) : ℝ) :=
              Finset.prod_pos fun i _ => by exact_mod_cast hx1 _
            have hy' : ∏ u : Fin s, (x (Fin.castAdd sB (Fin.natAdd j u.castSucc)) : ℝ) ≤ 4 * (q : ℝ) ^ t := by
              have h1 : (∏ i ∈ S₀, (x (Fin.castAdd sB (Fin.castAdd (s + 1) i)) : ℝ)) *
                  ∏ u : Fin s, (x (Fin.castAdd sB (Fin.natAdd j u.castSucc)) : ℝ) <
                  (∏ i ∈ S₀, (x (Fin.castAdd sB (Fin.castAdd (s + 1) i)) : ℝ)) * (4 * (q : ℝ) ^ t) := by
                calc _ < (A : ℝ) + 1 := hlo
                  _ ≤ 4 * (q : ℝ) ^ t * ∏ i ∈ S₀, (x (Fin.castAdd sB (Fin.castAdd (s + 1) i)) : ℝ) := hAc
                  _ = _ := by ring
              exact (lt_of_mul_lt_mul_left h1 hcpos.le).le
            have hlast : (x (Fin.castAdd sB (Fin.natAdd j (Fin.last s))) : ℝ) ≤ z₀ := (hblk1 (Fin.last s)).1.le
            have hy1 : ∏ u : Fin (s + 1), (x (Fin.castAdd sB (Fin.natAdd j u)) : ℝ) ≤ 4 * (q : ℝ) ^ t * z₀ := by
              rw [Fin.prod_univ_castSucc]
              exact mul_le_mul hy' hlast (Nat.cast_nonneg _) (by positivity)
            have hy2 : ∏ v : Fin sB, (x (Fin.natAdd (j + (s + 1)) v) : ℝ) ≤ (Ar : ℝ) + 1 := hlt2.le
            have hy : (∏ u : Fin (s + 1), (x (Fin.castAdd sB (Fin.natAdd j u)) : ℝ)) *
                ∏ v : Fin sB, (x (Fin.natAdd (j + (s + 1)) v) : ℝ) ≤ 4 * (q : ℝ) ^ T :=
              (mul_le_mul hy1 hy2 (Finset.prod_nonneg fun v _ => Nat.cast_nonneg _) (by positivity)).trans hT
            obtain ⟨hI, hIc⟩ := leaf_blocks2_le S₁ eIn₁ (s₁ := s + 1) (s₂ := sB) hx1 hq0 hi hbox hy
            obtain ⟨hI', hIc'⟩ := blocks4 hq0 _ x S₁ eIn₁ hi hI hIc
            refine ⟨fun i => ?_, hI', hIc'⟩
            induction i using Fin.addCases with
            | left i =>
              induction i using Fin.addCases with
              | left i => exact hwz.trans (hz i)
              | right u => exact_mod_cast (hblk1 u).2
            | right v => exact_mod_cast (hblk2 v).2)
            hwpow hpA hpAΛ hth hthΛ hszA₁ hszA₂ hszB₁ hszB₂ hAE hBE hArE hBrE)
        hC₀ hC hk hk1 hkC
      rw [← hMcdef, ← hel, ← hec, ← hPN] at H
      exact H.trans (le_of_eq (add_assoc _ _ _))
    · refine Finset.sum_eq_zero fun x hx => ?_
      exfalso
      have hx1 := one_le_of_mem_RTg hx
      obtain ⟨-, ⟨-, hblk⟩, hlo, -⟩ := (stopCmps_holds Ω S₀ hE hw0 hz0 hx1).1 (Finset.mem_filter.1 hx).2
      rw [prod_idxInit] at hlo
      have h1 : (1 : ℝ) ≤ ∏ i ∈ S₀, (x (Fin.castAdd (s + 1) i) : ℝ) :=
        Finset.one_le_prod₀ fun i _ => by exact_mod_cast hx1 _
      have h2 : (w : ℝ) ^ s ≤ ∏ u : Fin s, (x (Fin.natAdd j u.castSucc) : ℝ) := by
        calc (w : ℝ) ^ s = ∏ _u : Fin s, (w : ℝ) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hw0.le) fun u _ => (hblk u.castSucc).2
      have h3 : (w : ℝ) ^ smax ≤ (w : ℝ) ^ s := pow_le_pow_right₀ hw1 hs
      have h4 : 0 ≤ ∏ u : Fin s, (x (Fin.natAdd j u.castSucc) : ℝ) :=
        Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
      have h5 := mul_le_mul h1 (le_refl (∏ u : Fin s, (x (Fin.natAdd j u.castSucc) : ℝ))) h4 (by linarith)
      linarith
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      have hsub := sum_stops_inv_le Ω S₀ ((A : ℝ) + 1) (Y := N₂) (by omega : 1 ≤ w) hwz hz₀ smax
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsub hPN0) hMc
      linarith
  have e : Mc * (((∑ rt ∈ RTg j N₂ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) * ∏ p ∈ primesIco w z₀, (1 + 1 / (p : ℝ))) *
      (1 + PN)) = Mc * ((∑ rt ∈ RTg j N₂ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
        ∏ p ∈ primesIco w z₀, (1 + 1 / (p : ℝ))) +
      Mc * (((∑ rt ∈ RTg j N₂ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) * ∏ p ∈ primesIco w z₀, (1 + 1 / (p : ℝ))) * PN) := by
    ring
  rw [e]
  have e2 : ((smax : ℝ) + smax * smax) * el + (smax : ℝ) * smax * ec =
      smax * el + smax * (smax * el + smax * ec) := by ring
  linarith

end SieveFillE
