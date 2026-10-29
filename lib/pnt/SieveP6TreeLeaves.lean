/-
# Proposition 6 with the bilinear estimate: the leaves of the tree

Plain statements. `GCmp`, `RTg`, `eS` and `merge` are `SieveChain`'s; `DT` is `SieveP6Split`'s; `leafCmps` is
`SieveP6Tree`'s; `rough z n` and `primesIco w z` are `SieveTree`'s; `zeta`, `rem` and `Jw` are `SieveProp6`'s.
`N₁ = ⌊q^L⌋`, `N₂ = ⌊2q^L⌋` and `w = ⌈q^{εw}⌉`.

* `LeavesOK`, `leavesOK_of`: `SieveP6Leaves.leaves_chain` at `q`, for every pair of block sizes up to `K_max`.
* `large_leaves_le`: for a family of chains split into the blocks `S` and `Sᶜ`, with comparisons none of which is
  constant, forms at most `Λ₀ log q`, chains strictly decreasing with entries at least `w`, and the sizes of
  `leaves_chain`: the leaves total at most `ζ(k)(N₂ − N₁)/(φ(q) log w)·Σ 1/d + q^{L−δ}/φ(q)`.
* `small_leaves_le`: `SieveProp6.leaf_bound` at each chain of a set of tuples of primes at least `w ≥ 2`.
* `sum_leaves_inv_le`: over the leaves of a tree, `Σ 1/d ≤ (Σ_{rt} 1/r)∏_{p∈[w,z₀)}(1 + 1/p)`.
* `tree_leaves_le`: **the leaves of a tree.** The leaves with `∏x ≤ X = q^{L−1−δ'}` by `small_leaves_le`, at most
  `X·Σ 1/d` of them; the others, split into two blocks with the sizes of `leaves_chain`, by `large_leaves_le` after
  dropping constant comparisons. In all, `(2ζ(k)(N₂ − N₁)/(φ(q) log w) + 2·rem·X)(Σ_{rt} 1/r)∏_{p∈[w,z₀)}(1 + 1/p)`
  plus `s_max·q^{L−δ}/φ(q)`.

The file imports `SieveP6Split.lean` and `SieveP6Leaves.lean`.
-/
import SieveP6Split
import SieveP6Leaves

open Real Finset SieveFamily SieveTree SieveChain SieveP6Chain SieveP6Split

namespace SieveP6TreeLeaves

open Classical

/-! ### The large leaves for every pair of block sizes up to a bound -/

/-- **The large leaves for every pair of block sizes up to `K_max`**: the conclusion of
`SieveP6Leaves.leaves_chain` at `q` with `δ`, for every `K₁, K₂ ≤ K_max`. -/
def LeavesOK (q : ℕ) (a' : ZMod q) (L a b δ' εw Λ₀ C₀ δ : ℝ) (k J₀ Kmax : ℕ) : Prop :=
  ∀ K₁ K₂ : ℕ, K₁ ≤ Kmax → K₂ ≤ Kmax →
  ∀ (Y₁ : Finset (Fin K₁ → ℕ)) (Y₂ : Finset (Fin K₂ → ℕ)),
    (∀ y ∈ Y₁, StrictAnti y ∧ ∀ i, (y i).Prime ∧ ⌈(q : ℝ) ^ εw⌉₊ ≤ y i ∧ y i ≤ ⌊2 * (q : ℝ) ^ L⌋₊) →
    (∀ y ∈ Y₂, StrictAnti y ∧ ∀ i, (y i).Prime ∧ ⌈(q : ℝ) ^ εw⌉₊ ≤ y i ∧ y i ≤ ⌊2 * (q : ℝ) ^ L⌋₊) →
  ∀ {M : ℕ}, M ≤ J₀ → ∀ (cc : Fin M → ℝ) (e₁ : Fin M → Fin K₁ → ℝ) (e₂ : Fin M → Fin K₂ → ℝ)
    (Pr : Fin M → (Fin K₁ → ℕ) → (Fin K₂ → ℕ) → Prop),
    (∀ j y₁ y₂, (0 < cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i) → Pr j y₁ y₂) ∧
      (Pr j y₁ y₂ → 0 ≤ cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i))) →
    (∀ j, ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂,
      cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i) ≤ Λ₀ * Real.log q) →
    (∀ j, (∃ i, e₁ j i = 1 ∨ e₁ j i = -1) ∨ ∃ i, e₂ j i = 1 ∨ e₂ j i = -1) →
    (∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, (∀ j, Pr j y₁ y₂) →
      ((∏ i, y₁ i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
      ((∏ i, y₁ i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i, y₂ i : ℕ) : ℝ) ^ 2 ≤
        (q : ℝ) ^ (L - b) ∧
      (q : ℝ) ^ (L - 1 - δ') ≤ ((∏ i, y₁ i : ℕ) : ℝ) * ((∏ i, y₂ i : ℕ) : ℝ)) →
    ‖∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, if Pr j y₁ y₂ then (1 : ℂ) else 0) *
        ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊, dw q a' n *
          (if (∏ i, y₁ i) * (∏ i, y₂ i) ∣ n ∧ rough ⌈(q : ℝ) ^ εw⌉₊ n then 1 else 0)‖ ≤
      SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) *
        ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, if Pr j y₁ y₂ then (1 : ℝ) else 0) /
          (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ) +
      (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)

/-- `SieveP6Leaves.leaves_chain` for every pair of block sizes up to `K_max`. -/
theorem leavesOK_of {L : ℝ} (hL : 2 < L) {a b δ' εw Λ₀ : ℝ} (hδ' : 0 ≤ δ') (hab : δ' < a) (haL : a ≤ L - 2)
    (hb : 0 < b) (hbL : b ≤ L) (hεw : 0 < εw) (hΛ₀ : 0 ≤ Λ₀) (Kmax J₀ : ℕ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) {k : ℕ} (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) (hεwk : (2 * k + 4) * εw ≤ 1 / 16) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a' : ZMod q), IsUnit a' →
      LeavesOK q a' L a b δ' εw Λ₀ C₀ δ k J₀ Kmax := by
  have H := fun K₁ K₂ : ℕ =>
    SieveP6Leaves.leaves_chain hL hδ' hab haL hb hbL hεw hΛ₀ K₁ K₂ J₀ hC₀ hC hk hk1 hkC hεwk
  choose δf hδf q₀f hq₀f using H
  set P : Finset (ℕ × ℕ) := (range (Kmax + 1)) ×ˢ (range (Kmax + 1)) with hPdef
  have hP : P.Nonempty := ⟨(0, 0), by simp [hPdef]⟩
  refine ⟨P.inf' hP (fun p => δf p.1 p.2), (Finset.lt_inf'_iff hP).2 fun p _ => hδf p.1 p.2,
    P.sup (fun p => q₀f p.1 p.2), ?_⟩
  intro q _ hq a' ha' K₁ K₂ hK₁ hK₂ Y₁ Y₂ hY₁ hY₂ M hM cc e₁ e₂ Pr hPr hΛ hpiv hgeo
  have hmem : (K₁, K₂) ∈ P :=
    Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩
  have hq' : q₀f K₁ K₂ ≤ q := le_trans (Finset.le_sup (f := fun p : ℕ × ℕ => q₀f p.1 p.2) hmem) hq
  refine (hq₀f K₁ K₂ q hq' a' ha' Y₁ Y₂ hY₁ hY₂ hM cc e₁ e₂ Pr hPr hΛ hpiv hgeo).trans ?_
  have hδle : P.inf' hP (fun p => δf p.1 p.2) ≤ δf K₁ K₂ := Finset.inf'_le (fun p : ℕ × ℕ => δf p.1 p.2) hmem
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith))
    (by positivity))

/-! ### The large leaves of a family of chains -/

theorem prod_Sc {K : ℕ} (S : Finset (Fin K)) (f : Fin K → ℕ) : ∏ i ∈ Sᶜ, f i = ∏ v, f (eS S (Sum.inr v)) := by
  conv_lhs => rw [← Sᶜ.image_orderEmbOfFin_univ rfl]
  rw [Finset.prod_image (fun u _ v _ h => (Sᶜ.orderEmbOfFin rfl).injective h)]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [show eS S (Sum.inr v) = Sᶜ.orderEmbOfFin rfl v from finSumEquivOfFinset_inr rfl rfl v]

/-- **The large leaves of a family of chains**, split into the blocks `S` and `Sᶜ`: `LeavesOK` with the family's
comparisons, none of them constant, their forms at most `Λ₀ log q`, the chains strictly decreasing with entries at least
`w`, and the sizes of `leaves_chain` at every chain. -/
theorem large_leaves_le {q : ℕ} {a' : ZMod q} {L a b δ' εw Λ₀ C₀ δ : ℝ} {k J₀ Kmax : ℕ}
    (hok : LeavesOK q a' L a b δ' εw Λ₀ C₀ δ k J₀ Kmax) {K : ℕ} (S : Finset (Fin K)) (hK₁ : S.card ≤ Kmax)
    (hK₂ : Sᶜ.card ≤ Kmax) (Ω : List (GCmp K)) (hlen : Ω.length ≤ J₀) (hnz : ∀ C ∈ Ω, ∃ i, C.e i ≠ 0)
    (hform : ∀ C ∈ Ω, ∀ x : Fin K → ℕ, (∀ i, 1 ≤ x i ∧ x i ≤ ⌊2 * (q : ℝ) ^ L⌋₊) →
      C.form 0 x ≤ Λ₀ * Real.log q)
    (hreg : ∀ x ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω, StrictAnti x ∧ ∀ i, ⌈(q : ℝ) ^ εw⌉₊ ≤ x i)
    (hgeo : ∀ x ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω,
      ((∏ i ∈ S, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
      ((∏ i ∈ S, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ Sᶜ, x i : ℕ) : ℝ) ^ 2 ≤
        (q : ℝ) ^ (L - b) ∧
      (q : ℝ) ^ (L - 1 - δ') ≤ ((∏ i, x i : ℕ) : ℝ)) :
    ‖∑ x ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊, dw q a' n *
        (if (∏ i, x i) ∣ n ∧ rough ⌈(q : ℝ) ^ εw⌉₊ n then 1 else 0)‖ ≤
      SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) *
        ∑ x ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, x i : ℕ) : ℝ) +
      (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  set N₂ := ⌊2 * (q : ℝ) ^ L⌋₊ with hN₂
  set w := ⌈(q : ℝ) ^ εw⌉₊ with hw
  have hprod : ∀ (y₁ : Fin S.card → ℕ) (y₂ : Fin Sᶜ.card → ℕ), ∏ i, merge S y₁ y₂ i = (∏ i, y₁ i) * ∏ i, y₂ i :=
    fun y₁ y₂ => by rw [prod_split_nat (S := S)]; simp only [merge_inl, merge_inr]
  have hL : ∑ x ∈ RTg K N₂ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ N₂, dw q a' n *
        (if (∏ i, x i) ∣ n ∧ rough w n then 1 else 0) =
      ∑ y₁ ∈ DT S.card w N₂, ∑ y₂ ∈ DT Sᶜ.card w N₂,
        (∏ j : Fin Ω.length, if (Ω.get j).holds 0 (merge S y₁ y₂) then (1 : ℂ) else 0) *
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ N₂, dw q a' n *
            (if (∏ i, y₁ i) * (∏ i, y₂ i) ∣ n ∧ rough w n then 1 else 0) := by
    rw [sum_RTg_split S Ω hreg]
    refine Finset.sum_congr rfl fun y₁ _ => Finset.sum_congr rfl fun y₂ _ => ?_
    rw [ite_forall_eq_prod (fun C => C.holds 0 (merge S y₁ y₂)) Ω, hprod]
  have hR : ∑ x ∈ RTg K N₂ Ω, 1 / ((∏ i, x i : ℕ) : ℝ) =
      ∑ y₁ ∈ DT S.card w N₂, ∑ y₂ ∈ DT Sᶜ.card w N₂,
        (∏ j : Fin Ω.length, if (Ω.get j).holds 0 (merge S y₁ y₂) then (1 : ℝ) else 0) /
          (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ) := by
    rw [sum_RTg_split S Ω hreg]
    refine Finset.sum_congr rfl fun y₁ _ => Finset.sum_congr rfl fun y₂ _ => ?_
    rw [ite_forall_eq_prod (fun C => C.holds 0 (merge S y₁ y₂)) Ω, hprod, mul_one_div]
  rw [hL, hR]
  have hDT : ∀ {n : ℕ}, ∀ y ∈ DT n w N₂, StrictAnti y ∧ ∀ i, (y i).Prime ∧ w ≤ y i ∧ y i ≤ N₂ :=
    fun y hy => mem_DT.1 hy
  have hmerge1 : ∀ y₁ ∈ DT S.card w N₂, ∀ y₂ ∈ DT Sᶜ.card w N₂, ∀ i, (merge S y₁ y₂ i).Prime ∧
      1 ≤ merge S y₁ y₂ i ∧ merge S y₁ y₂ i ≤ N₂ := by
    intro y₁ hy₁ y₂ hy₂ i
    obtain ⟨t, rfl⟩ := (eS S).surjective i
    rcases t with u | v
    · rw [merge_inl]
      obtain ⟨hp, -, hY⟩ := (hDT y₁ hy₁).2 u
      exact ⟨hp, hp.one_lt.le, hY⟩
    · rw [merge_inr]
      obtain ⟨hp, -, hY⟩ := (hDT y₂ hy₂).2 v
      exact ⟨hp, hp.one_lt.le, hY⟩
  refine hok S.card Sᶜ.card hK₁ hK₂ (DT S.card w N₂) (DT Sᶜ.card w N₂) (fun y hy => hDT y hy)
    (fun y hy => hDT y hy) hlen (fun j => (Ω.get j).c 0) (fun j u => (Ω.get j).e (eS S (Sum.inl u)))
    (fun j v => (Ω.get j).e (eS S (Sum.inr v))) (fun j y₁ y₂ => (Ω.get j).holds 0 (merge S y₁ y₂)) ?_ ?_ ?_ ?_
  · intro j y₁ y₂
    rw [← form_merge]
    unfold GCmp.holds
    split_ifs
    · exact ⟨id, le_of_lt⟩
    · exact ⟨le_of_lt, id⟩
  · intro j y₁ hy₁ y₂ hy₂
    rw [← form_merge]
    exact hform _ (List.get_mem Ω j) _ fun i => ⟨(hmerge1 y₁ hy₁ y₂ hy₂ i).2.1, (hmerge1 y₁ hy₁ y₂ hy₂ i).2.2⟩
  · intro j
    obtain ⟨i, hi⟩ := hnz _ (List.get_mem Ω j)
    have hpm : (Ω.get j).e i = 1 ∨ (Ω.get j).e i = -1 := by
      rcases (Ω.get j).he i with h | h | h
      · exact Or.inr h
      · exact absurd h hi
      · exact Or.inl h
    obtain ⟨t, rfl⟩ := (eS S).surjective i
    rcases t with u | v
    · exact Or.inl ⟨u, hpm⟩
    · exact Or.inr ⟨v, hpm⟩
  · intro y₁ hy₁ y₂ hy₂ hP
    have hΩ : ∀ C ∈ Ω, C.holds 0 (merge S y₁ y₂) := forall_mem_iff_get.2 hP
    have hmem : merge S y₁ y₂ ∈ RTg K N₂ Ω := Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i =>
      SieveTypeIIU.mem_primesLe.2 ⟨(hmerge1 y₁ hy₁ y₂ hy₂ i).2.2, (hmerge1 y₁ hy₁ y₂ hy₂ i).1⟩, hΩ⟩
    obtain ⟨h1, h2, h3⟩ := hgeo _ hmem
    rw [prod_S] at h1
    rw [prod_S, prod_Sc] at h2
    simp only [merge_inl, merge_inr] at h1 h2
    rw [hprod] at h3
    push_cast at h1 h2 h3 ⊢
    exact ⟨h1, h2, h3⟩

/-! ### The small leaves, and the sums of `1/d` over the leaves -/

/-- **The small leaves**: `SieveProp6.leaf_bound` at each chain of a set `F` of tuples of primes at least `w ≥ 2`. -/
theorem small_leaves_le {q : ℕ} [NeZero q] {a' : ZMod q} (ha' : IsUnit a') {K : ℕ} (F : Finset (Fin K → ℕ))
    {w J k : ℕ} (hw : 2 ≤ w) (hF : ∀ x ∈ F, ∀ i, (x i).Prime ∧ w ≤ x i) (hJ : (w : ℝ) ^ ((1 / 2 : ℝ) ^ J) ≤ 2)
    {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) :
    ‖∑ x ∈ F, ∑ n ∈ Finset.Ioc N₁ N₂, dw q a' n * (if (∏ i, x i) ∣ n ∧ rough w n then 1 else 0)‖ ≤
      2 * SieveProp6.zeta C₀ k * (((N₂ : ℝ) - N₁) / (q.totient * Real.log w)) *
          ∑ x ∈ F, 1 / ((∏ i, x i : ℕ) : ℝ) +
        2 * SieveProp6.rem w J k * F.card := by
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ x ∈ F, ‖∑ n ∈ Finset.Ioc N₁ N₂, dw q a' n * (if (∏ i, x i) ∣ n ∧ rough w n then 1 else 0)‖ ≤
      2 * SieveProp6.zeta C₀ k * (((N₂ : ℝ) - N₁) / ((∏ i, x i : ℕ) * (q.totient * Real.log w))) +
        2 * SieveProp6.rem w J k := by
    intro x hx
    have hp := fun i => (hF x hx i).1
    refine SieveProp6.leaf_bound ha' (by have := SieveP6Leaves.one_le_prod hp; omega) hw (fun p hpp hd => ?_) hJ hN
      hC₀ hC hk hk1 hkC
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).1 hd
    rw [(Nat.prime_dvd_prime_iff_eq hpp (hp i)).1 hi]
    exact (hF x hx i).2
  refine (Finset.sum_le_sum h).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    ring
  · ring

/-- Over the sizes below `M`, the `s`-subsets of `T` are some of its subsets. -/
theorem sum_sizes_le_powerset (T : Finset ℕ) (M : ℕ) (h : Finset ℕ → ℝ) (hh : ∀ P, 0 ≤ h P) :
    ∑ s ∈ range M, ∑ P ∈ T.powersetCard s, h P ≤ ∑ P ∈ T.powerset, h P := by
  rw [Finset.sum_powerset]
  rcases le_total M (T.card + 1) with hM | hM
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hM) fun s _ _ =>
      Finset.sum_nonneg fun P _ => hh P
  · rw [← Finset.sum_range_add_sum_Ico _ hM]
    have hz : ∑ s ∈ Finset.Ico (T.card + 1) M, ∑ P ∈ T.powersetCard s, h P = 0 := Finset.sum_eq_zero fun s hs => by
      rw [Finset.powersetCard_eq_empty.2 (by have := (Finset.mem_Ico.1 hs).1; omega), Finset.sum_empty]
    rw [hz, add_zero]

/-- **The sums of `1/d` over the leaves**: at most `(Σ_{rt} 1/r)∏_{p∈[w,z₀)}(1 + 1/p)`. -/
theorem sum_leaves_inv_le {j : ℕ} (Ω : List (GCmp j)) (S₀ : Finset (Fin j)) (E : ℝ) {Y w z₀ : ℕ} (hw : 1 ≤ w)
    (hwz : w ≤ z₀) (hz₀ : z₀ ≤ Y + 1) (M : ℕ) :
    ∑ s ∈ range M, ∑ x ∈ RTg (j + s) Y (SieveP6Tree.leafCmps Ω S₀ E w z₀ s), 1 / ((∏ i, x i : ℕ) : ℝ) ≤
      (∑ rt ∈ RTg j Y Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) * ∏ p ∈ primesIco w z₀, (1 + 1 / (p : ℝ)) := by
  rw [← SieveProp6.sum_leaves_inv]
  have hstep : ∀ s, ∑ x ∈ RTg (j + s) Y (SieveP6Tree.leafCmps Ω S₀ E w z₀ s), 1 / ((∏ i, x i : ℕ) : ℝ) ≤
      ∑ rt ∈ RTg j Y Ω, ∑ P ∈ (primesIco w z₀).powersetCard s, 1 / (((∏ i, rt i) * ∏ p ∈ P, p : ℕ) : ℝ) := by
    intro s
    rw [SieveP6Tree.leafCmps, SieveP6Tree.RTg_append (j + s) Y (Ω.map liftChain ++ Pblock j s w z₀)]
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun x _ _ => by positivity).trans
      (le_of_eq ?_)
    have e : ∀ x : Fin (j + s) → ℕ, 1 / ((∏ i, x i : ℕ) : ℝ) =
        1 / (((∏ i, x (Fin.castAdd s i)) * ∏ u, x (Fin.natAdd j u) : ℕ) : ℝ) := fun x => by
      rw [← Fin.prod_univ_add]
    rw [Finset.sum_congr rfl fun x _ => e x,
      ← sum_chain j s Ω hw hwz hz₀ (fun rt y => 1 / (((∏ i, rt i) * ∏ u, y u : ℕ) : ℝ))]
    refine Finset.sum_congr rfl fun rt _ => ?_
    rw [sum_powersetCard_desc]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Finset.prod_image fun u _ v _ h => (Finset.mem_filter.1 hy).2.injective h]
  refine (Finset.sum_le_sum fun s _ => hstep s).trans ?_
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun rt _ => sum_sizes_le_powerset _ M _ fun P => by positivity

/-! ### The leaves of a tree -/

/-- The `m`-parts of the comparisons of a leaf, and of the threshold `X < ∏x`, are at most `Λ₁ log q`. -/
theorem leafCmps_c_le {j : ℕ} {Ω : List (GCmp j)} {S₀ : Finset (Fin j)} {E w z₀ X B : ℝ} {s : ℕ} (hB : 0 ≤ B)
    (hc : ∀ C ∈ Ω, C.c 0 ≤ B) (hz : Real.log z₀ ≤ B) (hE : Real.log E ≤ B) (hw : 1 ≤ w) (hX : 1 ≤ X) :
    ∀ C ∈ SieveP6Tree.leafCmps Ω S₀ E w z₀ s ++ [gDown univ X true], C.c 0 ≤ B := by
  intro C hC
  simp only [SieveP6Tree.leafCmps, List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff,
    or_false] at hC
  rcases hC with ((⟨C', hC', rfl⟩ | hC) | rfl) | rfl
  · exact hc C' hC'
  · exact SieveP6Tree.Pblock_c_le hB hz hw C hC
  · exact hE
  · show -Real.log X ≤ B
    have := Real.log_nonneg hX
    linarith

/-- The leaves above the threshold `X > 0` are the chains with the comparison `X < ∏x` added. -/
theorem filter_large_eq {K Y : ℕ} (Ω : List (GCmp K)) {X : ℝ} (hX : 0 < X) :
    (RTg K Y Ω).filter (fun x => ¬ ((∏ i, x i : ℕ) : ℝ) ≤ X) = RTg K Y (Ω ++ [gDown univ X true]) := by
  rw [SieveP6Tree.RTg_append]
  refine Finset.filter_congr fun x hx => ?_
  have hx1 := SieveP6Tree.one_le_of_mem_RTg hx
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true,
    gDown_holds _ hX true 0 hx1, ite_true, not_le]
  push_cast
  rfl

/-- A sum over sizes, with signs of norm at most one, whose terms are at most `b_s ≥ 0` below `s_max` and vanish from
`s_max` on, is at most `Σ_{s < s_max} b_s`. -/
theorem norm_sum_sizes_le' {N smax : ℕ} {ε X : ℕ → ℂ} {b : ℕ → ℝ} (hε : ∀ s, ‖ε s‖ ≤ 1) (hb : ∀ s, 0 ≤ b s)
    (hX : ∀ s < smax, ‖X s‖ ≤ b s) (h0 : ∀ s, smax ≤ s → X s = 0) :
    ‖∑ s ∈ range N, ε s * X s‖ ≤ ∑ s ∈ range smax, b s := by
  have hterm : ∀ s ∈ range N, ‖ε s * X s‖ ≤ if s < smax then b s else 0 := by
    intro s _
    rw [norm_mul]
    by_cases hs : s < smax
    · rw [ite_eq_left hs]
      calc ‖ε s‖ * ‖X s‖ ≤ 1 * b s := mul_le_mul (hε s) (hX s hs) (norm_nonneg _) zero_le_one
        _ = b s := one_mul _
    · rw [ite_eq_right hs, h0 s (not_lt.1 hs), norm_zero, mul_zero]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.sum_filter]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun s hs => Finset.mem_range.2 (Finset.mem_filter.1 hs).2)
    fun s _ _ => hb s

/-- **The leaves of a tree.** At `w = ⌈q^{εw}⌉ ≥ 2`, with `J = Jw(w)` ranges, `w ≤ z₀ ≤ N₂ + 1`, the rule `E ≤ c∏P`
with `E ≤ w^{s_max}` and `j + s_max ≤ K_max`: for a family `RTg j N₂ Ω` of strictly decreasing tuples with entries at
least `z₀` (at most `J₀ − s_max² − 2s_max − 2` comparisons, with `m`-parts, `log z₀` and `log E` at most
`Λ₁ log q`, and `Λ₁ log q + (j + s_max) log N₂ ≤ Λ₀ log q`): split each leaf `x` of size `s` with `∏x > X = q^{L−1−δ'}`
into the blocks `I_s` and `I_sᶜ` with the sizes of `leaves_chain`. Then the leaves (with the signs `(−1)^s`) total at
most `(2ζ(k)(N₂ − N₁)/(φ(q) log w) + 2·rem·X)(Σ_{rt} 1/r)∏_{p∈[w,z₀)}(1 + 1/p) + s_max·q^{L−δ}/φ(q)`. -/
theorem tree_leaves_le {q : ℕ} [NeZero q] {a' : ZMod q} (ha' : IsUnit a') {L a b δ' εw Λ₀ Λ₁ C₀ δ : ℝ}
    {k J₀ Kmax : ℕ} (hok : LeavesOK q a' L a b δ' εw Λ₀ C₀ δ k J₀ Kmax) {j : ℕ} (Ω : List (GCmp j))
    (S₀ : Finset (Fin j)) (I : ∀ s, Finset (Fin (j + s))) {E : ℝ} (hE : 0 < E) {z₀ smax : ℕ}
    (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hwz : ⌈(q : ℝ) ^ εw⌉₊ ≤ z₀) (hz₀ : z₀ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1)
    (hsmax : E ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax) (hK : j + smax ≤ Kmax)
    (hlen : Ω.length + smax * smax + 2 * smax + 2 ≤ J₀) (hΛ₁ : 0 ≤ Λ₁)
    (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) (hlz : Real.log z₀ ≤ Λ₁ * Real.log q)
    (hlE : Real.log E ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + (j + smax) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hreg : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) → StrictAnti rt ∧ ∀ i, z₀ ≤ rt i)
    (hgeo : ∀ s < smax, ∀ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊
        (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s),
      (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) →
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ (I s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤
          (q : ℝ) ^ (L - b))
    (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) (N : ℕ) :
    ‖∑ s ∈ range N, (-1 : ℂ) ^ s *
        ∑ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s),
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
            dw q a' n * (if (∏ i, x i) ∣ n ∧ rough ⌈(q : ℝ) ^ εw⌉₊ n then 1 else 0)‖ ≤
      (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
          ((∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
            ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀, (1 + 1 / (p : ℝ))) +
        smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)) := by
  obtain ⟨hJw, -, -⟩ := SieveProp6.Jw_spec hw2
  have hw1 : 1 ≤ ⌈(q : ℝ) ^ εw⌉₊ := by omega
  have hw0 : (0 : ℝ) < ⌈(q : ℝ) ^ εw⌉₊ := by exact_mod_cast (by omega : 0 < ⌈(q : ℝ) ^ εw⌉₊)
  have hw1' : (1 : ℝ) ≤ ⌈(q : ℝ) ^ εw⌉₊ := by exact_mod_cast hw1
  have hz0 : (0 : ℝ) < z₀ := by exact_mod_cast (by omega : 0 < z₀)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have hlogw : 0 < Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := Real.log_pos (by exact_mod_cast hw2)
  have hNN : (0 : ℝ) ≤ (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊ := by
    have : (⌊(q : ℝ) ^ L⌋₊ : ℝ) ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := by exact_mod_cast hN
    linarith
  have hN₂1 : (1 : ℝ) ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := by exact_mod_cast (by omega : 1 ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
  have hlogN₂ : 0 ≤ Real.log (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) := Real.log_nonneg hN₂1
  have hζ0 := SieveProp6.zeta_nonneg hC₀ k
  have hrem0 := SieveProp6.rem_nonneg (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k
  have hX0 : (0 : ℝ) < (q : ℝ) ^ (L - 1 - δ') := by linarith
  have he0 : 0 ≤ (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by positivity
  -- the entries of a leaf
  have hleaf : ∀ s, ∀ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s),
      StrictAnti x ∧ ∀ i, (x i).Prime ∧ ⌈(q : ℝ) ^ εw⌉₊ ≤ x i := by
    intro s x hx
    have hx1 := SieveP6Tree.one_le_of_mem_RTg hx
    obtain ⟨hΩ1, ⟨hanti, hblk⟩, -⟩ :=
      (SieveP6Tree.leafCmps_holds Ω S₀ hE hw0 hz0 hx1).1 (Finset.mem_filter.1 hx).2
    have hprime : ∀ i, (x i).Prime := fun i =>
      (SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx).1 i)).2
    obtain ⟨ha, hz⟩ := hreg _ (fun i => hprime _) hΩ1
    refine ⟨SieveP6Tree.strictAnti_chain (j := j) (t := s) ha hanti (fun i => by exact_mod_cast hz i)
      (fun u => (hblk u).1), fun i => ⟨hprime i, ?_⟩⟩
    induction i using Fin.addCases with
    | left i => exact le_trans hwz (hz i)
    | right u => exact_mod_cast (hblk u).2
  refine (norm_sum_sizes_le' (smax := smax) (b := fun s => (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) -
      ⌊(q : ℝ) ^ L⌋₊) / (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
      ∑ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s),
        1 / ((∏ i, x i : ℕ) : ℝ) + (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ))
    (fun s => by simp) (fun s => by positivity) (fun s hs => ?_) (fun s hs => ?_)).trans ?_
  · obtain ⟨Zh, hZh⟩ : ∃ Zh, Zh = SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
        (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) := ⟨_, rfl⟩
    have hZh0 : 0 ≤ Zh := by rw [hZh]; positivity
    have hZ2 : 2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
        (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) = 2 * Zh := by rw [hZh]; ring
    obtain ⟨rm, hrm⟩ : ∃ rm, rm = SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k :=
      ⟨_, rfl⟩
    have hrm0 : 0 ≤ rm := by rw [hrm]; exact hrem0
    rw [hZ2, ← hrm]
    -- the small leaves and the large ones
    rw [← Finset.sum_filter_add_sum_filter_not (RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊
      (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s)) (fun x => ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ'))]
    rw [← Finset.sum_filter_add_sum_filter_not (RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊
      (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s)) (fun x => ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ'))
      (fun x => 1 / ((∏ i, x i : ℕ) : ℝ))]
    refine (norm_add_le _ _).trans ?_
    have hsm := small_leaves_le ha' ((RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊
      (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s)).filter
        (fun x => ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ'))) hw2
      (fun x hx => (hleaf s x (Finset.mem_filter.1 hx).1).2) hJw hN hC₀ hC hk hk1 hkC
    rw [hZ2, ← hrm] at hsm
    have hcard : (((RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s)).filter
        (fun x => ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ'))).card : ℝ) ≤
        (q : ℝ) ^ (L - 1 - δ') * ∑ x ∈ (RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊
          (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s)).filter
            (fun x => ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ')), 1 / ((∏ i, x i : ℕ) : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun x hx => ?_
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
      have hp : (0 : ℝ) < ((∏ i, x i : ℕ) : ℝ) := by
        have := SieveP6Leaves.one_le_prod fun i => ((hleaf s x hx1).2 i).1
        exact_mod_cast (by omega : 0 < ∏ i, x i)
      rw [mul_one_div, le_div_iff₀ hp]
      push_cast at hx2 ⊢
      linarith
    have hlg : ‖∑ x ∈ (RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s)).filter
        (fun x => ¬ ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ')), ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
          dw q a' n * (if (∏ i, x i) ∣ n ∧ rough ⌈(q : ℝ) ^ εw⌉₊ n then 1 else 0)‖ ≤
        Zh * ∑ x ∈ (RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s)).filter
          (fun x => ¬ ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ')), 1 / ((∏ i, x i : ℕ) : ℝ) +
          (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
      rw [filter_large_eq _ hX0]
      rcases SieveP6Split.RTg_nz (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s ++
          [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]) with h | h
      · rw [h, Finset.sum_empty, Finset.sum_empty, norm_zero, mul_zero, zero_add]
        exact he0
      · rw [h, hZh]
        have hK1 : (I s).card ≤ Kmax :=
          le_trans (Finset.card_le_univ _) (by rw [Fintype.card_fin]; omega)
        have hK2 : (I s)ᶜ.card ≤ Kmax :=
          le_trans (Finset.card_le_univ _) (by rw [Fintype.card_fin]; omega)
        have hlen' : ((SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s ++
            [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter
              fun C : GCmp (j + s) => decide (∃ i, C.e i ≠ 0)).length ≤ J₀ := by
          refine (List.length_filter_le _ _).trans ?_
          have h1 := length_Pblock_le j s (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (z₀ : ℝ)
          have h2 : s * s + 2 * s ≤ smax * smax + 2 * smax := by nlinarith
          simp only [SieveP6Tree.leafCmps, List.length_append, List.length_map, List.length_cons, List.length_nil]
          omega
        have hnz' : ∀ C ∈ (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s ++
            [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter (fun C : GCmp (j + s) => decide (∃ i, C.e i ≠ 0)),
            ∃ i, C.e i ≠ 0 :=
          fun C hC => of_decide_eq_true (List.mem_filter.1 hC).2
        have hcΩ := leafCmps_c_le (j := j) (Ω := Ω) (S₀ := S₀) (E := E) (w := (⌈(q : ℝ) ^ εw⌉₊ : ℝ))
          (z₀ := (z₀ : ℝ)) (X := (q : ℝ) ^ (L - 1 - δ')) (s := s) (B := Λ₁ * Real.log q) (by positivity) hc hlz hlE
          hw1' hX
        have hform' : ∀ C ∈ (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s ++
            [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter (fun C : GCmp (j + s) => decide (∃ i, C.e i ≠ 0)),
            ∀ x : Fin (j + s) → ℕ, (∀ i, 1 ≤ x i ∧ x i ≤ ⌊2 * (q : ℝ) ^ L⌋₊) → C.form 0 x ≤ Λ₀ * Real.log q := by
          intro C hC x hx
          have h1 := SieveP6Split.form_le C 0 (fun i => (hx i).1) (Y := (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ))
            (fun i => by exact_mod_cast (hx i).2)
          have h2 := hcΩ C (List.mem_filter.1 hC).1
          have h3 : ((j + s : ℕ) : ℝ) * Real.log (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) ≤
              (j + smax) * Real.log (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ hlogN₂
            push_cast
            have : (s : ℝ) ≤ smax := by exact_mod_cast hs.le
            linarith
          linarith
        have hreg' : ∀ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ ((SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s ++
            [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter (fun C : GCmp (j + s) => decide (∃ i, C.e i ≠ 0))),
            StrictAnti x ∧ ∀ i, ⌈(q : ℝ) ^ εw⌉₊ ≤ x i := by
          intro x hx
          rw [← h, ← filter_large_eq _ hX0] at hx
          have hx' := (Finset.mem_filter.1 hx).1
          exact ⟨(hleaf s x hx').1, fun i => ((hleaf s x hx').2 i).2⟩
        have hgeo' : ∀ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ ((SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s ++
            [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter (fun C : GCmp (j + s) => decide (∃ i, C.e i ≠ 0))),
            ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
            ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) *
              ((∏ i ∈ (I s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) ^ (L - b) ∧
            (q : ℝ) ^ (L - 1 - δ') ≤ ((∏ i, x i : ℕ) : ℝ) := by
          intro x hx
          rw [← h, ← filter_large_eq _ hX0] at hx
          obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
          have hlt := not_le.1 hx2
          obtain ⟨g1, g2⟩ := hgeo s hs x hx1 hlt
          exact ⟨g1, g2, hlt.le⟩
        exact large_leaves_le hok (I s) hK1 hK2 _ hlen' hnz' hform' hreg' hgeo'
    have h3 := mul_le_mul_of_nonneg_left hcard (by positivity : (0 : ℝ) ≤ 2 * rm)
    have h4 : 0 ≤ Zh * ∑ x ∈ (RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊
        (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s)).filter
          (fun x => ¬ ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ')), 1 / ((∏ i, x i : ℕ) : ℝ) :=
      mul_nonneg hZh0 (Finset.sum_nonneg fun x _ => by positivity)
    have h5 : 0 ≤ rm * (q : ℝ) ^ (L - 1 - δ') * ∑ x ∈ (RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊
        (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s)).filter
          (fun x => ¬ ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ')), 1 / ((∏ i, x i : ℕ) : ℝ) :=
      mul_nonneg (mul_nonneg hrm0 hX0.le) (Finset.sum_nonneg fun x _ => by positivity)
    nlinarith [hsm, hlg, h3, h4, h5]
  · refine Finset.sum_eq_zero fun x hx => ?_
    exfalso
    have hx1 := SieveP6Tree.one_le_of_mem_RTg hx
    obtain ⟨-, ⟨-, hblk⟩, hlo⟩ := (SieveP6Tree.leafCmps_holds Ω S₀ hE hw0 hz0 hx1).1 (Finset.mem_filter.1 hx).2
    rw [SieveP6Tree.prod_idxAll] at hlo
    have h1 : (1 : ℝ) ≤ ∏ i ∈ S₀, (x (Fin.castAdd s i) : ℝ) := Finset.one_le_prod₀ fun i _ => by exact_mod_cast hx1 _
    have h2 : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ s ≤ ∏ u : Fin s, (x (Fin.natAdd j u) : ℝ) := by
      calc (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ s = ∏ _u : Fin s, (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hw0.le) fun u _ => (hblk u).2
    have h3 : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ s := pow_le_pow_right₀ hw1' hs
    have h4 : 0 ≤ ∏ u : Fin s, (x (Fin.natAdd j u) : ℝ) := Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
    have h5 := mul_le_mul h1 (le_refl (∏ u : Fin s, (x (Fin.natAdd j u) : ℝ))) h4 (by linarith)
    linarith
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h := sum_leaves_inv_le Ω S₀ E hw1 hwz hz₀ smax
    have hZR : 0 ≤ 2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
        (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ') := by
      positivity
    exact add_le_add (mul_le_mul_of_nonneg_left h hZR) le_rfl

end SieveP6TreeLeaves
