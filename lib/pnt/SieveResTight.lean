/-
# The resonant window's condition on a box with the variable tied to the rest

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveTypeIIHM.ResBox g L K m_lo lo` asks the window's condition `ResCond` at every exponent `m ≥ m_lo` of the
variable and every exponents `s j ≥ lo j` of the rest: on a box of cells it is tested at a corner that is no point of
the box, the rest's lower ends with the variable that the rest's upper ends leave. On a box the rest and the variable
make up `q^L`, so the variable's exponent is `L − Σ_j s_j` up to the dyadic blocks.

* `ResBoxT g L K lo hi w`, **the condition on a box, the variable tied to the rest**: `ResCond` at every exponents
  `lo j ≤ s j ≤ hi j` of the rest and every `m` with `L − w ≤ Σ_j s_j + m ≤ L + 10⁻⁵`.
* `FullEst L e₀ n Reg`, **the estimate of the tuples of primes with a rest in a region**: for every `K`, `J₀` and
  `Λ₁ ≥ 0` there are `δ > 0` and `q₀` such that for `q ≥ q₀`, a unit `a` and injective positions `r 0, …, r n`, the
  `K`-tuples `z` of primes up to `⌊2q^L⌋` that satisfy at most `J₀` comparisons with constants at most `Λ₁ log q`,
  each with entries at least `q^{e₀}`, product in `(⌊q^L⌋, ⌊2q^L⌋]` and `Reg q (z ∘ r)`, have
  `|Σ_z (1[∏z ≡ a] − 1[(∏z, q) = 1]/φ(q))| ≤ q^{L−δ}/φ(q)`: what `full_res_exp` gives, as a hypothesis of the
  terms' evaluations.
* `resBox_of_tight`: on a sub-cell `[a_j, a_j + η)` of each cell `[lo j, hi j]`, with `2(n + 1)η ≤ 10⁻⁵`, the
  condition `ResBox` of `full_res_exp` (`ρ₂ = Σ_j (a_j + η)`, `ε = η`) follows from `ResBoxT` on the cells widened
  by `2·10⁻⁵`: there the rest's exponents are within `2(n + 1)η + 10⁻⁵` of the sub-cell and the variable's is tied.
* `fullEst_of_tightG`: **`FullEst` on a box from `ResBoxT`, with the rest grouped into parts**, the region
  `q^{lo p} ≤ ∏_{grp i = p} x_i ≤ q^{hi p}`: the family is cut by the sub-cell of each part's product (comparisons of
  products with thresholds `q^{a}`, `prodGeC` and `prodLtC`, appended to the family's), a fixed number of families,
  each evaluated by `full_res_expG`. `FullEst.mono`: a smaller region.
* `fullEst_of_tight`: the case of one entry in each part, the region `q^{lo i} ≤ x_i ≤ q^{hi i}`.

The file imports `SieveResFull.lean` and `SieveP6Tree.lean`.
-/
import SieveResFull
import SieveP6Tree

open Real Finset

namespace SieveTypeIIHM

/-- **The resonant window's condition on a box, the variable tied to the rest**: `ResCond` at every exponents
`lo j ≤ s j ≤ hi j` of the rest and every exponent `m` of the variable with `L − w ≤ Σ_j s_j + m ≤ L + 10⁻⁵`. -/
def ResBoxT (g : ℝ → ℝ) (L : ℝ) (K : ℕ) (lo hi : ℕ → ℝ) (w : ℝ) : Prop :=
  ∀ (m : ℝ) (s : ℕ → ℝ), (∀ j < K, lo j ≤ s j ∧ s j ≤ hi j) → L - w ≤ ∑ j ∈ Finset.range K, s j + m →
    ∑ j ∈ Finset.range K, s j + m ≤ L + 1 / 10 ^ 5 → ResCond g L K m s

/-- **A thin sub-cell of a box with the variable tied to the rest**: for `a j` in `[lo j, hi j]` and `η > 0` with
`2(n + 1)η ≤ 10⁻⁵`, `ResBoxT` on the cells widened by `2·10⁻⁵` gives `ResBox` at the variable's exponent
`L − Σ_j (a_j + η) − η` and the rest's `a_j − η`. -/
lemma resBox_of_tight {g : ℝ → ℝ} {L : ℝ} {n : ℕ} {lo hi : ℕ → ℝ} {η : ℝ} (hη : 0 < η)
    (hηn : ((n : ℝ) + 1) * η ≤ 1 / (2 * 10 ^ 5))
    (hres : ResBoxT g L (n + 1) (fun j => lo j - 2 / 10 ^ 5) (fun j => hi j + 2 / 10 ^ 5) (2 / 10 ^ 5))
    {a : ℕ → ℝ} (ha : ∀ j < n + 1, lo j ≤ a j ∧ a j ≤ hi j) :
    ResBox g L (n + 1) (L - ∑ j ∈ Finset.range (n + 1), (a j + η) - η) (fun j => a j - η) := by
  intro m s hm hs _ hsm
  have hηT : η ≤ ((n : ℝ) + 1) * η := le_mul_of_one_le_left hη.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have h2 : ∑ i ∈ Finset.range (n + 1), (a i - η) = ∑ i ∈ Finset.range (n + 1), a i - ((n : ℝ) + 1) * η := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have h3 : ∑ i ∈ Finset.range (n + 1), (a i + η) = ∑ i ∈ Finset.range (n + 1), a i + ((n : ℝ) + 1) * η := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ((n : ℝ) + 1) * η := ⟨_, rfl⟩
  rw [← hT] at hηT hηn h2 h3
  have h4 : ∑ i ∈ Finset.range (n + 1), (a i - η) ≤ ∑ i ∈ Finset.range (n + 1), s i :=
    Finset.sum_le_sum fun i hi => hs i (Finset.mem_range.1 hi)
  have h5 : (1 : ℝ) / (2 * 10 ^ 5) = 1 / 10 ^ 5 / 2 := by norm_num
  refine hres m s (fun j hj => ⟨?_, ?_⟩) ?_ hsm
  · have h6 := hs j hj
    have h7 := (ha j hj).1
    show lo j - 2 / 10 ^ 5 ≤ s j
    linarith
  · have h1 : s j - (a j - η) ≤ ∑ i ∈ Finset.range (n + 1), (s i - (a i - η)) :=
      Finset.single_le_sum (f := fun i => s i - (a i - η))
        (fun i hi => sub_nonneg.2 (hs i (Finset.mem_range.1 hi))) (Finset.mem_range.2 hj)
    rw [Finset.sum_sub_distrib] at h1
    have h7 := (ha j hj).2
    show s j ≤ hi j + 2 / 10 ^ 5
    linarith
  · linarith

section Est

open SieveTypeIIGen SieveChain SieveFamily SieveDecomp Classical

/-- **The estimate of the tuples of primes with a rest in a region.** For every `K`, `J₀` and `Λ₁ ≥ 0` there are
`δ > 0` and `q₀` such that for `q ≥ q₀`, a unit `a` mod `q` and injective positions `r 0, …, r n`: if the `K`-tuples
`z` of primes that satisfy at most `J₀` comparisons `Ω` with constants at most `Λ₁ log q` have their entries at
least `q^{e₀}`, their product in `(⌊q^L⌋, ⌊2q^L⌋]` and `Reg q (z ∘ r)`, then
`|Σ_z (1[∏z ≡ a] − 1[(∏z, q) = 1]/φ(q))| ≤ q^{L−δ}/φ(q)` over those up to `⌊2q^L⌋`. -/
def FullEst (L e₀ : ℝ) (n : ℕ) (Reg : ℕ → (Fin (n + 1) → ℕ) → Prop) : Prop :=
  ∀ (K J₀ : ℕ) (Λ₁ : ℝ), 0 ≤ Λ₁ → ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
    ∀ (a : ZMod q), IsUnit a → ∀ (r : Fin (n + 1) → Fin K), Function.Injective r →
    ∀ (Ω : List (GCmp K)), Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
    (∀ z : Fin K → ℕ, (∀ t, (z t).Prime) → (∀ C ∈ Ω, C.holds 0 z) →
      (∀ t, (q : ℝ) ^ e₀ ≤ z t) ∧ Reg q (fun i => z (r i)) ∧
        ⌊(q : ℝ) ^ L⌋₊ < ∏ t, z t ∧ ∏ t, z t ≤ ⌊2 * (q : ℝ) ^ L⌋₊) →
    ‖∑ z ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω, dw q a (∏ t, z t)‖ ≤ (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)


/-- The comparison `∏_{t∈T} x_t ≥ b`. -/
noncomputable def prodGeC {K : ℕ} (T : Finset (Fin K)) (b : ℝ) : GCmp K :=
  ⟨fun _ => -Real.log b, fun i => if i ∈ T then 1 else 0, false, fun i => by split_ifs <;> simp⟩

/-- The comparison `∏_{t∈T} x_t < b`. -/
noncomputable def prodLtC {K : ℕ} (T : Finset (Fin K)) (b : ℝ) : GCmp K :=
  ⟨fun _ => Real.log b, fun i => -(if i ∈ T then 1 else 0), true, fun i => by split_ifs <;> simp⟩

lemma prodGeC_holds {K : ℕ} (T : Finset (Fin K)) {b : ℝ} (hb : 0 < b) {x : Fin K → ℕ} (hx : ∀ i, 1 ≤ x i) :
    (prodGeC T b).holds 0 x ↔ b ≤ ∏ t ∈ T, (x t : ℝ) := by
  have hprod : (0 : ℝ) < ∏ i ∈ T, (x i : ℝ) := Finset.prod_pos fun i _ => by exact_mod_cast hx i
  simp only [prodGeC, GCmp.holds, GCmp.form, Bool.false_eq_true, ite_false, SieveCmp.sum_set T x hx,
    neg_add_eq_sub, sub_nonneg]
  exact Real.log_le_log_iff hb hprod

lemma prodLtC_holds {K : ℕ} (T : Finset (Fin K)) {b : ℝ} (hb : 0 < b) {x : Fin K → ℕ} (hx : ∀ i, 1 ≤ x i) :
    (prodLtC T b).holds 0 x ↔ ∏ t ∈ T, (x t : ℝ) < b := by
  have hprod : (0 : ℝ) < ∏ i ∈ T, (x i : ℝ) := Finset.prod_pos fun i _ => by exact_mod_cast hx i
  simp only [prodLtC, GCmp.holds, GCmp.form, ite_true, neg_mul, Finset.sum_neg_distrib, SieveCmp.sum_set T x hx,
    ← sub_eq_add_neg, sub_pos]
  exact Real.log_lt_log_iff hprod hb

/-- `FullEst` for a region gives it for any smaller region. -/
lemma FullEst.mono {L e₀ : ℝ} {n : ℕ} {Reg Reg' : ℕ → (Fin (n + 1) → ℕ) → Prop} (h : FullEst L e₀ n Reg')
    (hsub : ∀ q x, Reg q x → Reg' q x) : FullEst L e₀ n Reg := by
  intro K J₀ Λ₁ hΛ₁
  obtain ⟨δ, hδ, q₀, H⟩ := h K J₀ Λ₁ hΛ₁
  refine ⟨δ, hδ, q₀, fun q _ hq a ha r hr Ω hΩlen hΩc hreg => H q hq a ha r hr Ω hΩlen hΩc fun z hz hzΩ => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hreg z hz hzΩ
  exact ⟨h1, hsub q _ h2, h3, h4⟩

set_option maxHeartbeats 1600000 in
/-- **The estimate on a box, from the condition with the variable tied to the rest, with the rest grouped into
parts.** `fullEst_of_tight` for the rest's entries grouped by `grp` into `m + 1` nonempty parts, with cells
`0 ≤ lo p ≤ hi p` for the parts' products: from `ResBoxT` at the parts on the cells widened by `2·10⁻⁵`, `FullEst`
holds for the region `q^{lo p} ≤ ∏_{grp i = p} x_i ≤ q^{hi p}`. The family is cut by the sub-cells
`[lo p + cη, lo p + (c + 1)η)` of the parts' products, `η = 1/(4·10⁵(m + 1))` (comparisons of products,
`prodGeC`, `prodLtC`), each evaluated by `full_res_expG`. -/
theorem fullEst_of_tightG {g : ℝ → ℝ} {L : ℝ} (hg1 : ∀ σ, g σ ≤ 1) (hg0 : g (1 / 2) = 1) (hcnt : CurveCounts g)
    (hL0 : 0 < L) (hL : L ≤ 5 / 2) {e₀ : ℝ} (he₀ : 0 < e₀) {n m : ℕ} {grp : ℕ → ℕ}
    (hgrp : ∀ j < n + 1, grp j < m + 1) (hne : ∀ p < m + 1, ∃ j < n + 1, grp j = p) {lo hi : ℕ → ℝ}
    (hlo : ∀ p < m + 1, 0 ≤ lo p ∧ lo p ≤ hi p) (hsum : ∑ p ∈ Finset.range (m + 1), hi p + 1 / 10 ^ 5 ≤ L)
    (hres : ResBoxT g L (m + 1) (fun p => lo p - 2 / 10 ^ 5) (fun p => hi p + 2 / 10 ^ 5) (2 / 10 ^ 5)) :
    FullEst L e₀ n (fun q x => ∀ p < m + 1,
      (q : ℝ) ^ lo p ≤ ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => grp i = p), (x i : ℝ) ∧
      ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => grp i = p), (x i : ℝ) ≤ (q : ℝ) ^ hi p) := by
  intro K J₀ Λ₁ hΛ₁
  -- the sub-cells
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = 1 / (4 * 10 ^ 5 * ((m : ℝ) + 1)) := ⟨_, rfl⟩
  have hn1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hη : 0 < η := by rw [hηdef]; positivity
  have hT : ((m : ℝ) + 1) * η = 1 / (4 * 10 ^ 5) := by rw [hηdef]; field_simp
  have hηT : η ≤ ((m : ℝ) + 1) * η := le_mul_of_one_le_left hη.le (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have hηn : ((m : ℝ) + 1) * η ≤ 1 / (2 * 10 ^ 5) := by rw [hT]; norm_num
  have hη5 : η ≤ 1 / (4 * 10 ^ 5) := by rw [← hT]; exact hηT
  set S : Finset (Fin (m + 1) → ℕ) :=
    Fintype.piFinset (fun p : Fin (m + 1) => Finset.range (⌊(hi p - lo p) / η⌋₊ + 1)) with hS
  set A : (Fin (m + 1) → ℕ) → ℕ → ℝ := fun c p => if h : p < m + 1 then lo p + (c ⟨p, h⟩ : ℝ) * η else 0 with hA
  have hAin : ∀ c ∈ S, ∀ p < m + 1, lo p ≤ A c p ∧ A c p ≤ hi p := by
    intro c hc p hp
    have hcp := Finset.mem_range.1 (Fintype.mem_piFinset.1 hc ⟨p, hp⟩)
    have h1 : (c ⟨p, hp⟩ : ℝ) ≤ (hi p - lo p) / η := by
      have h2 : c ⟨p, hp⟩ ≤ ⌊(hi p - lo p) / η⌋₊ := Nat.lt_succ_iff.1 hcp
      exact (Nat.cast_le.2 h2).trans (Nat.floor_le (div_nonneg (sub_nonneg.2 (hlo p hp).2) hη.le))
    rw [le_div_iff₀ hη] at h1
    have h3 : (0 : ℝ) ≤ (c ⟨p, hp⟩ : ℝ) * η := by positivity
    simp only [hA, dite_eq_left hp]
    exact ⟨by linarith, by linarith⟩
  have hhi0 : ∀ p < m + 1, 0 ≤ hi p := fun p hp => (hlo p hp).1.trans (hlo p hp).2
  have hhiL : ∀ p < m + 1, hi p + 1 / 10 ^ 5 ≤ L := fun p hp => by
    have h1 : hi p ≤ ∑ i ∈ Finset.range (m + 1), hi i :=
      Finset.single_le_sum (f := hi) (fun i hi' => hhi0 i (Finset.mem_range.1 hi')) (Finset.mem_range.2 hp)
    linarith
  have hρle : ∀ c ∈ S, ∑ p ∈ Finset.range (m + 1), (A c p + η) ≤
      ∑ p ∈ Finset.range (m + 1), hi p + ((m : ℝ) + 1) * η := by
    intro c hc
    calc ∑ p ∈ Finset.range (m + 1), (A c p + η) ≤ ∑ p ∈ Finset.range (m + 1), (hi p + η) :=
          Finset.sum_le_sum fun p hp => by linarith [(hAin c hc p (Finset.mem_range.1 hp)).2]
      _ = ∑ p ∈ Finset.range (m + 1), hi p + ((m : ℝ) + 1) * η := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hρ0 : ∀ c ∈ S, 0 ≤ ∑ p ∈ Finset.range (m + 1), (A c p + η) := fun c hc =>
    Finset.sum_nonneg fun p hp => by
      linarith [(hAin c hc p (Finset.mem_range.1 hp)).1, (hlo p (Finset.mem_range.1 hp)).1]
  have hLρ : ∀ c ∈ S, 0 < L - ∑ p ∈ Finset.range (m + 1), (A c p + η) - η := fun c hc => by
    have h1 := hρle c hc
    rw [hT] at h1
    have h2 : (1 : ℝ) / (4 * 10 ^ 5) = 1 / 10 ^ 5 / 4 := by norm_num
    rw [h2] at h1 hη5
    linarith
  have H := fun c : S => full_res_expG hg1 hg0 hcnt hL0 hL he₀ K (J₀ + 2 * (m + 1)) (Λ₁ := Λ₁ + L)
    (by linarith) (hρ0 c.1 c.2) hη (hLρ c.1 c.2)
  choose δf hδf q₀f hq₀f using H
  have hSne : S.attach.Nonempty := by
    rw [Finset.attach_nonempty_iff]
    exact ⟨fun _ => 0, Fintype.mem_piFinset.2 fun p => Finset.mem_range.2 (Nat.succ_pos _)⟩
  obtain ⟨δ₀, hδ₀def⟩ : ∃ δ₀ : ℝ, δ₀ = S.attach.inf' hSne δf := ⟨_, rfl⟩
  have hδ₀ : 0 < δ₀ := by rw [hδ₀def]; exact (Finset.lt_inf'_iff hSne).2 fun c _ => hδf c
  have hδ₀le : ∀ c : S, δ₀ ≤ δf c := fun c => by
    rw [hδ₀def]
    exact Finset.inf'_le δf (Finset.mem_attach S c)
  have hev := (tendsto_rpow_atTop (half_pos hδ₀)).eventually_ge_atTop (S.card : ℝ)
  obtain ⟨q₂, hq₂⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨δ₀ / 2, half_pos hδ₀, max (max (S.attach.sup q₀f) q₂) 2, ?_⟩
  intro q _ hq a ha r hr Ω hΩlen hΩc hreg
  have hqS := hq₂ q (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq)
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) < q := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  set N₂ := ⌊2 * (q : ℝ) ^ L⌋₊ with hN₂
  have hRT : ∀ z ∈ RTg K N₂ Ω, (∀ t, (z t).Prime) ∧ (∀ C ∈ Ω, C.holds 0 z) := by
    intro z hz
    rw [RTg, Finset.mem_filter, Fintype.mem_piFinset] at hz
    exact ⟨fun t => (SieveTypeIIU.mem_primesLe.1 (hz.1 t)).2, hz.2⟩
  -- a part's positions, and its product
  set Gp : Fin (m + 1) → Finset (Fin K) := fun p =>
    (Finset.univ.filter (fun i : Fin (n + 1) => grp i = p)).image r with hGp
  have hGprod : ∀ (z : Fin K → ℕ) (p : Fin (m + 1)), ∏ t ∈ Gp p, (z t : ℝ) =
      ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => grp i = p), (z (r i) : ℝ) := fun z p =>
    Finset.prod_image fun i _ j _ h => hr h
  -- the sub-cell of a tuple, and a sub-cell's comparisons
  set idx : (Fin K → ℕ) → Fin (m + 1) → ℕ := fun z p =>
    ⌊(Real.logb q (∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => grp i = p), (z (r i) : ℝ)) - lo p) / η⌋₊
    with hidx
  set Ωc : (Fin (m + 1) → ℕ) → List (GCmp K) := fun c =>
    List.ofFn (fun p : Fin (m + 1) => prodGeC (Gp p) ((q : ℝ) ^ A c p)) ++
      List.ofFn (fun p : Fin (m + 1) => prodLtC (Gp p) ((q : ℝ) ^ (A c p + η))) with hΩcdef
  have hΩciff : ∀ (c : Fin (m + 1) → ℕ) (z : Fin K → ℕ), (∀ t, 1 ≤ z t) →
      ((∀ C ∈ Ωc c, C.holds 0 z) ↔
        (∀ p : Fin (m + 1), (q : ℝ) ^ A c p ≤ ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => grp i = p),
          (z (r i) : ℝ)) ∧
        ∀ p : Fin (m + 1), ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => grp i = p), (z (r i) : ℝ) <
          (q : ℝ) ^ (A c p + η)) := by
    intro c z hz1
    simp only [hΩcdef, List.forall_mem_append, List.forall_mem_ofFn_iff]
    refine and_congr (forall_congr' fun p => ?_) (forall_congr' fun p => ?_)
    · rw [prodGeC_holds _ (by positivity) hz1, hGprod]
    · rw [prodLtC_holds _ (by positivity) hz1, hGprod]
  have hAj : ∀ (c : Fin (m + 1) → ℕ) (p : Fin (m + 1)), A c p = lo p + (c p : ℝ) * η := fun c p => by
    simp only [hA, dite_eq_left p.isLt, Fin.eta]
  have hcell : ∀ z ∈ RTg K N₂ Ω, ∀ c, (idx z = c ↔ ∀ C ∈ Ωc c, C.holds 0 z) := by
    intro z hz c
    obtain ⟨hzp, hzΩ⟩ := hRT z hz
    obtain ⟨-, hrg, -, -⟩ := hreg z hzp hzΩ
    rw [hΩciff c z fun t => (hzp t).one_lt.le]
    have key : ∀ p : Fin (m + 1), (idx z p = c p ↔
        (q : ℝ) ^ A c p ≤ ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => grp i = p), (z (r i) : ℝ) ∧
        ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => grp i = p), (z (r i) : ℝ) < (q : ℝ) ^ (A c p + η)) := by
      intro p
      have hpos : (0 : ℝ) < ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => grp i = p), (z (r i) : ℝ) :=
        Finset.prod_pos fun i _ => by exact_mod_cast (hzp _).pos
      have hx0 : 0 ≤ (Real.logb q (∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => grp i = p), (z (r i) : ℝ)) -
          lo p) / η := by
        refine div_nonneg (sub_nonneg.2 ?_) hη.le
        rw [Real.le_logb_iff_rpow_le hq1 hpos]
        exact (hrg p p.isLt).1
      show ⌊(Real.logb q (∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => grp i = p), (z (r i) : ℝ)) -
        lo p) / η⌋₊ = c p ↔ _
      rw [Nat.floor_eq_iff hx0, le_div_iff₀ hη, div_lt_iff₀ hη, ← Real.le_logb_iff_rpow_le hq1 hpos,
        ← Real.logb_lt_iff_lt_rpow hq1 hpos, hAj]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    constructor
    · intro h
      exact ⟨fun p => ((key p).1 (congrFun h p)).1, fun p => ((key p).1 (congrFun h p)).2⟩
    · rintro ⟨h1, h2⟩
      exact funext fun p => (key p).2 ⟨h1 p, h2 p⟩
  have hmaps : ∀ z ∈ RTg K N₂ Ω, idx z ∈ S := by
    intro z hz
    obtain ⟨hzp, hzΩ⟩ := hRT z hz
    obtain ⟨-, hrg, -, -⟩ := hreg z hzp hzΩ
    refine Fintype.mem_piFinset.2 fun p => Finset.mem_range.2 (Nat.lt_succ_iff.2 (Nat.floor_le_floor ?_))
    have hpos : (0 : ℝ) < ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => grp i = p), (z (r i) : ℝ) :=
      Finset.prod_pos fun i _ => by exact_mod_cast (hzp _).pos
    have h1 : Real.logb q (∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => grp i = p), (z (r i) : ℝ)) ≤ hi p := by
      rw [Real.logb_le_iff_le_rpow hq1 hpos]
      exact (hrg p p.isLt).2
    exact div_le_div_of_nonneg_right (by linarith) hη.le
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ c ∈ S, ∑ z ∈ (RTg K N₂ Ω).filter (fun z => idx z = c), dw q a (∏ t, z t) =
      ∑ z ∈ RTg K N₂ (Ω ++ Ωc c), dw q a (∏ t, z t) := by
    intro c _
    rw [SieveP6Tree.RTg_append]
    exact Finset.sum_congr (Finset.filter_congr fun z hz => hcell z hz c) fun _ _ => rfl
  rw [Finset.sum_congr rfl hfib]
  -- the parts partition the rest's entries
  have hgrpF : ∀ i : Fin (n + 1), grp i ∈ Finset.range (m + 1) := fun i => Finset.mem_range.2 (hgrp i i.isLt)
  have hbound : ∀ c ∈ S, ‖∑ z ∈ RTg K N₂ (Ω ++ Ωc c), dw q a (∏ t, z t)‖ ≤
      (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₀) := by
    intro c hc
    have hq' : q₀f ⟨c, hc⟩ ≤ q := le_trans (Finset.le_sup (f := q₀f) (Finset.mem_attach S ⟨c, hc⟩))
      (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hq))
    refine (hq₀f ⟨c, hc⟩ q hq' a ha n r hr (m + 1) grp hgrp hne (A c)
      (resBox_of_tight hη hηn hres (hAin c hc)) (Ω ++ Ωc c) 0 ?_ ?_ ?_).trans ?_
    · rw [List.length_append]
      simp only [hΩcdef, List.length_append, List.length_ofFn]
      omega
    · -- the constants
      have hΛl : Λ₁ * Real.log q ≤ (Λ₁ + L) * Real.log q := by nlinarith
      rw [List.forall_mem_append]
      refine ⟨fun C hC => (hΩc C hC).trans hΛl, ?_⟩
      simp only [hΩcdef, List.forall_mem_append, List.forall_mem_ofFn_iff]
      refine ⟨fun p => ?_, fun p => ?_⟩
      · show -Real.log ((q : ℝ) ^ A c p) ≤ _
        rw [Real.log_rpow hq0]
        have h1 := (hAin c hc p p.isLt).1
        have h2 := (hlo p p.isLt).1
        have h3 : 0 ≤ A c p * Real.log q := mul_nonneg (by linarith) hlogq.le
        have h4 : 0 ≤ (Λ₁ + L) * Real.log q := mul_nonneg (by linarith) hlogq.le
        linarith
      · show Real.log ((q : ℝ) ^ (A c p + η)) ≤ _
        rw [Real.log_rpow hq0]
        have h1 := (hAin c hc p p.isLt).2
        have h2 := hhiL p p.isLt
        have h3 : (1 : ℝ) / (4 * 10 ^ 5) = 1 / 10 ^ 5 / 4 := by norm_num
        rw [h3] at hη5
        have h5 : (A c p + η) * Real.log q ≤ L * Real.log q := mul_le_mul_of_nonneg_right (by linarith) hlogq.le
        have h6 : 0 ≤ Λ₁ * Real.log q := mul_nonneg hΛ₁ hlogq.le
        linarith
    · -- the region
      intro z hz hzΩ
      rw [List.forall_mem_append] at hzΩ
      obtain ⟨hzΩ1, hzΩ2⟩ := hzΩ
      obtain ⟨hge, -, hlo', hhi'⟩ := hreg z hz hzΩ1
      obtain ⟨hA1, hA2⟩ := (hΩciff c z fun t => (hz t).one_lt.le).1 hzΩ2
      have e : ∏ t ∈ Finset.univ.image r, z t = ∏ i, z (r i) := Finset.prod_image fun i _ j _ h => hr h
      refine ⟨hge, fun p hp => hA1 ⟨p, hp⟩, ?_, ?_, hlo', hhi'⟩
      · rw [Real.rpow_zero]
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun t _ => (hz t).ne_zero)
      · rw [e]
        push_cast
        have hfibR : ∏ i, (z (r i) : ℝ) = ∏ p ∈ Finset.range (m + 1),
            ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => grp i = p), (z (r i) : ℝ) :=
          (Finset.prod_fiberwise_of_maps_to (fun i _ => hgrpF i) _).symm
        rw [hfibR, ← Fin.prod_univ_eq_prod_range (fun p => ∏ i ∈ Finset.univ.filter
          (fun i : Fin (n + 1) => grp i = p), (z (r i) : ℝ))]
        calc ∏ p : Fin (m + 1), ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => grp i = p), (z (r i) : ℝ)
            ≤ ∏ p : Fin (m + 1), (q : ℝ) ^ (A c p + η) :=
              Finset.prod_le_prod₀ (fun p _ => Finset.prod_nonneg fun i _ => Nat.cast_nonneg _)
                fun p _ => (hA2 p).le
          _ = (q : ℝ) ^ ∑ p : Fin (m + 1), (A c p + η) := (Real.rpow_sum_of_pos hq0 _ _).symm
          _ = (q : ℝ) ^ ∑ p ∈ Finset.range (m + 1), (A c p + η) := by
              rw [Fin.sum_univ_eq_sum_range (fun p => A c p + η) (m + 1)]
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hq1.le (by linarith [hδ₀le ⟨c, hc⟩])) (by positivity)
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ hbound).trans ?_)
  rw [nsmul_eq_mul]
  calc (S.card : ℝ) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₀))
      ≤ (q : ℝ) ^ (δ₀ / 2) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₀)) :=
        mul_le_mul_of_nonneg_right hqS (by positivity)
    _ = (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₀ / 2) := by
        rw [mul_left_comm, ← Real.rpow_add hq0]
        congr 2
        ring

/-- **The estimate on a box, from the condition with the variable tied to the rest.** For cells `0 ≤ lo j ≤ hi j`
with `Σ_j hi j + 10⁻⁵ ≤ L` and `ResBoxT` on the cells widened by `2·10⁻⁵`, `FullEst` holds for the region
`q^{lo i} ≤ x_i ≤ q^{hi i}`. The family is cut by the sub-cells `[lo j + cη, lo j + (c + 1)η)` of the rest's primes,
`η = 1/(4·10⁵(n + 1))`: for each choice `c` of sub-cells the tuples with those are the family with `2(n + 1)` more
comparisons, evaluated by `full_res_exp` with `ρ₂ = Σ_j (a_j + η)`, `ε = η` (`resBox_of_tight`); the choices are a
fixed number, at most `q^{δ/2}`: `fullEst_of_tightG` with each entry its own part. -/
theorem fullEst_of_tight {g : ℝ → ℝ} {L : ℝ} (hg1 : ∀ σ, g σ ≤ 1) (hg0 : g (1 / 2) = 1) (hcnt : CurveCounts g)
    (hL0 : 0 < L) (hL : L ≤ 5 / 2) {e₀ : ℝ} (he₀ : 0 < e₀) {n : ℕ} {lo hi : ℕ → ℝ}
    (hlo : ∀ j < n + 1, 0 ≤ lo j ∧ lo j ≤ hi j) (hsum : ∑ j ∈ Finset.range (n + 1), hi j + 1 / 10 ^ 5 ≤ L)
    (hres : ResBoxT g L (n + 1) (fun j => lo j - 2 / 10 ^ 5) (fun j => hi j + 2 / 10 ^ 5) (2 / 10 ^ 5)) :
    FullEst L e₀ n (fun q x => ∀ i : Fin (n + 1), (q : ℝ) ^ lo i ≤ x i ∧ (x i : ℝ) ≤ (q : ℝ) ^ hi i) := by
  refine FullEst.mono (fullEst_of_tightG hg1 hg0 hcnt hL0 hL he₀ (n := n) (m := n) (grp := id) (fun j hj => hj)
    (fun p hp => ⟨p, hp, rfl⟩) hlo hsum hres) fun q x hx p hp => ?_
  have hsing : Finset.univ.filter (fun i : Fin (n + 1) => id (i : ℕ) = p) = {⟨p, hp⟩} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, id, Finset.mem_singleton]
    exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
  rw [hsing, Finset.prod_singleton]
  exact hx ⟨p, hp⟩

end Est

end SieveTypeIIHM

#print axioms SieveTypeIIHM.fullEst_of_tight
