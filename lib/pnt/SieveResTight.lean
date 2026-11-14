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
* `fullEst_of_tight`: **`FullEst` on a box from `ResBoxT`**, the region `q^{lo i} ≤ x_i ≤ q^{hi i}`: the family is
  cut by the sub-cell of each prime of the rest (comparisons with thresholds `q^{a}`, appended to the family's), a
  fixed number of families, each evaluated by `full_res_exp`.

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

set_option maxHeartbeats 1600000 in
/-- **The estimate on a box, from the condition with the variable tied to the rest.** For cells `0 ≤ lo j ≤ hi j`
with `Σ_j hi j + 10⁻⁵ ≤ L` and `ResBoxT` on the cells widened by `2·10⁻⁵`, `FullEst` holds for the region
`q^{lo i} ≤ x_i ≤ q^{hi i}`. The family is cut by the sub-cells `[lo j + cη, lo j + (c + 1)η)` of the rest's primes,
`η = 1/(4·10⁵(n + 1))`: for each choice `c` of sub-cells the tuples with those are the family with `2(n + 1)` more
comparisons, evaluated by `full_res_exp` with `ρ₂ = Σ_j (a_j + η)`, `ε = η` (`resBox_of_tight`); the choices are a
fixed number, at most `q^{δ/2}`. -/
theorem fullEst_of_tight {g : ℝ → ℝ} {L : ℝ} (hg1 : ∀ σ, g σ ≤ 1) (hg0 : g (1 / 2) = 1) (hcnt : CurveCounts g)
    (hL0 : 0 < L) (hL : L ≤ 5 / 2) {e₀ : ℝ} (he₀ : 0 < e₀) {n : ℕ} {lo hi : ℕ → ℝ}
    (hlo : ∀ j < n + 1, 0 ≤ lo j ∧ lo j ≤ hi j) (hsum : ∑ j ∈ Finset.range (n + 1), hi j + 1 / 10 ^ 5 ≤ L)
    (hres : ResBoxT g L (n + 1) (fun j => lo j - 2 / 10 ^ 5) (fun j => hi j + 2 / 10 ^ 5) (2 / 10 ^ 5)) :
    FullEst L e₀ n (fun q x => ∀ i : Fin (n + 1), (q : ℝ) ^ lo i ≤ x i ∧ (x i : ℝ) ≤ (q : ℝ) ^ hi i) := by
  intro K J₀ Λ₁ hΛ₁
  -- the sub-cells
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = 1 / (4 * 10 ^ 5 * ((n : ℝ) + 1)) := ⟨_, rfl⟩
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hη : 0 < η := by rw [hηdef]; positivity
  have hT : ((n : ℝ) + 1) * η = 1 / (4 * 10 ^ 5) := by rw [hηdef]; field_simp
  have hηT : η ≤ ((n : ℝ) + 1) * η := le_mul_of_one_le_left hη.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hηn : ((n : ℝ) + 1) * η ≤ 1 / (2 * 10 ^ 5) := by rw [hT]; norm_num
  have hη5 : η ≤ 1 / (4 * 10 ^ 5) := by rw [← hT]; exact hηT
  set S : Finset (Fin (n + 1) → ℕ) :=
    Fintype.piFinset (fun j : Fin (n + 1) => Finset.range (⌊(hi j - lo j) / η⌋₊ + 1)) with hS
  set A : (Fin (n + 1) → ℕ) → ℕ → ℝ := fun c j => if h : j < n + 1 then lo j + (c ⟨j, h⟩ : ℝ) * η else 0 with hA
  have hAin : ∀ c ∈ S, ∀ j < n + 1, lo j ≤ A c j ∧ A c j ≤ hi j := by
    intro c hc j hj
    have hcj := Finset.mem_range.1 (Fintype.mem_piFinset.1 hc ⟨j, hj⟩)
    have h1 : (c ⟨j, hj⟩ : ℝ) ≤ (hi j - lo j) / η := by
      have h2 : c ⟨j, hj⟩ ≤ ⌊(hi j - lo j) / η⌋₊ := Nat.lt_succ_iff.1 hcj
      exact (Nat.cast_le.2 h2).trans (Nat.floor_le (div_nonneg (sub_nonneg.2 (hlo j hj).2) hη.le))
    rw [le_div_iff₀ hη] at h1
    have h3 : (0 : ℝ) ≤ (c ⟨j, hj⟩ : ℝ) * η := by positivity
    simp only [hA, dite_eq_left hj]
    exact ⟨by linarith, by linarith⟩
  have hhi0 : ∀ j < n + 1, 0 ≤ hi j := fun j hj => (hlo j hj).1.trans (hlo j hj).2
  have hhiL : ∀ j < n + 1, hi j + 1 / 10 ^ 5 ≤ L := fun j hj => by
    have h1 : hi j ≤ ∑ i ∈ Finset.range (n + 1), hi i :=
      Finset.single_le_sum (f := hi) (fun i hi' => hhi0 i (Finset.mem_range.1 hi')) (Finset.mem_range.2 hj)
    linarith
  have hρle : ∀ c ∈ S, ∑ j ∈ Finset.range (n + 1), (A c j + η) ≤
      ∑ j ∈ Finset.range (n + 1), hi j + ((n : ℝ) + 1) * η := by
    intro c hc
    calc ∑ j ∈ Finset.range (n + 1), (A c j + η) ≤ ∑ j ∈ Finset.range (n + 1), (hi j + η) :=
          Finset.sum_le_sum fun j hj => by linarith [(hAin c hc j (Finset.mem_range.1 hj)).2]
      _ = ∑ j ∈ Finset.range (n + 1), hi j + ((n : ℝ) + 1) * η := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hρ0 : ∀ c ∈ S, 0 ≤ ∑ j ∈ Finset.range (n + 1), (A c j + η) := fun c hc =>
    Finset.sum_nonneg fun j hj => by
      linarith [(hAin c hc j (Finset.mem_range.1 hj)).1, (hlo j (Finset.mem_range.1 hj)).1]
  have hLρ : ∀ c ∈ S, 0 < L - ∑ j ∈ Finset.range (n + 1), (A c j + η) - η := fun c hc => by
    have h1 := hρle c hc
    rw [hT] at h1
    have h2 : (1 : ℝ) / (4 * 10 ^ 5) = 1 / 10 ^ 5 / 4 := by norm_num
    rw [h2] at h1 hη5
    linarith
  have H := fun c : S => full_res_exp hg1 hg0 hcnt hL0 hL he₀ K (J₀ + 2 * (n + 1)) (Λ₁ := Λ₁ + L)
    (by linarith) (hρ0 c.1 c.2) hη (hLρ c.1 c.2)
  choose δf hδf q₀f hq₀f using H
  have hSne : S.attach.Nonempty := by
    rw [Finset.attach_nonempty_iff]
    exact ⟨fun _ => 0, Fintype.mem_piFinset.2 fun j => Finset.mem_range.2 (Nat.succ_pos _)⟩
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
  -- the sub-cell of a tuple, and a sub-cell's comparisons
  set idx : (Fin K → ℕ) → Fin (n + 1) → ℕ := fun z j => ⌊(Real.logb q (z (r j)) - lo j) / η⌋₊ with hidx
  set Ωc : (Fin (n + 1) → ℕ) → List (GCmp K) := fun c =>
    List.ofFn (fun j : Fin (n + 1) => (Atom.ge (r j) ((q : ℝ) ^ A c j)).toG) ++
      List.ofFn (fun j : Fin (n + 1) => (Atom.lt (r j) ((q : ℝ) ^ (A c j + η))).toG) with hΩcdef
  have hΩciff : ∀ (c : Fin (n + 1) → ℕ) (z : Fin K → ℕ), (∀ t, 1 ≤ z t) →
      ((∀ C ∈ Ωc c, C.holds 0 z) ↔ (∀ j : Fin (n + 1), (q : ℝ) ^ A c j ≤ z (r j)) ∧
        ∀ j : Fin (n + 1), (z (r j) : ℝ) < (q : ℝ) ^ (A c j + η)) := by
    intro c z hz1
    simp only [hΩcdef, List.forall_mem_append, List.forall_mem_ofFn_iff]
    refine and_congr (forall_congr' fun j => ?_) (forall_congr' fun j => ?_)
    · exact Atom.toG_holds _ (by simp only [Atom.thr]; positivity) 0 hz1
    · exact Atom.toG_holds _ (by simp only [Atom.thr]; positivity) 0 hz1
  have hAj : ∀ (c : Fin (n + 1) → ℕ) (j : Fin (n + 1)), A c j = lo j + (c j : ℝ) * η := fun c j => by
    simp only [hA, dite_eq_left j.isLt, Fin.eta]
  have hcell : ∀ z ∈ RTg K N₂ Ω, ∀ c, (idx z = c ↔ ∀ C ∈ Ωc c, C.holds 0 z) := by
    intro z hz c
    obtain ⟨hzp, hzΩ⟩ := hRT z hz
    obtain ⟨-, hrg, -, -⟩ := hreg z hzp hzΩ
    have hzpos : ∀ t, (0 : ℝ) < z t := fun t => by exact_mod_cast (hzp t).pos
    rw [hΩciff c z fun t => (hzp t).one_lt.le]
    have key : ∀ j : Fin (n + 1), (idx z j = c j ↔
        (q : ℝ) ^ A c j ≤ z (r j) ∧ (z (r j) : ℝ) < (q : ℝ) ^ (A c j + η)) := by
      intro j
      have hx0 : 0 ≤ (Real.logb q (z (r j)) - lo j) / η := by
        refine div_nonneg (sub_nonneg.2 ?_) hη.le
        rw [Real.le_logb_iff_rpow_le hq1 (hzpos _)]
        exact (hrg j).1
      show ⌊(Real.logb q (z (r j)) - lo j) / η⌋₊ = c j ↔ _
      rw [Nat.floor_eq_iff hx0, le_div_iff₀ hη, div_lt_iff₀ hη, ← Real.le_logb_iff_rpow_le hq1 (hzpos (r j)),
        ← Real.logb_lt_iff_lt_rpow hq1 (hzpos (r j)), hAj]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    constructor
    · intro h
      exact ⟨fun j => ((key j).1 (congrFun h j)).1, fun j => ((key j).1 (congrFun h j)).2⟩
    · rintro ⟨h1, h2⟩
      exact funext fun j => (key j).2 ⟨h1 j, h2 j⟩
  have hmaps : ∀ z ∈ RTg K N₂ Ω, idx z ∈ S := by
    intro z hz
    obtain ⟨hzp, hzΩ⟩ := hRT z hz
    obtain ⟨-, hrg, -, -⟩ := hreg z hzp hzΩ
    refine Fintype.mem_piFinset.2 fun j => Finset.mem_range.2 (Nat.lt_succ_iff.2 (Nat.floor_le_floor ?_))
    have hzpos : (0 : ℝ) < z (r j) := by exact_mod_cast (hzp _).pos
    have h1 : Real.logb q (z (r j)) ≤ hi j := by
      rw [Real.logb_le_iff_le_rpow hq1 hzpos]
      exact (hrg j).2
    exact div_le_div_of_nonneg_right (by linarith) hη.le
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ c ∈ S, ∑ z ∈ (RTg K N₂ Ω).filter (fun z => idx z = c), dw q a (∏ t, z t) =
      ∑ z ∈ RTg K N₂ (Ω ++ Ωc c), dw q a (∏ t, z t) := by
    intro c _
    rw [SieveP6Tree.RTg_append]
    exact Finset.sum_congr (Finset.filter_congr fun z hz => hcell z hz c) fun _ _ => rfl
  rw [Finset.sum_congr rfl hfib]
  have hbound : ∀ c ∈ S, ‖∑ z ∈ RTg K N₂ (Ω ++ Ωc c), dw q a (∏ t, z t)‖ ≤
      (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₀) := by
    intro c hc
    have hq' : q₀f ⟨c, hc⟩ ≤ q := le_trans (Finset.le_sup (f := q₀f) (Finset.mem_attach S ⟨c, hc⟩))
      (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hq))
    refine (hq₀f ⟨c, hc⟩ q hq' a ha n r hr (A c) (resBox_of_tight hη hηn hres (hAin c hc)) (Ω ++ Ωc c) 0
      ?_ ?_ ?_).trans ?_
    · rw [List.length_append]
      simp only [hΩcdef, List.length_append, List.length_ofFn]
      omega
    · -- the constants
      have hΛl : Λ₁ * Real.log q ≤ (Λ₁ + L) * Real.log q := by nlinarith
      rw [List.forall_mem_append]
      refine ⟨fun C hC => (hΩc C hC).trans hΛl, ?_⟩
      simp only [hΩcdef, List.forall_mem_append, List.forall_mem_ofFn_iff]
      refine ⟨fun j => ?_, fun j => ?_⟩
      · show -Real.log ((q : ℝ) ^ A c j) ≤ _
        rw [Real.log_rpow hq0]
        have h1 := (hAin c hc j j.isLt).1
        have h2 := (hlo j j.isLt).1
        have h3 : 0 ≤ A c j * Real.log q := mul_nonneg (by linarith) hlogq.le
        have h4 : 0 ≤ (Λ₁ + L) * Real.log q := mul_nonneg (by linarith) hlogq.le
        linarith
      · show Real.log ((q : ℝ) ^ (A c j + η)) ≤ _
        rw [Real.log_rpow hq0]
        have h1 := (hAin c hc j j.isLt).2
        have h2 := hhiL j j.isLt
        have h3 : (1 : ℝ) / (4 * 10 ^ 5) = 1 / 10 ^ 5 / 4 := by norm_num
        rw [h3] at hη5
        have h5 : (A c j + η) * Real.log q ≤ L * Real.log q := mul_le_mul_of_nonneg_right (by linarith) hlogq.le
        have h6 : 0 ≤ Λ₁ * Real.log q := mul_nonneg hΛ₁ hlogq.le
        linarith
    · -- the region
      intro z hz hzΩ
      rw [List.forall_mem_append] at hzΩ
      obtain ⟨hzΩ1, hzΩ2⟩ := hzΩ
      obtain ⟨hge, -, hlo', hhi'⟩ := hreg z hz hzΩ1
      obtain ⟨hA1, hA2⟩ := (hΩciff c z fun t => (hz t).one_lt.le).1 hzΩ2
      have e : ∏ t ∈ Finset.univ.image r, z t = ∏ i, z (r i) := Finset.prod_image fun i _ j _ h => hr h
      refine ⟨hge, hA1, ?_, ?_, hlo', hhi'⟩
      · rw [Real.rpow_zero]
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun t _ => (hz t).ne_zero)
      · rw [e]
        push_cast
        calc ∏ i, (z (r i) : ℝ) ≤ ∏ i : Fin (n + 1), (q : ℝ) ^ (A c i + η) :=
              Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ => (hA2 i).le
          _ = (q : ℝ) ^ ∑ i : Fin (n + 1), (A c i + η) := (Real.rpow_sum_of_pos hq0 _ _).symm
          _ = (q : ℝ) ^ ∑ j ∈ Finset.range (n + 1), (A c j + η) := by
              rw [Fin.sum_univ_eq_sum_range (fun j => A c j + η) (n + 1)]
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

end Est

end SieveTypeIIHM

#print axioms SieveTypeIIHM.fullEst_of_tight
