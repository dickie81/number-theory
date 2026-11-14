/-
# The resonant window on tuples of primes with a given product, in no order

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveTwoChain.chain_two` evaluates a family of tuples of primes, in no order, with two of their products as the
variables of the estimate in two variables and the other primes as the rest. This file is the same with the
resonant window's estimate (`SieveTypeIIHM.typeII_res`): one variable, the product of the primes outside a set
`Rs`, and the primes of `Rs` as the rest, each with its own lower bound. The tuples of the variable with a given
product number at most `(K + 1)^K` (`SieveTwoTuples.card_fiber_le`), so a polynomial over them is a polynomial over
the integers with coefficients at most `(K + 1)^K`.

* `box_res_gen`: **the resonant estimate for a polynomial over a finite set** with values in `(P, 2P]`, at most `D`
  elements for each value and coefficients `|f| ≤ 1`: the sum over `χ ≠ 1` of `|Σ_x f(x)χ(nv x)|·|∏_j Sp_j(χ)|` is at
  most `D·q^{L − 1/50000}` where `ResCond` holds.
* `chain_res_core`: **families of tuples of primes, by the resonant window**: `SieveTwoChain.chain_two_core` with
  one variable, the product of the entries outside the rest `r 0, …, r n`, in `(P, P′]`, each `z (r i) ≥ 2q^{lo i}`,
  given `ResCond` at the variable's blocks and the rest's scales.

The file imports `SieveResChain.lean` and `SieveTwoChain.lean`.
-/
import SieveResChain
import SieveTwoChain

open Real Finset

namespace SieveTypeIIHM

open SieveTypeIIGen SieveTwoTuples

/-- **The resonant estimate for a polynomial over a finite set.** For a curve `g ≤ 1` with `g(1/2) = 1` and its
counts, `K₀` and `e₁ > 0`: for large `q`, a finite set `X` with values `nv x ∈ (P, 2P]`, at most `D` elements for
each value, coefficients `|f| ≤ 1` on `X`, `n + 1 ≤ K₀` scales `Q_j ≥ q^{e₁}` with heights `|h_j| ≤ q^{1/100000}` and
`∏Q_j ≤ 2^{K₀}q^L/P`, and `ResCond` at `log_q P` and `log_q Q_j`: `Σ_{χ≠1} |Σ_x f(x)χ(nv x)|·|∏_j Sp(χ, Q_j, h_j)|` is
at most `D·q^{L − 1/50000}`. The polynomial over `X` is the polynomial over the values with the fibres' sums as its
coefficients (`SieveTwoTuples.dp_image`), whose mean square is at most `D²` (`sqrt_fiber_le`, `sqrt_sum_le`). -/
theorem box_res_gen {g : ℝ → ℝ} {L : ℝ} (hg1 : ∀ σ, g σ ≤ 1) (hg0 : g (1 / 2) = 1) (hcnt : CurveCounts g)
    (K₀ : ℕ) {e₁ : ℝ} (he₁ : 0 < e₁) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ {ι : Type} (X : Finset ι) (nv : ι → ℕ) (P : ℕ), 0 < P → (∀ x ∈ X, nv x ∈ Finset.Ioc P (2 * P)) →
      ∀ (D : ℕ), (∀ m, (X.filter (fun x => nv x = m)).card ≤ D) →
      ∀ (f : ι → ℂ), (∀ x ∈ X, ‖f x‖ ≤ 1) →
      ∀ (n : ℕ), n + 1 ≤ K₀ → ∀ Q hh : ℕ → ℝ,
      (∀ j < n + 1, (q : ℝ) ^ e₁ ≤ Q j ∧ |hh j| ≤ (q : ℝ) ^ (1 / 100000 : ℝ)) →
      ∏ j ∈ Finset.range (n + 1), Q j ≤ 2 ^ K₀ * (q : ℝ) ^ L / (P : ℝ) →
      ResCond g L (n + 1) (Real.logb q P) (fun j => Real.logb q (Q j)) →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖∑ x ∈ X, f x * χ ((nv x : ℕ) : ZMod q)‖ *
            ‖∏ j ∈ Finset.range (n + 1), SieveWeight.Sp χ SieveDyadic.bump (Q j) (hh j)‖ ≤
        D * (q : ℝ) ^ (L - 1 / 50000) := by
  obtain ⟨q₀, hq₀⟩ := typeII_res hg1 hg0 hcnt (f0 := SieveDyadic.bump) (SieveDyadic.contDiff_bump (n := ⊤))
    SieveDyadic.bump_support K₀ he₁ (η := 1 / 100000) (by norm_num) le_rfl
  refine ⟨q₀, fun q _ hq ι X nv P hP hXv D hD f hf n hn Q hh hQh hprod hres => ?_⟩
  have hdp : ∀ χ : DirichletCharacter ℂ q, ∑ x ∈ X, f x * χ ((nv x : ℕ) : ZMod q) =
      DirMean.dp (X.image nv) (fun m => (∑ x ∈ X.filter (fun x => nv x = m), f x) * χ m) 0 :=
    fun χ => (dp_image X nv f χ).symm
  simp_rw [hdp]
  have hS : X.image nv ⊆ Finset.Ioc P (2 * P) := fun m hm => by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hm
    exact hXv x hx
  have hmain := hq₀ q hq P (X.image nv) hS hP (fun m => ∑ x ∈ X.filter (fun x => nv x = m), f x) 0 (n + 1) hn
    Q hh hQh hprod hres
  refine hmain.trans ?_
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have h1 := sqrt_fiber_le X nv f hP0 hD
  have h2 := sqrt_sum_le X nv f hXv hD hf
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have h3 : Real.sqrt ((D : ℝ) / P) * Real.sqrt ((D : ℝ) * P) = D := by
    rw [← Real.sqrt_mul (by positivity), show (D : ℝ) / P * (D * P) = D ^ 2 by field_simp]
    exact Real.sqrt_sq hD0
  have hq0 : (0 : ℝ) ≤ (q : ℝ) ^ (L - 1 / 50000) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc (q : ℝ) ^ (L - 1 / 50000) *
        Real.sqrt ((∑ m ∈ X.image nv, ‖∑ x ∈ X.filter (fun x => nv x = m), f x‖ ^ 2) / P)
      ≤ (q : ℝ) ^ (L - 1 / 50000) * (Real.sqrt ((D : ℝ) / P) * Real.sqrt ((D : ℝ) * P)) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) hq0
        exact mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ = D * (q : ℝ) ^ (L - 1 / 50000) := by rw [h3]; ring

section Chain

open SieveChain SieveFamily SieveTypeIIU SieveTwoChain Classical

/-- **Families of tuples of primes, by the resonant window.** `SieveTwoChain.chain_two_core` with one variable: for a
curve `g ≤ 1` with `g(1/2) = 1` and its counts, `0 < L ≤ 5/2`, `e₀ > 0`, `K`, `J₀` and `Λ₁ ≥ 0`, there are `δ > 0`
and `q₀` such that for `q ≥ q₀` and a unit `a` mod `q`: let the rest be the positions `r 0, …, r n` (`r` injective)
with numbers `lo i`, and let `z` run over the `K`-tuples of primes up to `⌊2q^L⌋` that satisfy at most `J₀`
comparisons `Ω` with constants at most `Λ₁ log q`, each with its entries at least `q^{e₀}`, `z (r i) ≥ 2q^{lo i}`,
the product `W` of its entries outside the rest in `(P, P′]` and `∏z ≤ 2q^L`. If `ResCond` holds at `log_q P″` for
`P″ ≥ P` and the exponents of scales `Q_i ≥ q^{e₀/2}`, `Q_i ≥ q^{lo i}` with `∏Q_i ≤ 2^{K+1}q^L/P″`, then
`|Σ_z (1[∏z ≡ a] − 1[(∏z, q) = 1]/φ(q))| ≤ q^{L−δ}/φ(q)`.

The proof is `chain_two_core`'s with the two variables as one: the tuples of the variable, with the comparisons
that have no prime of the rest, are the polynomial part, cut into dyadic blocks of `W`; the comparisons with a prime
of the rest are pivoted there; `SieveUnwGen.unw_gen_lo` applies, with `box_res_gen` on each block (a tuple of the
variable is one of at most `(K + 1)^K` with its product, `SieveTwoTuples.card_fiber_le`). -/
theorem chain_res_core {g : ℝ → ℝ} {L : ℝ} (hg1 : ∀ σ, g σ ≤ 1) (hg0 : g (1 / 2) = 1) (hcnt : CurveCounts g)
    (hL0 : 0 < L) (hL : L ≤ 5 / 2) {e₀ : ℝ} (he₀ : 0 < e₀) (K J₀ : ℕ) {Λ₁ : ℝ} (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (n : ℕ) (r : Fin (n + 1) → Fin K), Function.Injective r → ∀ lo : ℕ → ℝ,
      ∀ (Ω : List (GCmp K)), Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      ∀ (P P' : ℕ), 1 ≤ P →
      (∀ P'' : ℕ, P ≤ P'' → ∀ Q : ℕ → ℝ, (∀ j < n + 1, (q : ℝ) ^ (e₀ / 2) ≤ Q j) →
        (∀ j < n + 1, (q : ℝ) ^ lo j ≤ Q j) →
        ∏ j ∈ Finset.range (n + 1), Q j ≤ 2 ^ (K + 1) * (q : ℝ) ^ L / (P'' : ℝ) →
        ResCond g L (n + 1) (Real.logb q P'') (fun j => Real.logb q (Q j))) →
      (∀ z : Fin K → ℕ, (∀ t, (z t).Prime) → (∀ C ∈ Ω, C.holds 0 z) →
        (∀ t, (q : ℝ) ^ e₀ ≤ z t) ∧ (∀ i : Fin (n + 1), 2 * (q : ℝ) ^ lo i ≤ z (r i)) ∧
          P < ∏ t ∈ (Finset.univ.image r)ᶜ, z t ∧ ∏ t ∈ (Finset.univ.image r)ᶜ, z t ≤ P' ∧
          ((∏ t, z t : ℕ) : ℝ) ≤ 2 * (q : ℝ) ^ L) →
      ‖∑ z ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω, dw q a (∏ t, z t)‖ ≤ (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = (K + 1) ^ K := ⟨_, rfl⟩
  have hD1 : 1 ≤ D := by rw [hD]; exact Nat.one_le_pow _ _ (by omega)
  have he₁ : 0 < e₀ / 2 := half_pos he₀
  have hΛ' : 0 ≤ Λ₁ + K * (L + 1) := by positivity
  obtain ⟨δ, hδ, q₁, hq₁⟩ := SieveUnwGen.unw_gen_lo (ι := Fin K → ℕ) (κ := ℕ) K J₀ 1 hL0 hL he₁ zero_le_one hΛ'
  obtain ⟨q₂, hq₂⟩ := box_res_gen hg1 hg0 hcnt (L := L) (K + 1) he₁
  have hev1 := (tendsto_rpow_atTop he₁).eventually_ge_atTop (2 : ℝ)
  have hev3 := (tendsto_rpow_atTop (show (0 : ℝ) < δ / 2 by positivity)).eventually_ge_atTop (D : ℝ)
  obtain ⟨q₃, hq₃⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually (hev1.and hev3))
  refine ⟨δ / 2, half_pos hδ, max (max q₁ q₂) (max q₃ 2), ?_⟩
  intro q _ hq a ha n r hr lo Ω hΩlen hΩc P P' hP hRes hreg
  have hq1 : q₁ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hq2 : q₂ ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  obtain ⟨hqe, hqD⟩ := hq₃ q (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hq)
  have hq3 : 2 ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hq
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1' : (1 : ℝ) < q := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hqR
  have hlogq0 : 0 ≤ Real.log q := by linarith
  have hqL0 : 0 < (q : ℝ) ^ L := Real.rpow_pos_of_pos hq0 _
  have hqL1 : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow (by linarith) hL0.le
  have hqe2 : (2 : ℝ) * (q : ℝ) ^ (e₀ / 2) ≤ (q : ℝ) ^ e₀ := by
    have h1 : (q : ℝ) ^ e₀ = (q : ℝ) ^ (e₀ / 2) * (q : ℝ) ^ (e₀ / 2) := by
      rw [← Real.rpow_add hq0]; ring_nf
    rw [h1]
    have h2 : (0 : ℝ) ≤ (q : ℝ) ^ (e₀ / 2) := by positivity
    nlinarith
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ, Y = ⌊2 * (q : ℝ) ^ L⌋₊ := ⟨_, rfl⟩
  rw [← hY]
  have hY1 : 1 ≤ Y := by rw [hY]; exact Nat.le_floor (by push_cast; linarith)
  have hY0 : Y ≠ 0 := by omega
  have hYle : (Y : ℝ) ≤ 2 * (q : ℝ) ^ L := by rw [hY]; exact Nat.floor_le (by positivity)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = Nat.log 2 Y + 1 := ⟨_, rfl⟩
  have hNlog : (Nat.log 2 Y : ℝ) ≤ 1 + 4 * Real.log q := by
    have h1 : ((2 ^ Nat.log 2 Y : ℕ) : ℝ) ≤ Y := by exact_mod_cast Nat.pow_log_le_self 2 hY0
    push_cast at h1
    have h3 : Real.log ((2 : ℝ) ^ Nat.log 2 Y) ≤ Real.log (2 * (q : ℝ) ^ L) :=
      Real.log_le_log (by positivity) (h1.trans hYle)
    rw [Real.log_pow, Real.log_mul (by norm_num) hqL0.ne', Real.log_rpow hq0] at h3
    have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    refine le_of_mul_le_mul_right ?_ hlog2
    nlinarith [hL, hL0]
  have hMle : (M : ℝ) ≤ 3 + 4 * Real.log q := by rw [hM]; push_cast; linarith
  -- logarithms of the entries
  have hlogY : ∀ m : ℕ, 1 ≤ m → m ≤ Y → Real.log (m : ℝ) ≤ (L + 1) * Real.log q := by
    intro m hm1 hmY
    have h1 : (m : ℝ) ≤ (q : ℝ) ^ (L + 1) := by
      rw [Real.rpow_add hq0, Real.rpow_one]
      have h2 : (m : ℝ) ≤ Y := by exact_mod_cast hmY
      nlinarith
    have h3 := Real.log_le_log (by exact_mod_cast hm1) h1
    rwa [Real.log_rpow hq0] at h3
  -- the rest and the variable
  obtain ⟨Rs, hRs⟩ : ∃ Rs : Finset (Fin K), Rs = Finset.univ.image r := ⟨_, rfl⟩
  rw [← hRs] at hreg
  obtain ⟨V, hV⟩ : ∃ V : Finset (Fin K), V = Rsᶜ := ⟨_, rfl⟩
  rw [← hV] at hreg
  have hσmem : ∀ i, r i ∈ Rs := fun i => by rw [hRs]; exact Finset.mem_image_of_mem r (Finset.mem_univ i)
  let σ : Fin (n + 1) ≃ {t // t ∈ Rs} := Equiv.ofBijective (fun i => ⟨r i, hσmem i⟩)
    ⟨fun i j h => hr (congrArg Subtype.val h), fun ⟨t, ht⟩ => by
      rw [hRs] at ht
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht
      exact ⟨i, rfl⟩⟩
  have hσ : ∀ i, (σ i : Fin K) = r i := fun i => rfl
  have hnK : n + 1 ≤ K := by
    have h1 : (Finset.univ.image r).card = n + 1 := by
      rw [Finset.card_image_of_injective _ hr, Finset.card_univ, Fintype.card_fin]
    have h2 := Finset.card_le_univ (Finset.univ.image r)
    rw [Fintype.card_fin] at h2
    omega
  have hVR : Disjoint V Rs := by rw [hV]; exact disjoint_compl_left
  have hVRu : V ∪ Rs = Finset.univ := by rw [hV, Finset.union_comm]; exact Finset.union_compl _
  have hnotRs : ∀ t, t ∉ Rs → t ∈ V := fun t ht => by rw [hV]; exact Finset.mem_compl.2 ht
  have hinRs : ∀ t, t ∈ Rs → t ∉ V := fun t ht => by rw [hV, Finset.mem_compl, not_not]; exact ht
  -- the comparisons with a prime of the rest, and those without
  obtain ⟨lp, hlp⟩ : ∃ l : List (GCmp K), l = Ω.filter (fun C => decide (∃ t ∈ Rs, C.e t ≠ 0)) := ⟨_, rfl⟩
  obtain ⟨lf, hlf⟩ : ∃ l : List (GCmp K), l = Ω.filter (fun C => decide (∀ t ∈ Rs, C.e t = 0)) := ⟨_, rfl⟩
  have hmem_lp : ∀ C, C ∈ lp ↔ C ∈ Ω ∧ ∃ t ∈ Rs, C.e t ≠ 0 := fun C => by
    rw [hlp, List.mem_filter, decide_eq_true_eq]
  have hmem_lf : ∀ C, C ∈ lf ↔ C ∈ Ω ∧ ∀ t ∈ Rs, C.e t = 0 := fun C => by
    rw [hlf, List.mem_filter, decide_eq_true_eq]
  have hlp_len : lp.length ≤ J₀ := by rw [hlp]; exact (List.length_filter_le _ _).trans hΩlen
  have hex : ∀ j : Fin lp.length, ∃ i : Fin (n + 1), (lp.get j).e (σ i) = 1 ∨ (lp.get j).e (σ i) = -1 := by
    intro j
    obtain ⟨-, t, ht, hne'⟩ := (hmem_lp _).1 (List.get_mem lp j)
    refine ⟨σ.symm ⟨t, ht⟩, ?_⟩
    rw [Equiv.apply_symm_apply]
    rcases (lp.get j).he t with h | h | h
    · exact Or.inr h
    · exact absurd h hne'
    · exact Or.inl h
  choose piv hpiv using hex
  -- a comparison with no prime of the rest, at a product with the rest
  have hfree : ∀ C : GCmp K, (∀ t ∈ Rs, C.e t = 0) → ∀ (z : Fin K → ℕ) (x : Fin (n + 1) → ℕ),
      (∀ t, 1 ≤ z t) → (∀ i, 1 ≤ x i) → (C.holds 0 (z * pad σ x) ↔ C.holds 0 z) := by
    intro C hC z x hz1 hx1
    unfold GCmp.holds
    rw [form_eq, form_eq, lin_mul C hz1 (pad_pos σ hx1),
      lin_eq_zero hC (fun t ht => pad_of_notMem σ x ht), add_zero]
  have hΩiff : ∀ (z : Fin K → ℕ) (x : Fin (n + 1) → ℕ), (∀ t, 1 ≤ z t) → (∀ i, 1 ≤ x i) →
      ((∀ C ∈ Ω, C.holds 0 (z * pad σ x)) ↔
        (∀ C ∈ lf, C.holds 0 z) ∧ ∀ j : Fin lp.length, PrOf (lp.get j) σ z x) := by
    intro z x hz1 hx1
    constructor
    · intro h
      refine ⟨fun C hC => ?_, fun j => ?_⟩
      · obtain ⟨hCΩ, hCf⟩ := (hmem_lf C).1 hC
        exact (hfree C hCf z x hz1 hx1).1 (h C hCΩ)
      · exact (PrOf_iff _ σ hz1 hx1).2 (h _ ((hmem_lp _).1 (List.get_mem lp j)).1)
    · rintro ⟨h1, h2⟩ C hC
      by_cases hCp : ∃ t ∈ Rs, C.e t ≠ 0
      · obtain ⟨j, rfl⟩ := List.mem_iff_get.1 ((hmem_lp C).2 ⟨hC, hCp⟩)
        exact (PrOf_iff _ σ hz1 hx1).1 (h2 j)
      · have hCf : ∀ t ∈ Rs, C.e t = 0 := fun t ht => by
          by_contra hne'
          exact hCp ⟨t, ht, hne'⟩
        exact (hfree C hCf z x hz1 hx1).2 (h1 C ((hmem_lf C).2 ⟨hC, hCf⟩))
  -- the polynomial part: the tuples of the variable in `(P, P′]`, with the comparisons without the rest
  obtain ⟨Xs, hXs⟩ : ∃ X : Finset (Fin K → ℕ), X = (padded V Y).filter (fun z =>
      (P < ∏ t, z t ∧ ∏ t, z t ≤ P' ∧ ∏ t, z t ≤ Y) ∧ ∀ C ∈ lf, C.holds 0 z) := ⟨_, rfl⟩
  have hmemXs : ∀ z, z ∈ Xs ↔ z ∈ padded V Y ∧
      ((P < ∏ t, z t ∧ ∏ t, z t ≤ P' ∧ ∏ t, z t ≤ Y) ∧ ∀ C ∈ lf, C.holds 0 z) := fun z => by
    rw [hXs, Finset.mem_filter]
  have hprodV : ∀ z ∈ padded V Y, ∏ t ∈ V, z t = ∏ t, z t := fun z hz =>
    Finset.prod_subset (Finset.subset_univ _) fun t _ ht => (mem_padded.1 hz).2 t ht
  -- the full tuple of a polynomial part and a rest
  have hprime : ∀ z ∈ padded V Y, ∀ x : Fin (n + 1) → ℕ, (∀ i, (x i).Prime) →
      ∀ t, ((z * pad σ x) t).Prime := by
    intro z hzp x hx t
    by_cases ht : t ∈ Rs
    · have hzt : z t = 1 := (mem_padded.1 hzp).2 t (hinRs t ht)
      rw [Pi.mul_apply, hzt, one_mul]
      unfold pad
      rw [dite_eq_left ht]
      exact hx _
    · rw [Pi.mul_apply, pad_of_notMem σ x ht, mul_one]
      exact (mem_primesLe.1 ((mem_padded.1 hzp).1 t (hnotRs t ht))).2
  have hprodw : ∀ (z : Fin K → ℕ) (x : Fin (n + 1) → ℕ), ∏ t, (z * pad σ x) t = (∏ t, z t) * ∏ i, x i := by
    intro z x
    rw [← prod_pad σ x, ← Finset.prod_mul_distrib]
    rfl
  -- the dyadic blocks of the variable
  have hblk : ∀ {m : ℕ}, P < m → m ≤ Y → Nat.log 2 ((m - 1) / P) ∈ Finset.range M := by
    intro m hPm hmY
    obtain ⟨h1, -⟩ := blk_spec hP hPm
    rw [Finset.mem_range, hM, Nat.lt_succ_iff]
    refine Nat.le_log_of_pow_le (by norm_num) ?_
    exact le_trans (Nat.le_mul_of_pos_left _ (by omega)) (le_trans h1.le hmY)
  have hpos : ∀ b : ℕ, 0 < P * 2 ^ b := fun b => Nat.mul_pos (by omega) (by positivity)
  have hblkval : ∀ b, ∀ z ∈ Xs.filter (fun z => Nat.log 2 ((∏ t, z t - 1) / P) = b),
      ∏ t, z t ∈ Finset.Ioc (P * 2 ^ b) (2 * (P * 2 ^ b)) := by
    intro b z hz
    obtain ⟨hzX, hzb⟩ := Finset.mem_filter.1 hz
    obtain ⟨-, ⟨h1, -, -⟩, -⟩ := (hmemXs z).1 hzX
    have h := blk_spec hP h1
    rw [hzb] at h
    exact Finset.mem_Ioc.2 h
  have hblkfib : ∀ b m, ((Xs.filter (fun z => Nat.log 2 ((∏ t, z t - 1) / P) = b)).filter
      (fun z => ∏ t, z t = m)).card ≤ D := by
    intro b m
    refine le_trans (Finset.card_le_card ?_) (hD ▸ card_fiber_le V Y m)
    intro z hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
    exact Finset.mem_filter.2 ⟨((hmemXs z).1 (Finset.mem_filter.1 hz1).1).1, hz2⟩
  have hexp1 : ∀ r' : ℝ, ‖Complex.exp (2 * π * Complex.I * (r' : ℂ))‖ = 1 := fun r' => by
    have : 2 * π * Complex.I * (r' : ℂ) = ((2 * π * r' : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  -- the family as a family with an abstract polynomial part
  have hkey : ‖Dsum q a (Xs ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe Y))
      (fun mx => (∏ t, mx.1 t) * ∏ i, mx.2 i)
      (fun mx => (1 : ℂ) *
        ∏ j : Fin lp.length, ((if PrOf (lp.get j) σ mx.1 mx.2 then 1 else 0 : ℝ) : ℂ))‖ ≤
      (q.totient : ℝ)⁻¹ * ((D : ℝ) * (q : ℝ) ^ (L - δ)) := by
    rw [hY]
    rw [hY] at hmemXs hprodV hprime hblk hlogY
    refine hq₁ q hq1 a ha Xs (fun z => ∏ t, z t) (fun _ => (1 : ℂ)) (D : ℝ) (Nat.cast_nonneg _)
      (fun z => Nat.log 2 ((∏ t, z t - 1) / P)) (Finset.range M) (fun b => ((P * 2 ^ b : ℕ) : ℝ)) ?_ ?_ ?_ ?_ ?_
      n hnK lo hlp_len (fun j z => (lp.get j).c 0 + lin (lp.get j) z) (fun j i => (lp.get j).e (σ i))
      (fun j z x => PrOf (lp.get j) σ z x) ?_ (fun j z x => PrOf_spec (lp.get j) σ z x) ?_ piv hpiv ?_ ?_
    · -- the labels
      intro z hz
      obtain ⟨-, ⟨h1, -, h1Y⟩, -⟩ := (hmemXs z).1 hz
      exact hblk h1 h1Y
    · -- their number
      rw [Finset.card_range, pow_one]
      exact hMle
    · -- the sizes are positive
      intro b _
      exact_mod_cast hpos b
    · -- a tuple is above the size of its block
      intro z hz
      obtain ⟨-, ⟨h1, -, -⟩, -⟩ := (hmemXs z).1 hz
      obtain ⟨h1', -⟩ := blk_spec hP h1
      exact_mod_cast h1'
    · -- the number of tuples of a block
      intro b _
      have hcN : (Xs.filter (fun z => Nat.log 2 ((∏ t, z t - 1) / P) = b)).card ≤ D * (P * 2 ^ b) :=
        card_le_of_fibers (P := P * 2 ^ b) (D := D) (Xs.filter (fun z => Nat.log 2 ((∏ t, z t - 1) / P) = b))
          (fun z : Fin K → ℕ => ∏ t, z t) (fun z hz => hblkval b z hz) (fun m => hblkfib b m)
      have hc : ((Xs.filter (fun z => Nat.log 2 ((∏ t, z t - 1) / P) = b)).card : ℝ) ≤
          (D : ℝ) * ((P * 2 ^ b : ℕ) : ℝ) := by
        rw [← Nat.cast_mul]
        exact Nat.cast_le.2 hcN
      calc ∑ z ∈ Xs.filter (fun z => Nat.log 2 ((∏ t, z t - 1) / P) = b), ‖(1 : ℂ)‖
          = ((Xs.filter (fun z => Nat.log 2 ((∏ t, z t - 1) / P) = b)).card : ℝ) := by simp
        _ ≤ (D : ℝ) * (P * 2 ^ b : ℕ) := hc
        _ = ((P * 2 ^ b : ℕ) : ℝ) * D := by ring
    · -- the coefficients of the forms
      intro j i
      rcases (lp.get j).he (σ i) with h | h | h <;> rw [h] <;> norm_num
    · -- the polynomial parts of the forms
      intro j z hz
      have h1 := hΩc _ ((hmem_lp _).1 (List.get_mem lp j)).1
      obtain ⟨hzp, -⟩ := (hmemXs z).1 hz
      have h2 : lin (lp.get j) z ≤ K * ((L + 1) * Real.log q) := by
        unfold lin
        calc ∑ t, (lp.get j).e t * Real.log (z t) ≤ ∑ _t : Fin K, (L + 1) * Real.log q := by
              refine Finset.sum_le_sum fun t _ => ?_
              have hz1 : (1 : ℝ) ≤ z t := by exact_mod_cast padded_pos hzp t
              have hlz0 : 0 ≤ Real.log (z t) := Real.log_nonneg hz1
              have hzY : z t ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := by
                by_cases ht : t ∈ V
                · exact (mem_primesLe.1 ((mem_padded.1 hzp).1 t ht)).1
                · rw [(mem_padded.1 hzp).2 t ht]
                  exact hY ▸ hY1
              have hlz := hlogY (z t) (padded_pos hzp t) hzY
              have hLq : 0 ≤ (L + 1) * Real.log q := by positivity
              rcases (lp.get j).he t with h | h | h <;> rw [h] <;> nlinarith
          _ = K * ((L + 1) * Real.log q) := by simp
      show (lp.get j).c 0 + lin (lp.get j) z ≤ (Λ₁ + K * (L + 1)) * Real.log q
      nlinarith
    · -- the primes of the rest and the product
      intro z hz x hx hall
      obtain ⟨hzp, -, hzf⟩ := (hmemXs z).1 hz
      have hz1 : ∀ t, 1 ≤ z t := padded_pos hzp
      have hx1 : ∀ i, 1 ≤ x i := fun i => (hx i).one_lt.le
      have hwΩ : ∀ C ∈ Ω, C.holds 0 (z * pad σ x) := (hΩiff z x hz1 hx1).2 ⟨hzf, hall⟩
      obtain ⟨hge, hlo, -, -, hprod⟩ := hreg _ (hprime z hzp x hx) hwΩ
      have hpadσ : ∀ i, (z * pad σ x) (r i) = x i := by
        intro i
        have hzt : z (r i) = 1 := (mem_padded.1 hzp).2 _ (hinRs _ (hσmem i))
        rw [Pi.mul_apply, hzt, one_mul, ← hσ i, pad_apply]
      refine ⟨fun i => ?_, fun i => ?_, ?_⟩
      · have h1 := hge (r i)
        rw [hpadσ i] at h1
        linarith
      · have h1 := hlo i
        rw [hpadσ i] at h1
        exact h1
      · rw [hprodw z x] at hprod
        exact_mod_cast hprod
    · -- the estimate on a block
      intro b _ Q hQe hQlo hQP c' hc' ξ κ' hh hhh
      have hc1 : c' = fun _ => (1 : ℂ) := by
        rcases hc' with rfl | rfl
        · rfl
        · funext z
          simp
      rw [hc1]
      by_cases hne : (Xs.filter (fun z => Nat.log 2 ((∏ t, z t - 1) / P) = b)).Nonempty
      swap
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        simp only [hne, Finset.sum_empty, norm_zero, zero_mul, Finset.sum_const_zero]
        positivity
      obtain ⟨z₀, hz₀⟩ := hne
      have hPb : P ≤ P * 2 ^ b := Nat.le_mul_of_pos_right P (by positivity)
      have hRb := hRes (P * 2 ^ b) hPb Q hQe hQlo (by rw [show K + 1 = K + 1 from rfl]; exact hQP)
      have hb := hq₂ q hq2 (Xs.filter (fun z => Nat.log 2 ((∏ t, z t - 1) / P) = b)) (fun z => ∏ t, z t)
        (P * 2 ^ b) (hpos b) (hblkval b) D (hblkfib b)
        (fun z => (1 : ℂ) * Complex.exp (2 * π * Complex.I *
          ((κ' + ∑ j : Fin lp.length, ξ j * ((lp.get j).c 0 + lin (lp.get j) z) : ℝ) : ℂ)))
        (fun z _ => by rw [norm_mul, norm_one, one_mul, hexp1]) n (by omega) Q hh
        (fun j hj => ⟨hQe j hj, hhh j hj⟩) hQP hRb
      exact hb
  -- the family's sum is that family's
  have hident : ∑ z ∈ RTg K Y Ω, dw q a (∏ t, z t) =
      Dsum q a (Xs ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe Y))
        (fun mx => (∏ t, mx.1 t) * ∏ i, mx.2 i)
        (fun mx => (1 : ℂ) *
          ∏ j : Fin lp.length, ((if PrOf (lp.get j) σ mx.1 mx.2 then 1 else 0 : ℝ) : ℂ)) := by
    unfold Dsum
    have hpu : padded (Finset.univ : Finset (Fin K)) Y = padded (V ∪ Rs) Y := by rw [hVRu]
    rw [RTg, Finset.sum_filter, ← padded_univ, hpu, sum_padded_mul hVR, Finset.sum_product]
    have hXsub : Xs ⊆ padded V Y := by rw [hXs]; exact Finset.filter_subset _ _
    have h0 : ∀ z ∈ padded V Y, z ∉ Xs →
        ∑ w ∈ padded Rs Y, (if ∀ C ∈ Ω, C.holds 0 (z * w) then dw q a (∏ t, (z * w) t) else 0) = 0 := by
      intro z hzp hzX
      refine Finset.sum_eq_zero fun w hw => ?_
      rw [ite_eq_right]
      intro hall
      exfalso
      apply hzX
      obtain ⟨x, hxw, hxp⟩ : ∃ x : Fin (n + 1) → ℕ, pad σ x = w ∧ ∀ i, (x i).Prime :=
        ⟨fun i => w (σ i), pad_read σ (mem_padded.1 hw).2,
          fun i => (mem_primesLe.1 ((mem_padded.1 hw).1 _ (σ i).2)).2⟩
      rw [← hxw] at hall
      have hz1 : ∀ t, 1 ≤ z t := padded_pos hzp
      have hx1 : ∀ i, 1 ≤ x i := fun i => (hxp i).one_lt.le
      obtain ⟨-, -, h1, h2, h5⟩ := hreg _ (hprime z hzp x hxp) hall
      have hw1 : ∀ t ∉ Rs, pad σ x t = 1 := fun t ht => pad_of_notMem σ x ht
      rw [prod_part_mul hVR z hw1, hprodV z hzp] at h1 h2
      have hle : ∏ t, (z * pad σ x) t ≤ Y := by rw [hY]; exact Nat.le_floor h5
      rw [hprodw z x] at hle
      have hx0 : 0 < ∏ i, x i := Finset.prod_pos fun i _ => hx1 i
      have hYz : ∏ t, z t ≤ Y := le_trans (Nat.le_mul_of_pos_right _ hx0) hle
      exact (hmemXs z).2 ⟨hzp, ⟨h1, h2, hYz⟩, ((hΩiff z x hz1 hx1).1 hall).1⟩
    rw [← Finset.sum_subset hXsub h0]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [sum_padded_fin σ]
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hzp, -, hzf⟩ := (hmemXs z).1 hz
    have hz1 : ∀ t, 1 ≤ z t := padded_pos hzp
    have hx1 : ∀ i, 1 ≤ x i := fun i => (mem_primesLe.1 (Fintype.mem_piFinset.1 hx i)).2.one_lt.le
    have hcast : ∀ j : Fin lp.length, (((if PrOf (lp.get j) σ z x then 1 else 0 : ℝ)) : ℂ) =
        if PrOf (lp.get j) σ z x then 1 else 0 := fun j => by split_ifs <;> simp
    simp only [hcast]
    rw [Finset.prod_boole, hprodw z x]
    by_cases hall : ∀ C ∈ Ω, C.holds 0 (z * pad σ x)
    · rw [ite_eq_left hall, ite_eq_left (fun j _ => ((hΩiff z x hz1 hx1).1 hall).2 j), one_mul, one_mul]
    · rw [ite_eq_right hall,
        ite_eq_right (fun h' => hall ((hΩiff z x hz1 hx1).2 ⟨hzf, fun j => h' j (Finset.mem_univ _)⟩)),
        mul_zero, zero_mul]
  rw [hident]
  refine hkey.trans ?_
  have hφ0 : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  calc (q.totient : ℝ)⁻¹ * ((D : ℝ) * (q : ℝ) ^ (L - δ))
      ≤ (q.totient : ℝ)⁻¹ * ((q : ℝ) ^ (δ / 2) * (q : ℝ) ^ (L - δ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hqD (Real.rpow_nonneg hq0.le _)) hφ0
    _ = (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ / 2) := by
        rw [← Real.rpow_add hq0]
        congr 2
        ring

end Chain

end SieveTypeIIHM

#print axioms SieveTypeIIHM.box_res_gen
#print axioms SieveTypeIIHM.chain_res_core
