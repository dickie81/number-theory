/-
# The test of the comparison in two variables for a tree of Buchstab steps is sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. The setting is a route with `RouteOK` whose exponent is `Lnum/Lden` (`SieveQ.IBFits`); the test is
`SieveAdTwoDefs.lean`'s `chkJ2`. Write `κ = L/DEN`, so that a number `n` of units of `1/DEN` of exponents of `x` is
the exponent `κn` of `q`.

* `mset k m`: the primes of a box of `k` primes at the positions whose bit is set in `m`; `sum_mset`: a sum over
  them is `mSum` on the list.
* `evJ_two`, `evJ_okJ2`: **the comparison in two variables on a box.** If `chkJ2` passes the box at the floor
  `f`, for the sets `s0`, `sr`, `s1`, the flag `e`, the window `[u, v]` and the growth `t`, the terms of the box at
  the floor `x^{f/DEN}` are evaluated (`SieveAd.EvJ`): `SieveTwoComp.prop6_two_at` for the region
  `SieveTwoZone7D.Zone7d L` (`SieveFamilyTwo.typeIITwoAt_7d`), on the box's atoms, with the rests of exponent in
  `[κ(ρ₁ − 1), κ(ρ₂ + 1)]`.
* `chain2_exp`: `SieveTwoTerm.chain2_bound` for a first variable and a rest in ranges of exponents: the region is
  asked for a first variable of exponent in `[u − ε, v]` and a rest in `[ρ₁ − ε, ρ₂ + ε]`.
* `evI_two`, `evI_okI2`: **a box evaluated by the estimate.** If `chkI2` passes the box, for the first variable
  `s0` and the rest `sr`, the term of the box is evaluated (`SieveAd.EvI`), the second variable being the other
  primes and the cofactor.
* `twoTests_sound`: so the tests of the estimate in two variables are sound (`SieveAd.Tests.Sound`).

The file imports `SieveAdSpec.lean`, `SieveAdTwoDefs.lean` and `SieveTwoComp.lean`.
-/
import SieveAdSpec
import SieveAdTwoDefs
import SieveTwoComp

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRoute SieveChain SieveFamily

namespace SieveAd

open Classical
open SieveCert (DEN DEN_pos')

/-! ### Sets of primes by the bits of their positions -/

/-- The primes of a box of `k` primes at the positions whose bit is set in `m`. -/
def mset (k m : ℕ) : Finset (Fin k) := Finset.univ.filter fun i => Nat.testBit m (k - 1 - (i : ℕ)) = true

/-- A sum over the primes at the positions of `m` is `mSum` on the list. -/
theorem sum_mset (F : Cell → ℕ) :
    ∀ (bl : List Cell) (k : ℕ) (h : bl.length = k) (m : ℕ), ∑ i ∈ mset k m, F (boxFn bl k h i) = mSum F bl m := by
  intro bl
  induction bl with
  | nil =>
    intro k h m
    subst h
    simp [mset, mSum]
  | cons x bl ih =>
    intro k h m
    subst h
    show ∑ i ∈ mset (bl.length + 1) m, F (boxFn (x :: bl) (bl.length + 1) rfl i) = _
    rw [boxFn_cons x bl bl.length rfl, mset, Finset.sum_filter, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last, mSum]
    rw [← ih bl.length rfl (m / 2), mset, Finset.sum_filter, add_comm]
    congr 1
    · have : bl.length + 1 - 1 - bl.length = 0 := by omega
      rw [this]
      cases Nat.testBit m 0 <;> simp
    · refine Finset.sum_congr rfl fun j _ => ?_
      have hj := j.2
      have : bl.length + 1 - 1 - (j : ℕ) = (bl.length - 1 - (j : ℕ)) + 1 := by omega
      rw [this, Nat.testBit_succ]

theorem mSum_le (F G : Cell → ℕ) (bl : List Cell) (hFG : ∀ c ∈ bl, F c ≤ G c) (m : ℕ) :
    mSum F bl m ≤ mSum G bl m := by
  induction bl generalizing m with
  | nil => simp [mSum]
  | cons x bl ih =>
    have h1 := hFG x (List.mem_cons_self ..)
    have h2 := ih (fun c hc => hFG c (List.mem_cons_of_mem _ hc)) (m / 2)
    simp only [mSum]
    cases Nat.testBit m 0 <;> simp <;> omega

theorem cellsFrom_iff (f : ℕ) (bl : List Cell) :
    cellsFrom f bl = true ↔ ∀ c ∈ bl, f ≤ c.1 ∧ c.1 ≤ c.2 ∧ c.2 ≤ DEN := by
  induction bl with
  | nil => simp [cellsFrom]
  | cons x bl ih => simp [cellsFrom, ih, Nat.ble_eq, and_assoc]

/-- Sets with no common bit are disjoint. -/
theorem mset_disjoint (k : ℕ) {a b : ℕ} (h : a &&& b = 0) : Disjoint (mset k a) (mset k b) := by
  rw [mset, mset, Finset.disjoint_filter]
  intro i _ ha hb
  have : (a &&& b).testBit (k - 1 - (i : ℕ)) = true := by rw [Nat.testBit_and, ha, hb]; rfl
  rw [h, Nat.zero_testBit] at this
  exact Bool.false_ne_true this

/-- The sum over the complement of a set is the whole sum minus the set's. -/
theorem sum_mset_compl (bl : List Cell) (k : ℕ) (h : bl.length = k) (m : ℕ) :
    ∑ i ∈ (mset k m)ᶜ, (boxFn bl k h i).2 = hiSum bl - mSum (fun c => c.2) bl m := by
  have h1 := Finset.sum_add_sum_compl (mset k m) fun i => (boxFn bl k h i).2
  rw [sum_mset (fun c => c.2) bl k h m, sum_boxFn (fun c => c.2) bl k h, ← hiSum_eq] at h1
  omega

/-! ### The comparison in two variables on a box -/

variable [Route] [RouteOK] [SieveCert.IBPar] [IBFits]

open SieveCert.IBPar (Lnum Lden)

omit [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- A power of `q` with an exponent `κn`, `κ = L/DEN`, is the power `x^{n/DEN}`. -/
theorem qpow_eq (q : ℕ) (n : ℕ) : (q : ℝ) ^ (L / DEN * (n : ℝ)) = xq q ^ ((n : ℝ) / DEN) := by
  rw [xpow]
  congr 1
  ring

/-- `Lnum` and `Lden` are positive, and `Lnum = Lden·DEN·κ` for `κ = L/DEN`. -/
theorem lnum_eq : (0 : ℝ) < Lden ∧ (Lnum : ℝ) = (Lden : ℝ) * DEN * (L / DEN) := by
  have h := (IBFits.L_eq : (Lnum : ℝ) / Lden = L)
  have hL := (two_lt_L : (2 : ℝ) < L)
  have hD := DEN_pos'
  have hden : (Lden : ℝ) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at h
    linarith
  have hden' : (0 : ℝ) < Lden := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hden)
  refine ⟨hden', ?_⟩
  rw [← h]
  field_simp

omit [SieveCert.IBPar] [IBFits] in
/-- **Chains with the first variable and the rest in ranges of exponents.** Let `Rg` be a region of
`TypeIITwoAt L`, and let it hold at the `(m₁, m₂)` with `u − ε ≤ m₁ ≤ v` and `L − ρ₂ − ε ≤ m₁ + m₂ ≤ L − ρ₁ + ε`,
for `0 < u ≤ v`, `0 ≤ ρ₁ ≤ ρ₂`, `v + ρ₂ ≤ L` and `ε > 0`. Let `rt` run over the `(k′ + 1)`-tuples of primes up to
`N₂` that satisfy at most `J₀` comparisons, each strictly decreasing with entries at least `q^{e₀}`,
`q^u ≤ ∏_{i∈S} rt_i ≤ q^v` and `q^{ρ₁} ≤ ∏_{i∈Sr} rt_i ≤ q^{ρ₂}`, for disjoint sets `S` and `Sr ≠ ∅`. Then the
multiples `n ∈ (N₁, N₂]` of `∏rt` with no prime factor below `rt`'s last entry, summed over `rt`, have
`|A − B/φ(q)|` at most `q^{L−δ}/φ(q)`: `SieveTwoTerm.chain2_bound` with the windows `(⌈q^u⌉ − 1, ⌊q^v⌋]` and
`(⌈q^{ρ₁}⌉ − 1, ⌊q^{ρ₂}⌋]`. -/
theorem chain2_exp {Rg : ℝ → ℝ → Prop} (hII : SieveFamilyTwo.TypeIITwoAt L Rg) {e₀ : ℝ} (he₀ : 0 < e₀) (k' J₀ : ℕ) {Λ₁ : ℝ}
    (hΛ₁ : 0 ≤ Λ₁) {u v ρ₁ ρ₂ ε : ℝ} (hu : 0 < u) (huv : u ≤ v) (hρ₁0 : 0 ≤ ρ₁) (hρ : ρ₁ ≤ ρ₂) (hvρ : v + ρ₂ ≤ L)
    (hε : 0 < ε)
    (hzone : ∀ m₁ m₂ : ℝ, u - ε ≤ m₁ → m₁ ≤ v → L - ρ₂ - ε ≤ m₁ + m₂ → m₁ + m₂ ≤ L - ρ₁ + ε → Rg m₁ m₂) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (S Sr : Finset (Fin (k' + 1))) (Ω : List (GCmp (k' + 1))), Disjoint S Sr → Sr.Nonempty →
      Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      (∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
        StrictAnti rt ∧ (∀ i, (q : ℝ) ^ e₀ ≤ rt i) ∧ (q : ℝ) ^ u ≤ ((∏ i ∈ S, rt i : ℕ) : ℝ) ∧
          ((∏ i ∈ S, rt i : ℕ) : ℝ) ≤ (q : ℝ) ^ v ∧ (q : ℝ) ^ ρ₁ ≤ ((∏ i ∈ Sr, rt i : ℕ) : ℝ) ∧
          ((∏ i ∈ Sr, rt i : ℕ) : ℝ) ≤ (q : ℝ) ^ ρ₂) →
      ‖∑ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ L⌋₊ Ω,
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
            dw q a n * (if (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last k')) n then 1 else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  obtain ⟨δ, hδ, q₀, hq₀⟩ := SieveTwoTerm.chain2_bound hII he₀ k' J₀ hΛ₁
  have hLρ : 0 < L - ρ₂ := by linarith
  obtain ⟨q₁, hq₁⟩ := Filter.eventually_atTop.1 ((ev_rpow hε 8).and ((ev_rpow hLρ 2).and
    ((ev_rpow hu 2).and (Filter.eventually_ge_atTop 2))))
  refine ⟨δ, hδ, max q₀ q₁, fun q _ hq a ha S Sr Ω hdisj hSr hlen hc hreg => ?_⟩
  obtain ⟨h8ε, h2ρ, h2u, hq2⟩ := hq₁ q (le_trans (le_max_right _ _) hq)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1' : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hq1 : (1 : ℝ) ≤ q := hq1'.le
  have h2ε : (2 : ℝ) ≤ (q : ℝ) ^ ε := by linarith
  have hqρ₂1 : (1 : ℝ) ≤ (q : ℝ) ^ ρ₂ := Real.one_le_rpow hq1 (by linarith)
  have hqv2 : (2 : ℝ) ≤ (q : ℝ) ^ v := h2u.trans (Real.rpow_le_rpow_of_exponent_le hq1 huv)
  have hP₁ge : (q : ℝ) ^ u ≤ (⌈(q : ℝ) ^ u⌉₊ : ℝ) := Nat.le_ceil _
  have hP₁2 : 2 ≤ ⌈(q : ℝ) ^ u⌉₊ := by
    have : (2 : ℝ) ≤ (⌈(q : ℝ) ^ u⌉₊ : ℝ) := h2u.trans hP₁ge
    exact_mod_cast this
  have hP₂le : (⌊(q : ℝ) ^ v⌋₊ : ℝ) ≤ (q : ℝ) ^ v := Nat.floor_le (by positivity)
  have hBrle : (⌊(q : ℝ) ^ ρ₂⌋₊ : ℝ) ≤ (q : ℝ) ^ ρ₂ := Nat.floor_le (by positivity)
  have hP₂1 : 1 ≤ ⌊(q : ℝ) ^ v⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hBr1 : 1 ≤ ⌊(q : ℝ) ^ ρ₂⌋₊ := Nat.le_floor (by exact_mod_cast hqρ₂1)
  have hAr1 : 1 ≤ ⌈(q : ℝ) ^ ρ₁⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hArge : (q : ℝ) ^ ρ₁ ≤ (⌈(q : ℝ) ^ ρ₁⌉₊ : ℝ) := Nat.le_ceil _
  have hN₂r : (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) ≤ 2 * (q : ℝ) ^ L := Nat.floor_le (by positivity)
  have hBBr : ⌊(q : ℝ) ^ v⌋₊ * ⌊(q : ℝ) ^ ρ₂⌋₊ ≤ ⌊(q : ℝ) ^ L⌋₊ := by
    refine Nat.le_floor ?_
    push_cast
    calc (⌊(q : ℝ) ^ v⌋₊ : ℝ) * (⌊(q : ℝ) ^ ρ₂⌋₊ : ℝ) ≤ (q : ℝ) ^ v * (q : ℝ) ^ ρ₂ :=
          mul_le_mul hP₂le hBrle (Nat.cast_nonneg _) (by positivity)
      _ = (q : ℝ) ^ (v + ρ₂) := (Real.rpow_add hq0 _ _).symm
      _ ≤ (q : ℝ) ^ L := Real.rpow_le_rpow_of_exponent_le hq1 hvρ
  -- `⌈q^u⌉ − 1 ≥ q^{u−ε}`
  have hAcast : ((⌈(q : ℝ) ^ u⌉₊ - 1 : ℕ) : ℝ) = (⌈(q : ℝ) ^ u⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hAge : (q : ℝ) ^ (u - ε) ≤ ((⌈(q : ℝ) ^ u⌉₊ - 1 : ℕ) : ℝ) := by
    rw [hAcast]
    have e : (q : ℝ) ^ u = (q : ℝ) ^ (u - ε) * (q : ℝ) ^ ε := by
      rw [← Real.rpow_add hq0]; congr 1; ring
    have h0 : (0 : ℝ) < (q : ℝ) ^ (u - ε) := by positivity
    have h1 : (q : ℝ) ^ (u - ε) * 8 ≤ (q : ℝ) ^ u := by
      rw [e]
      exact mul_le_mul_of_nonneg_left h8ε h0.le
    linarith
  have hR : ∀ u' v' : ℝ, Real.logb q ((⌈(q : ℝ) ^ u⌉₊ - 1 : ℕ) : ℝ) ≤ u' →
      u' ≤ Real.logb q (⌊(q : ℝ) ^ v⌋₊ : ℝ) →
      ((⌊(q : ℝ) ^ L⌋₊ / ⌊(q : ℝ) ^ ρ₂⌋₊ : ℕ) : ℝ) ≤ 4 * (q : ℝ) ^ (u' + v') →
      (q : ℝ) ^ (u' + v') ≤ ((⌊2 * (q : ℝ) ^ L⌋₊ / (⌈(q : ℝ) ^ ρ₁⌉₊ - 1 + 1) : ℕ) : ℝ) → Rg u' v' := by
    intro u' v' h1 h2 h5 h6
    have hlogb : ∀ y : ℝ, Real.logb q ((q : ℝ) ^ y) = y := fun y => Real.logb_rpow hq0 hq1'.ne'
    refine hzone u' v' ?_ ?_ ?_ ?_
    · exact le_trans ((hlogb (u - ε)).symm.le.trans (Real.logb_le_logb_of_le hq1' (by positivity) hAge)) h1
    · exact h2.trans ((Real.logb_le_logb_of_le hq1' (by exact_mod_cast hP₂1) hP₂le).trans (hlogb v).le)
    · refine (Real.rpow_le_rpow_left_iff hq1').1 ?_
      have hm0 : (0 : ℝ) < (q : ℝ) ^ (L - ρ₂ - ε) := by positivity
      have hprod : (q : ℝ) ^ (L - ρ₂ - ε) * (q : ℝ) ^ ε * (q : ℝ) ^ ρ₂ = (q : ℝ) ^ L := by
        rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]; congr 1; ring
      have h8' : 8 * ((q : ℝ) ^ (L - ρ₂ - ε) * (q : ℝ) ^ ρ₂) ≤ (q : ℝ) ^ L := by
        have h := mul_le_mul_of_nonneg_left h8ε (mul_nonneg hm0.le (Real.rpow_nonneg hq0.le ρ₂))
        calc 8 * ((q : ℝ) ^ (L - ρ₂ - ε) * (q : ℝ) ^ ρ₂) = (q : ℝ) ^ (L - ρ₂ - ε) * (q : ℝ) ^ ρ₂ * 8 := by ring
          _ ≤ (q : ℝ) ^ (L - ρ₂ - ε) * (q : ℝ) ^ ρ₂ * (q : ℝ) ^ ε := h
          _ = (q : ℝ) ^ L := by rw [← hprod]; ring
      have h2' : 2 * (q : ℝ) ^ ρ₂ ≤ (q : ℝ) ^ L := by
        have e : (q : ℝ) ^ L = (q : ℝ) ^ (L - ρ₂) * (q : ℝ) ^ ρ₂ := by
          rw [← Real.rpow_add hq0]; congr 1; ring
        rw [e]
        exact mul_le_mul_of_nonneg_right h2ρ (by positivity)
      have hmle : ⌈4 * (q : ℝ) ^ (L - ρ₂ - ε)⌉₊ ≤ ⌊(q : ℝ) ^ L⌋₊ / ⌊(q : ℝ) ^ ρ₂⌋₊ := by
        refine (Nat.le_div_iff_mul_le hBr1).2 (Nat.le_floor ?_)
        push_cast
        have hc1 : (⌈4 * (q : ℝ) ^ (L - ρ₂ - ε)⌉₊ : ℝ) < 4 * (q : ℝ) ^ (L - ρ₂ - ε) + 1 :=
          Nat.ceil_lt_add_one (by positivity)
        have h3 : (⌈4 * (q : ℝ) ^ (L - ρ₂ - ε)⌉₊ : ℝ) * (⌊(q : ℝ) ^ ρ₂⌋₊ : ℝ) ≤
            (4 * (q : ℝ) ^ (L - ρ₂ - ε) + 1) * (q : ℝ) ^ ρ₂ :=
          mul_le_mul hc1.le hBrle (Nat.cast_nonneg _) (by positivity)
        linarith
      have h9 : 4 * (q : ℝ) ^ (L - ρ₂ - ε) ≤ ((⌊(q : ℝ) ^ L⌋₊ / ⌊(q : ℝ) ^ ρ₂⌋₊ : ℕ) : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hmle)
      linarith
    · refine (Real.rpow_le_rpow_left_iff hq1').1 (h6.trans ?_)
      rw [Nat.sub_add_cancel hAr1]
      calc ((⌊2 * (q : ℝ) ^ L⌋₊ / ⌈(q : ℝ) ^ ρ₁⌉₊ : ℕ) : ℝ)
          ≤ (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) / (⌈(q : ℝ) ^ ρ₁⌉₊ : ℝ) := Nat.cast_div_le
        _ ≤ (2 * (q : ℝ) ^ L) / (q : ℝ) ^ ρ₁ := div_le_div₀ (by positivity) hN₂r (by positivity) hArge
        _ = 2 * (q : ℝ) ^ (L - ρ₁) := by rw [mul_div_assoc, ← Real.rpow_sub hq0]
        _ ≤ (q : ℝ) ^ ε * (q : ℝ) ^ (L - ρ₁) := mul_le_mul_of_nonneg_right h2ε (by positivity)
        _ = (q : ℝ) ^ (L - ρ₁ + ε) := by rw [← Real.rpow_add hq0]; congr 1; ring
  refine hq₀ q (le_trans (le_max_left _ _) hq) a ha S Sr Ω (⌈(q : ℝ) ^ u⌉₊ - 1) ⌊(q : ℝ) ^ v⌋₊
    (⌈(q : ℝ) ^ ρ₁⌉₊ - 1) ⌊(q : ℝ) ^ ρ₂⌋₊ hdisj hSr hlen hc (by omega) hP₂1 hBr1 hBBr hR fun rt hp hΩ => ?_
  obtain ⟨hsa, hge, h1, h2, h3, h4⟩ := hreg rt hp hΩ
  refine ⟨hsa, hge, ?_, Nat.le_floor h2, ?_, Nat.le_floor h4⟩
  · have := Nat.ceil_le.2 h1
    omega
  · have := Nat.ceil_le.2 h3
    omega

/-- **The comparison in two variables on a box.** If `chkJ2` passes the box at the floor `f`, for the sets `s0`,
`sr`, `s1`, the flag `e`, the window `[u, v]` and the growth `t`, then the terms of the box at the floor `x^{f/DEN}`
are evaluated. -/
theorem evJ_two (bl : List Cell) (k : ℕ) (h : bl.length = k) (f s0 sr s1 : ℕ) (e : Bool) (u v t : ℕ)
    (hok : chkJ2 bl f s0 sr s1 e u v t = true) : EvJ f (boxFn bl k h) := by
  simp only [chkJ2, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hf0, hlen⟩, hcells⟩, hland⟩, z1⟩, z2⟩, z3⟩, z4⟩, z5⟩, z6⟩, p1⟩, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩ := hok
  have hland' : s0 &&& sr = 0 := Nat.eq_of_beq_eq_true hland
  have hc := (cellsFrom_iff f bl).1 hcells
  set bx := boxFn bl k h with hbx
  have hbxc : ∀ i, f ≤ (bx i).1 ∧ (bx i).1 ≤ (bx i).2 ∧ (bx i).2 ≤ DEN := fun i => hc _ (boxFn_mem bl k h i)
  -- the sums of the test
  set ρ₁ := mSum (fun c => c.1) bl sr with hρ₁
  set ρ₂ := mSum (fun c => c.2) bl sr with hρ₂
  set c0lo := mSum (fun c => c.1) bl s0 with hc0lo
  set c0hi := mSum (fun c => c.2) bl s0 with hc0hi
  set h1s := mSum (fun c => c.2) bl s1 with hh1s
  set D₁ := h1s + cond e t 0 with hD₁def
  set D₂ := hiSum bl - h1s + cond e 0 t with hD₂def
  have hρ12 : ρ₁ ≤ ρ₂ := by
    rw [hρ₁, hρ₂]
    exact mSum_le _ _ bl (fun c hcm => (hc c hcm).2.1) sr
  -- the reals
  have hD := DEN_pos'
  have hL0 : 0 < L := L_pos
  obtain ⟨hden, hLnum⟩ := lnum_eq
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = L / DEN := ⟨_, rfl⟩
  rw [← hκdef] at hLnum
  have hκ : 0 < κ := by rw [hκdef]; positivity
  have hκD : κ * DEN = L := by rw [hκdef]; field_simp
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = (Lden : ℝ) * DEN := ⟨_, rfl⟩
  have hM : 0 < M := by rw [hMdef]; positivity
  have hLnum' : (Lnum : ℝ) = M * κ := by rw [hMdef]; exact hLnum
  have cast : ∀ {a b : ℕ}, a ≤ b → (a : ℝ) ≤ b := fun hab => by exact_mod_cast hab
  have castlt : ∀ {a b : ℕ}, a < b → (a : ℝ) < b := fun hab => by exact_mod_cast hab
  have conv : ∀ {A B : ℝ}, M * A ≤ M * B → A ≤ B := fun hAB => le_of_mul_le_mul_left hAB hM
  have conv' : ∀ {A B : ℝ}, M * A < M * B → A < B := fun hAB => lt_of_mul_lt_mul_left hAB hM.le
  -- the region's six inequalities, in exponents of `q`
  have Z1 : 1 + 2000 * κ ≤ 2000 * (κ * ρ₁) := conv (by
    have := cast z1
    push_cast at this
    rw [hLnum', ← hMdef] at this
    linarith)
  have Z2 : 2 ≤ 3 * (κ * u) := conv (by
    have := cast z2
    push_cast at this
    rw [hLnum'] at this
    have e1 : (2 : ℝ) * Lden * DEN = 2 * M := by rw [hMdef]; ring
    rw [e1] at this
    linarith)
  have Z3 : 2 + 3 * (κ * (ρ₂ + 1 + v)) ≤ 3 * L := conv (by
    have := cast z3
    push_cast at this
    rw [hLnum'] at this
    have e1 : (2 : ℝ) * Lden * DEN = 2 * M := by rw [hMdef]; ring
    rw [e1] at this
    have e2 : M * (3 * L) = 3 * (M * κ) * DEN := by rw [← hκD]; ring
    rw [e2]
    linarith)
  have Z4 : 62505 + 27637 * κ ≤ 62500 * (κ * u) + 27637 * (κ * ρ₁) := conv (by
    have := cast z4
    push_cast at this
    rw [hLnum'] at this
    have e1 : (62505 : ℝ) * Lden * DEN = 62505 * M := by rw [hMdef]; ring
    rw [e1] at this
    linarith)
  have Z5 : 62505 + 62500 * (κ * v) + 34863 * (κ * (ρ₂ + 1)) ≤ 62500 * L := conv (by
    have := cast z5
    push_cast at this
    rw [hLnum'] at this
    have e1 : (62505 : ℝ) * Lden * DEN = 62505 * M := by rw [hMdef]; ring
    rw [e1] at this
    have e2 : M * (62500 * L) = 62500 * (M * κ) * DEN := by rw [← hκD]; ring
    rw [e2]
    linarith)
  have Z6 : 125005 + 34863 * (κ * (ρ₂ + 1)) ≤ 62500 * L := conv (by
    have := cast z6
    push_cast at this
    rw [hLnum'] at this
    have e1 : (125005 : ℝ) * Lden * DEN = 125005 * M := by rw [hMdef]; ring
    rw [e1] at this
    have e2 : M * (62500 * L) = 62500 * (M * κ) * DEN := by rw [← hκD]; ring
    rw [e2]
    linarith)
  have P4 : κ * D₁ + 1 < L := conv' (by
    have := castlt p4
    push_cast at this
    rw [hLnum', ← hMdef] at this
    have e2 : M * L = M * κ * DEN := by rw [← hκD]; ring
    rw [e2]
    linarith)
  have P5 : 2 * (κ * (D₁ + D₂)) + 1 < 2 * L := conv' (by
    have := castlt p5
    push_cast at this
    rw [hLnum', ← hMdef] at this
    have e2 : M * (2 * L) = 2 * (M * κ) * DEN := by rw [← hκD]; ring
    rw [e2]
    linarith)
  have P6 : κ * (D₁ + 2 * D₂) + 2 < 2 * L := conv' (by
    have := castlt p6
    push_cast at this
    rw [hLnum'] at this
    have e1 : (2 : ℝ) * Lden * DEN = 2 * M := by rw [hMdef]; ring
    rw [e1] at this
    have e2 : M * (2 * L) = 2 * (M * κ) * DEN := by rw [← hκD]; ring
    rw [e2]
    linarith)
  -- the sets, and the sums over them
  have hdisj : Disjoint (mset k s0) (mset k sr) := mset_disjoint k hland'
  have hsumlo : ∀ m : ℕ, ∑ i ∈ mset k m, κ * ((bx i).1 : ℝ) = κ * ((mSum (fun c => c.1) bl m : ℕ) : ℝ) :=
    fun m => by rw [← Finset.mul_sum, ← Nat.cast_sum, hbx, sum_mset (fun c => c.1) bl k h m]
  have hsumhi : ∀ m : ℕ, ∑ i ∈ mset k m, κ * ((bx i).2 : ℝ) = κ * ((mSum (fun c => c.2) bl m : ℕ) : ℝ) :=
    fun m => by rw [← Finset.mul_sum, ← Nat.cast_sum, hbx, sum_mset (fun c => c.2) bl k h m]
  have hsumc : ∑ i ∈ (mset k s1)ᶜ, κ * ((bx i).2 : ℝ) = κ * ((hiSum bl - h1s : ℕ) : ℝ) := by
    rw [← Finset.mul_sum, ← Nat.cast_sum, hbx, sum_mset_compl bl k h s1]
  have hSr : (mset k sr).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have h0 := hsumlo sr
    rw [hne, Finset.sum_empty, ← hρ₁] at h0
    linarith
  -- the conditions of the comparison
  have hu : 0 < κ * (u : ℝ) := by linarith
  have huv : κ * (u : ℝ) + κ * (f : ℝ) < κ * (v : ℝ) := by
    have := mul_lt_mul_of_pos_left (castlt p1) hκ
    push_cast at this
    linarith
  have hρ₁0 : 0 ≤ κ * (ρ₁ : ℝ) := by positivity
  have hρ : κ * (ρ₁ : ℝ) ≤ κ * (ρ₂ : ℝ) := mul_le_mul_of_nonneg_left (cast hρ12) hκ.le
  have hvρ : κ * (v : ℝ) + κ * (ρ₂ : ℝ) < L := by linarith
  have hρlo : κ * (ρ₁ : ℝ) ≤ ∑ i ∈ mset k sr, κ * ((bx i).1 : ℝ) := (hsumlo sr).ge
  have hρhi : ∑ i ∈ mset k sr, κ * ((bx i).2 : ℝ) ≤ κ * (ρ₂ : ℝ) := (hsumhi sr).le
  have hzone : ∀ m₁ m₂ : ℝ, κ * (u : ℝ) ≤ m₁ → m₁ ≤ κ * (v : ℝ) → L - κ * (ρ₂ : ℝ) - κ ≤ m₁ + m₂ →
      m₁ + m₂ ≤ L - κ * (ρ₁ : ℝ) + κ → SieveTwoZone7D.Zone7d L m₁ m₂ := by
    intro m₁ m₂ h1 h2 h3 h4
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have hlo : κ * (u : ℝ) - ∑ i ∈ mset k s0, κ * ((bx i).1 : ℝ) ≤ κ * (t : ℝ) := by
    rw [hsumlo s0, ← hc0lo]
    have := mul_le_mul_of_nonneg_left (cast p2) hκ.le
    push_cast at this
    linarith
  have hhi : ∑ i ∈ mset k s0, κ * ((bx i).2 : ℝ) < κ * (v : ℝ) := by
    rw [hsumhi s0, ← hc0hi]
    exact mul_lt_mul_of_pos_left (castlt p3) hκ
  have hk1 : κ * (h1s : ℝ) + (if e then κ * (t : ℝ) else 0) = κ * (D₁ : ℝ) := by
    rw [hD₁def]
    cases e <;> simp [mul_add]
  have hk2 : κ * ((hiSum bl - h1s : ℕ) : ℝ) + (if e then 0 else κ * (t : ℝ)) = κ * (D₂ : ℝ) := by
    rw [hD₂def]
    cases e <;> simp [mul_add]
  have hD₁ : ∑ i ∈ mset k s1, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) else 0) < L - 1 := by
    rw [hsumhi s1, ← hh1s, hk1]
    linarith
  have hD₂ : max (∑ i ∈ mset k s1, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) else 0)) 1 +
      (∑ i ∈ mset k s1, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) else 0)) +
        2 * (∑ i ∈ (mset k s1)ᶜ, κ * ((bx i).2 : ℝ) + (if e then 0 else κ * (t : ℝ))) < 2 * L - 1 := by
    rw [hsumhi s1, ← hh1s, hk1, hsumc, hk2]
    rcases le_total (κ * (D₁ : ℝ)) 1 with hle | hle
    · rw [max_eq_right hle]
      linarith
    · rw [max_eq_left hle]
      linarith
  intro η hη
  obtain ⟨δ, hδ, q₀, hq₀⟩ := SieveTwoComp.prop6_two_at two_lt_L L_le (SieveFamilyTwo.typeIITwoAt_7d L) k 40
    (Λ₁ := L + 1) (a₀ := κ * (f : ℝ)) (by linarith) (mul_pos hκ (by exact_mod_cast hf0))
    (fun i => κ * ((bx i).1 : ℝ)) (fun i => κ * ((bx i).2 : ℝ)) (mset k s0) (mset k sr) (mset k s1) hdisj hSr e
    hu huv hρ₁0 hρ hvρ hρlo hρhi hκ hzone hlo hhi hD₁ hD₂ (η := η / (2 * L)) (by positivity)
  filter_upwards [eventually_ge_atTop q₀, eventually_ge_atTop 2, le_Xq hδ (half_pos hη)] with q hq hq2 hX a ha
  have : NeZero q := ⟨by omega⟩
  have hq1 : 1 ≤ q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hx1 : 1 ≤ xq q := Real.one_le_rpow hq1' hL0.le
  have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (show 0 < q by omega)
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hthr : ThrOK q (specB q bx) :=
    thrOK_specB hq1 hL0.le bx fun i => ⟨(hbxc i).2.1.trans (hbxc i).2.2, (hbxc i).2.2⟩
  have hmain := hq₀ q hq a ha ((specB q bx).map Atom.toG)
    (by rw [List.length_map]; have := specB_length q bx; omega) (c_le_of_thrOK hq1 hthr)
    (fun rt hp hΩ => by
      obtain ⟨hsa, hcc⟩ := (sem_specB q bx rt).1 ((holds_iff_sem hthr hp).1 hΩ)
      refine ⟨hsa, fun i => ?_, fun i => ⟨?_, ?_⟩⟩
      · rw [hκdef, qpow_eq]
        exact Nat.ceil_le.2 ((pow_mono hx1 (hbxc i).1).trans (hcc i).1)
      · show (q : ℝ) ^ (κ * ((bx i).1 : ℝ)) ≤ rt i
        rw [hκdef, qpow_eq]
        exact (hcc i).1
      · show (rt i : ℝ) ≤ (q : ℝ) ^ (κ * ((bx i).2 : ℝ))
        rw [hκdef, qpow_eq]
        exact (hcc i).2.le)
  rw [RTg_eq_of_thrOK hthr, sum_dw_famJ, Complex.norm_real, Real.norm_eq_abs] at hmain
  unfold dJ
  rw [famB_eq_famSet, ← qpow_eq q f, ← hκdef]
  refine hmain.trans ?_
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hlogx : Real.log ((q : ℝ) ^ L) = L * Real.log q := Real.log_rpow hq0 _
  have e1 : η / (2 * L) * (q : ℝ) ^ L / (q.totient * Real.log q) = (q.totient : ℝ)⁻¹ * (η / 2 * Xq q) := by
    unfold Xq
    rw [hlogx]
    field_simp
  have e2 : (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) ≤ (q.totient : ℝ)⁻¹ * (η / 2 * Xq q) :=
    mul_le_mul_of_nonneg_left hX hφ
  rw [e1]
  have e3 : (q.totient : ℝ)⁻¹ * (η * Xq q) =
      (q.totient : ℝ)⁻¹ * (η / 2 * Xq q) + (q.totient : ℝ)⁻¹ * (η / 2 * Xq q) := by ring
  linarith

omit [Route] [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- The product of the primes of a set, for primes with `q^{κ·lo_i} ≤ p_i ≤ q^{κ·hi_i}`. -/
theorem prod_set_bounds {q : ℕ} (hq0 : (0 : ℝ) < q) (κ : ℝ) {k : ℕ} (bx : Fin k → Cell) {rt : Fin k → ℕ}
    (hcc : ∀ i, (q : ℝ) ^ (κ * ((bx i).1 : ℝ)) ≤ rt i ∧ (rt i : ℝ) ≤ (q : ℝ) ^ (κ * ((bx i).2 : ℝ)))
    (S : Finset (Fin k)) :
    (q : ℝ) ^ (κ * ((∑ i ∈ S, (bx i).1 : ℕ) : ℝ)) ≤ ((∏ i ∈ S, rt i : ℕ) : ℝ) ∧
      ((∏ i ∈ S, rt i : ℕ) : ℝ) ≤ (q : ℝ) ^ (κ * ((∑ i ∈ S, (bx i).2 : ℕ) : ℝ)) := by
  constructor
  · rw [Nat.cast_sum, Finset.mul_sum, Real.rpow_sum_of_pos hq0, Nat.cast_prod]
    exact Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg hq0.le _) fun i _ => (hcc i).1
  · rw [Nat.cast_sum, Finset.mul_sum, Real.rpow_sum_of_pos hq0, Nat.cast_prod]
    exact Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ => (hcc i).2

/-- **A box evaluated by the estimate in two variables.** If `chkI2` passes the box, for the first variable `s0`
and the rest `sr`, the term of the box is evaluated. -/
theorem evI_two (bl : List Cell) (k' : ℕ) (h : bl.length = k' + 1) (s0 sr : ℕ) (hok : chkI2 bl s0 sr = true) :
    EvI (boxFn bl (k' + 1) h) := by
  simp only [chkI2, Bool.and_eq_true, Nat.ble_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hlen, hcells⟩, hland⟩, z1⟩, z2⟩, z3⟩, z4⟩, z5⟩, z6⟩ := hok
  have hland' : s0 &&& sr = 0 := Nat.eq_of_beq_eq_true hland
  have hc := (cellsFrom_iff 1 bl).1 hcells
  set bx := boxFn bl (k' + 1) h with hbx
  have hbxc : ∀ i, 1 ≤ (bx i).1 ∧ (bx i).1 ≤ (bx i).2 ∧ (bx i).2 ≤ DEN := fun i => hc _ (boxFn_mem bl _ h i)
  set ρ₁ := mSum (fun c => c.1) bl sr with hρ₁
  set ρ₂ := mSum (fun c => c.2) bl sr with hρ₂
  set u := mSum (fun c => c.1) bl s0 with hu0
  set v := mSum (fun c => c.2) bl s0 with hv0
  have hρ12 : ρ₁ ≤ ρ₂ := mSum_le _ _ bl (fun c hcm => (hc c hcm).2.1) sr
  have huv0 : u ≤ v := mSum_le _ _ bl (fun c hcm => (hc c hcm).2.1) s0
  have hD := DEN_pos'
  have hL0 : 0 < L := L_pos
  obtain ⟨hden, hLnum⟩ := lnum_eq
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = L / DEN := ⟨_, rfl⟩
  rw [← hκdef] at hLnum
  have hκ : 0 < κ := by rw [hκdef]; positivity
  have hκD : κ * DEN = L := by rw [hκdef]; field_simp
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = (Lden : ℝ) * DEN := ⟨_, rfl⟩
  have hM : 0 < M := by rw [hMdef]; positivity
  have hLnum' : (Lnum : ℝ) = M * κ := by rw [hMdef]; exact hLnum
  have cast : ∀ {a b : ℕ}, a ≤ b → (a : ℝ) ≤ b := fun hab => by exact_mod_cast hab
  have conv : ∀ {A B : ℝ}, M * A ≤ M * B → A ≤ B := fun hAB => le_of_mul_le_mul_left hAB hM
  have Z1 : 1 + 2000 * κ ≤ 2000 * (κ * ρ₁) := conv (by
    have := cast z1
    push_cast at this
    rw [hLnum', ← hMdef] at this
    linarith)
  have Z2 : 2 + 3 * κ ≤ 3 * (κ * u) := conv (by
    have := cast z2
    push_cast at this
    rw [hLnum'] at this
    have e1 : (2 : ℝ) * Lden * DEN = 2 * M := by rw [hMdef]; ring
    rw [e1] at this
    linarith)
  have Z3 : 2 + 3 * (κ * (ρ₂ + 1 + v)) ≤ 3 * L := conv (by
    have := cast z3
    push_cast at this
    rw [hLnum'] at this
    have e1 : (2 : ℝ) * Lden * DEN = 2 * M := by rw [hMdef]; ring
    rw [e1] at this
    have e2 : M * (3 * L) = 3 * (M * κ) * DEN := by rw [← hκD]; ring
    rw [e2]
    linarith)
  have Z4 : 62505 + 90137 * κ ≤ 62500 * (κ * u) + 27637 * (κ * ρ₁) := conv (by
    have := cast z4
    push_cast at this
    rw [hLnum'] at this
    have e1 : (62505 : ℝ) * Lden * DEN = 62505 * M := by rw [hMdef]; ring
    rw [e1] at this
    linarith)
  have Z5 : 62505 + 62500 * (κ * v) + 34863 * (κ * (ρ₂ + 1)) ≤ 62500 * L := conv (by
    have := cast z5
    push_cast at this
    rw [hLnum'] at this
    have e1 : (62505 : ℝ) * Lden * DEN = 62505 * M := by rw [hMdef]; ring
    rw [e1] at this
    have e2 : M * (62500 * L) = 62500 * (M * κ) * DEN := by rw [← hκD]; ring
    rw [e2]
    linarith)
  have Z6 : 125005 + 34863 * (κ * (ρ₂ + 1)) ≤ 62500 * L := conv (by
    have := cast z6
    push_cast at this
    rw [hLnum'] at this
    have e1 : (125005 : ℝ) * Lden * DEN = 125005 * M := by rw [hMdef]; ring
    rw [e1] at this
    have e2 : M * (62500 * L) = 62500 * (M * κ) * DEN := by rw [← hκD]; ring
    rw [e2]
    linarith)
  have hdisj : Disjoint (mset (k' + 1) s0) (mset (k' + 1) sr) := mset_disjoint _ hland'
  have hslo : ∀ m : ℕ, ∑ i ∈ mset (k' + 1) m, (bx i).1 = mSum (fun c => c.1) bl m :=
    fun m => by rw [hbx, sum_mset (fun c => c.1) bl _ h m]
  have hshi : ∀ m : ℕ, ∑ i ∈ mset (k' + 1) m, (bx i).2 = mSum (fun c => c.2) bl m :=
    fun m => by rw [hbx, sum_mset (fun c => c.2) bl _ h m]
  have hSr : (mset (k' + 1) sr).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have h0 := hslo sr
    rw [hne, Finset.sum_empty, ← hρ₁] at h0
    have : (ρ₁ : ℝ) = 0 := by exact_mod_cast h0.symm
    rw [this] at Z1
    linarith
  have hzone : ∀ m₁ m₂ : ℝ, κ * (u : ℝ) - κ ≤ m₁ → m₁ ≤ κ * (v : ℝ) → L - κ * (ρ₂ : ℝ) - κ ≤ m₁ + m₂ →
      m₁ + m₂ ≤ L - κ * (ρ₁ : ℝ) + κ → SieveTwoZone7D.Zone7d L m₁ m₂ := by
    intro m₁ m₂ h1 h2 h3 h4
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  intro η hη
  obtain ⟨δ, hδ, q₀, hq₀⟩ := chain2_exp (SieveFamilyTwo.typeIITwoAt_7d L) (e₀ := κ * ((1 : ℕ) : ℝ))
    (by positivity) k' 40 (Λ₁ := L + 1) (by linarith) (u := κ * (u : ℝ)) (v := κ * (v : ℝ)) (ρ₁ := κ * (ρ₁ : ℝ))
    (ρ₂ := κ * (ρ₂ : ℝ)) (ε := κ) (by linarith) (mul_le_mul_of_nonneg_left (cast huv0) hκ.le) (by positivity)
    (mul_le_mul_of_nonneg_left (cast hρ12) hκ.le) (by linarith) hκ hzone
  filter_upwards [eventually_ge_atTop q₀, eventually_ge_atTop 2, le_Xq hδ hη] with q hq hq2 hX a ha
  have : NeZero q := ⟨by omega⟩
  have hq1 : 1 ≤ q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hx1 : 1 ≤ xq q := Real.one_le_rpow hq1' hL0.le
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hthr : ThrOK q (specB q bx) :=
    thrOK_specB hq1 hL0.le bx fun i => ⟨(hbxc i).2.1.trans (hbxc i).2.2, (hbxc i).2.2⟩
  have hmain := hq₀ q hq a ha (mset (k' + 1) s0) (mset (k' + 1) sr) ((specB q bx).map Atom.toG) hdisj hSr
    (by rw [List.length_map]; have := specB_length q bx; omega) (c_le_of_thrOK hq1 hthr)
    (fun rt hp hΩ => by
      obtain ⟨hsa, hcc⟩ := (sem_specB q bx rt).1 ((holds_iff_sem hthr hp).1 hΩ)
      have hcc' : ∀ i, (q : ℝ) ^ (κ * ((bx i).1 : ℝ)) ≤ rt i ∧ (rt i : ℝ) ≤ (q : ℝ) ^ (κ * ((bx i).2 : ℝ)) :=
        fun i => by
          rw [hκdef, qpow_eq, qpow_eq]
          exact ⟨(hcc i).1, (hcc i).2.le⟩
      have b0 := prod_set_bounds hq0 κ bx hcc' (mset (k' + 1) s0)
      have br := prod_set_bounds hq0 κ bx hcc' (mset (k' + 1) sr)
      rw [hslo s0, hshi s0] at b0
      rw [hslo sr, hshi sr] at br
      refine ⟨hsa, fun i => ?_, b0.1, b0.2, br.1, br.2⟩
      rw [hκdef, qpow_eq]
      exact (pow_mono hx1 (hbxc i).1).trans (hcc i).1)
  rw [RTg_eq_of_thrOK hthr, sum_dw_famI, Complex.norm_real, Real.norm_eq_abs] at hmain
  unfold dI
  rw [famB_eq_famSet]
  exact hmain.trans (mul_le_mul_of_nonneg_left hX hφ)

/-- **The test of a box by the estimate in two variables is sound.** -/
theorem evI_okI2 (bl : List Cell) (cfg : Cfg) (k' : ℕ) (h : bl.length = k' + 1) (hok : okI2 bl cfg = true) :
    EvI (boxFn bl (k' + 1) h) :=
  evI_two bl k' h cfg.s0 cfg.sr hok

/-- **The test of the comparison in two variables is sound**: a box that passes `okJ2` at a floor has its terms
at that floor evaluated. -/
theorem evJ_okJ2 (bl : List Cell) (f : ℕ) (cfg : Cfg) (k : ℕ) (h : bl.length = k) (hok : okJ2 bl f cfg = true) :
    EvJ f (boxFn bl k h) :=
  evJ_two bl k h f cfg.s0 cfg.sr cfg.s1 cfg.e _ _ _ hok

/-- **The tests of the estimate in two variables are sound.** -/
theorem twoTests_sound : (twoTests).Sound :=
  ⟨fun bl cfg k' h hok => evI_okI2 bl cfg k' h hok, fun bl f cfg k h hok => evJ_okJ2 bl f cfg k h hok⟩

end SieveAd

#print axioms SieveAd.twoTests_sound
