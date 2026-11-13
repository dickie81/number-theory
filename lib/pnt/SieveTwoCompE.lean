/-
# Harman's comparison in two variables with the leaves of a box cut in three

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveTwoComp.prop6_two` is Harman's comparison with stops in two variables, its leaves by the paper's Lemma 4.3 on
the wider region: the leaves' blocks of exponents at most `D₁` and `D₂` (in exponents of `q`) must satisfy
`D₁ < L − 1` and `max(D₁, 1) + D₁ + 2D₂ < 2L − 1`. This file is the same for a box whose leaves do not: they are cut at
`d₁ ≤ q^{pA}` and then `d₂ ≤ q^{th}`, the first part by the paper's lemma with `pA` in place of `D₁`, the second with
`th` in place of `D₂`, and the third by the estimate in two variables with the cofactor as the second variable, on the
region `SieveLeafTwo.LeafZoneX` (`SieveLeafTwo.leavesE_of_zone`, `SieveLeafTwo.typeIITwoAt_leafX`).

Plain statement (`prop6_two3`). As `SieveTwoComp.prop6_two`, with the leaves' conditions replaced by: `S₁` and its
complement nonempty, `D₁, D₂ ≥ 0`, `D₁ + D₂ < L`, and exponents `pA, th ≥ 0` and `ε_E > 0` with

* `pA < L − 1` and `max(pA, 1) + pA + 2D₂ < 2L − 1` (the first part);
* `D₁ < L − 1` and `max(D₁, 1) + D₁ + 2th < 2L − 1` (the second);
* `LeafZoneX L m₁ m₂` for `pA − ε_E ≤ m₁ ≤ D₁ + ε_E` and `L − D₂ − ε_E ≤ m₁ + m₂ ≤ L − th + ε_E` (the third: `d₁` the first
  variable, the cofactor the second, `d₂` the rest).

The conclusion is the same: for every `η > 0` there are `δ > 0` and `q₀` with
`|Σ_{rt}(S(A_r, z₀) − S(B_r, z₀)/φ(q))| ≤ ηq^L/(φ(q) log q) + q^{L−δ}/φ(q)` for `q ≥ q₀`.

The proof is `prop6_two`'s with `SieveTwoP6E.prop6_two_core3` at each `q`: `leavesOK_wide` at each of the two parts'
exponents, `leavesE_of_zone` for the third on the boxes `(⌊q^{pA}⌋, ⌊4q^{D₁}⌋]` of `d₁` and `(⌊q^{th}⌋, ⌊4q^{D₂}⌋]`
of `d₂`, whose window lies in the region for large `q`, and the three at a common `δ`.

The file imports `SieveTwoComp.lean` and `SieveTwoP6E.lean`.
-/
import SieveTwoComp
import SieveTwoP6E

open Real Finset SieveFamily SieveTree SieveChain SieveRoute SieveP6Chain SieveP6ib SieveFamilyTwo SieveTwoP6
  SieveTwoTerm SieveP6LeavesWide

namespace SieveTwoCompE

open Classical

variable [Route]

omit [Route] in
/-- `LeavesOK` at `δ` gives it at any `δ₂ ≤ δ`. -/
theorem leavesOK_mono {q : ℕ} (hq : 1 ≤ q) {a' : ZMod q} {L a b δ' εw Λ₀ C₀ δ δ₂ : ℝ} {k J₀ Kmax : ℕ}
    (h : SieveP6TreeLeaves.LeavesOK q a' L a b δ' εw Λ₀ C₀ δ k J₀ Kmax) (hδ : δ₂ ≤ δ) :
    SieveP6TreeLeaves.LeavesOK q a' L a b δ' εw Λ₀ C₀ δ₂ k J₀ Kmax := by
  intro K₁ K₂ hK₁ hK₂ Y₁ Y₂ hY₁ hY₂ M hM cc e₁ e₂ Pr hPr hΛ hpiv hgeo
  refine (h K₁ K₂ hK₁ hK₂ Y₁ Y₂ hY₁ hY₂ hM cc e₁ e₂ Pr hPr hΛ hpiv hgeo).trans ?_
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith))
    (by positivity))

omit [Route] in
/-- **The window of the leaves' third part.** For `q > 1`, `pA, th, D₁, D₂ ≥ 0`, `64 ≤ q^{L−D₁−D₂}` and `64 ≤ q^{ε_E}`:
the boxes `(⌊q^{pA}⌋, ⌊4q^{D₁}⌋]` and `(⌊q^{th}⌋, ⌊4q^{D₂}⌋]` have their ends at least `1` and `⌊4q^{D₁}⌋⌊4q^{D₂}⌋ ≤ ⌊q^L⌋`,
and a region that holds for `pA − ε_E ≤ m₁ ≤ D₁ + ε_E` and `L − D₂ − ε_E ≤ m₁ + m₂ ≤ L − th + ε_E` holds on their
window (`SieveLeafTwo.leavesE_of_zone`'s). -/
theorem leaf_window {q : ℕ} {L pA th D₁ D₂ εE : ℝ} (hq1' : (1 : ℝ) < q) (hpA : 0 ≤ pA) (hth : 0 ≤ th)
    (hD₁0 : 0 ≤ D₁) (hD₂0 : 0 ≤ D₂) (hL0 : 0 < L) (h64D : 64 ≤ (q : ℝ) ^ (L - D₁ - D₂))
    (h64ε : 64 ≤ (q : ℝ) ^ εE) {Rg : ℝ → ℝ → Prop}
    (hzoneE : ∀ m₁ m₂ : ℝ, pA - εE ≤ m₁ → m₁ ≤ D₁ + εE → L - D₂ - εE ≤ m₁ + m₂ → m₁ + m₂ ≤ L - th + εE →
      Rg m₁ m₂) :
    1 ≤ ⌊(q : ℝ) ^ pA⌋₊ ∧ 1 ≤ ⌊4 * (q : ℝ) ^ D₁⌋₊ ∧ 1 ≤ ⌊4 * (q : ℝ) ^ D₂⌋₊ ∧
    ⌊4 * (q : ℝ) ^ D₁⌋₊ * ⌊4 * (q : ℝ) ^ D₂⌋₊ ≤ ⌊(q : ℝ) ^ L⌋₊ ∧
    ∀ u' v' : ℝ, Real.logb q (⌊(q : ℝ) ^ pA⌋₊ : ℝ) ≤ u' → u' ≤ Real.logb q (⌊4 * (q : ℝ) ^ D₁⌋₊ : ℝ) →
      ((⌊(q : ℝ) ^ L⌋₊ / ⌊4 * (q : ℝ) ^ D₂⌋₊ : ℕ) : ℝ) ≤ 4 * (q : ℝ) ^ (u' + v') →
      (q : ℝ) ^ (u' + v') ≤ ((⌊2 * (q : ℝ) ^ L⌋₊ / (⌊(q : ℝ) ^ th⌋₊ + 1) : ℕ) : ℝ) → Rg u' v' := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) ≤ q := hq1'.le
  have hqpA1 : (1 : ℝ) ≤ (q : ℝ) ^ pA := Real.one_le_rpow hq1 hpA
  have hqth1 : (1 : ℝ) ≤ (q : ℝ) ^ th := Real.one_le_rpow hq1 hth
  have hqD₁1 : (1 : ℝ) ≤ (q : ℝ) ^ D₁ := Real.one_le_rpow hq1 hD₁0
  have hqD₂1 : (1 : ℝ) ≤ (q : ℝ) ^ D₂ := Real.one_le_rpow hq1 hD₂0
  have hAE1 : 1 ≤ ⌊(q : ℝ) ^ pA⌋₊ := Nat.le_floor (by exact_mod_cast hqpA1)
  have hBE1 : 1 ≤ ⌊4 * (q : ℝ) ^ D₁⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hBrE1 : 1 ≤ ⌊4 * (q : ℝ) ^ D₂⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hBEle : (⌊4 * (q : ℝ) ^ D₁⌋₊ : ℝ) ≤ 4 * (q : ℝ) ^ D₁ := Nat.floor_le (by positivity)
  have hBrEle : (⌊4 * (q : ℝ) ^ D₂⌋₊ : ℝ) ≤ 4 * (q : ℝ) ^ D₂ := Nat.floor_le (by positivity)
  have hAEgt : (q : ℝ) ^ pA < (⌊(q : ℝ) ^ pA⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hAE1r : (1 : ℝ) ≤ (⌊(q : ℝ) ^ pA⌋₊ : ℝ) := by exact_mod_cast hAE1
  have hD12 : 0 ≤ (q : ℝ) ^ D₁ * (q : ℝ) ^ D₂ := by positivity
  have hqD : 64 * ((q : ℝ) ^ D₁ * (q : ℝ) ^ D₂) ≤ (q : ℝ) ^ L := by
    have e : (q : ℝ) ^ L = (q : ℝ) ^ (L - D₁ - D₂) * ((q : ℝ) ^ D₁ * (q : ℝ) ^ D₂) := by
      rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]; congr 1; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h64D hD12
  refine ⟨hAE1, hBE1, hBrE1, ?_, ?_⟩
  · refine Nat.le_floor ?_
    push_cast
    have h1 := mul_le_mul hBEle hBrEle (Nat.cast_nonneg _) (by positivity)
    have e : 4 * (q : ℝ) ^ D₁ * (4 * (q : ℝ) ^ D₂) = 16 * ((q : ℝ) ^ D₁ * (q : ℝ) ^ D₂) := by ring
    linarith only [h1, e, hqD, hD12]
  intro u' v' h1 h2 h5 h6
  have hAE0 : (0 : ℝ) < (⌊(q : ℝ) ^ pA⌋₊ : ℝ) := by linarith
  have hBE0 : (0 : ℝ) < (⌊4 * (q : ℝ) ^ D₁⌋₊ : ℝ) := by exact_mod_cast hBE1
  have hε2 : 2 ≤ (q : ℝ) ^ εE := by linarith
  refine hzoneE u' v' ?_ ?_ ?_ ?_
  · -- `q^{pA−εE} ≤ ⌊q^{pA}⌋ ≤ q^{u'}`
    have hle := (Real.logb_le_iff_le_rpow hq1' hAE0).1 h1
    refine (Real.rpow_le_rpow_left_iff hq1').1 (le_trans ?_ hle)
    have e : (q : ℝ) ^ pA = (q : ℝ) ^ (pA - εE) * (q : ℝ) ^ εE := by
      rw [← Real.rpow_add hq0]; congr 1; ring
    have h0 : 0 ≤ (q : ℝ) ^ (pA - εE) := by positivity
    have h2' := mul_le_mul_of_nonneg_left hε2 h0
    linarith only [e, h2', hAEgt, hAE1r]
  · -- `q^{u'} ≤ ⌊4q^{D₁}⌋ ≤ q^{D₁+εE}`
    have hle := (Real.le_logb_iff_rpow_le hq1' hBE0).1 h2
    refine (Real.rpow_le_rpow_left_iff hq1').1 (hle.trans (hBEle.trans ?_))
    have e : (q : ℝ) ^ (D₁ + εE) = (q : ℝ) ^ D₁ * (q : ℝ) ^ εE := Real.rpow_add hq0 _ _
    rw [e]
    have h0 : 0 ≤ (q : ℝ) ^ D₁ := by positivity
    have h3 := mul_le_mul_of_nonneg_left h64ε h0
    linarith only [h3, h0]
  · -- `4q^{L−D₂−εE} ≤ ⌊N₁/⌊4q^{D₂}⌋⌋`
    refine (Real.rpow_le_rpow_left_iff hq1').1 ?_
    have hm0 : (0 : ℝ) < (q : ℝ) ^ (L - D₂ - εE) := by positivity
    have hprod : (q : ℝ) ^ (L - D₂ - εE) * (q : ℝ) ^ εE * (q : ℝ) ^ D₂ = (q : ℝ) ^ L := by
      rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]; congr 1; ring
    have hD₂q : 0 ≤ (q : ℝ) ^ D₂ := by positivity
    have h64' : 64 * ((q : ℝ) ^ (L - D₂ - εE) * (q : ℝ) ^ D₂) ≤ (q : ℝ) ^ L := by
      have h := mul_le_mul_of_nonneg_left h64ε (mul_nonneg hm0.le hD₂q)
      calc 64 * ((q : ℝ) ^ (L - D₂ - εE) * (q : ℝ) ^ D₂) =
            (q : ℝ) ^ (L - D₂ - εE) * (q : ℝ) ^ D₂ * 64 := by ring
        _ ≤ (q : ℝ) ^ (L - D₂ - εE) * (q : ℝ) ^ D₂ * (q : ℝ) ^ εE := h
        _ = (q : ℝ) ^ L := by rw [← hprod]; ring
    have hD₂L : 64 * (q : ℝ) ^ D₂ ≤ (q : ℝ) ^ L := by
      have h1' : (q : ℝ) ^ D₂ ≤ (q : ℝ) ^ D₁ * (q : ℝ) ^ D₂ := le_mul_of_one_le_left hD₂q hqD₁1
      linarith only [h1', hqD]
    have hN₁gt : (q : ℝ) ^ L - 1 < (⌊(q : ℝ) ^ L⌋₊ : ℝ) := Nat.sub_one_lt_floor _
    have hXL : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow hq1 hL0.le
    have hmle : ⌈4 * (q : ℝ) ^ (L - D₂ - εE)⌉₊ ≤ ⌊(q : ℝ) ^ L⌋₊ / ⌊4 * (q : ℝ) ^ D₂⌋₊ := by
      refine (Nat.le_div_iff_mul_le hBrE1).2 (Nat.le_floor ?_)
      push_cast
      have hc1 : (⌈4 * (q : ℝ) ^ (L - D₂ - εE)⌉₊ : ℝ) < 4 * (q : ℝ) ^ (L - D₂ - εE) + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      have h3 : (⌈4 * (q : ℝ) ^ (L - D₂ - εE)⌉₊ : ℝ) * (⌊4 * (q : ℝ) ^ D₂⌋₊ : ℝ) ≤
          (4 * (q : ℝ) ^ (L - D₂ - εE) + 1) * (4 * (q : ℝ) ^ D₂) :=
        mul_le_mul hc1.le hBrEle (Nat.cast_nonneg _) (by positivity)
      have e : (4 * (q : ℝ) ^ (L - D₂ - εE) + 1) * (4 * (q : ℝ) ^ D₂) =
          16 * ((q : ℝ) ^ (L - D₂ - εE) * (q : ℝ) ^ D₂) + 4 * (q : ℝ) ^ D₂ := by ring
      linarith only [h3, e, h64', hD₂L, hXL]
    have h9 : 4 * (q : ℝ) ^ (L - D₂ - εE) ≤ ((⌊(q : ℝ) ^ L⌋₊ / ⌊4 * (q : ℝ) ^ D₂⌋₊ : ℕ) : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hmle)
    linarith only [h9, h5]
  · -- `⌊N₂/(⌊q^{th}⌋ + 1)⌋ ≤ q^{L−th+εE}`
    have hN₂r : (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) ≤ 2 * (q : ℝ) ^ L := Nat.floor_le (by positivity)
    have hArEgt : (q : ℝ) ^ th < (⌊(q : ℝ) ^ th⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    refine (Real.rpow_le_rpow_left_iff hq1').1 (h6.trans ?_)
    calc ((⌊2 * (q : ℝ) ^ L⌋₊ / (⌊(q : ℝ) ^ th⌋₊ + 1) : ℕ) : ℝ)
        ≤ (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) / ((⌊(q : ℝ) ^ th⌋₊ + 1 : ℕ) : ℝ) := Nat.cast_div_le
      _ ≤ (2 * (q : ℝ) ^ L) / (q : ℝ) ^ th := by
          refine div_le_div₀ (by positivity) hN₂r (by positivity) ?_
          push_cast
          linarith only [hArEgt]
      _ = 2 * (q : ℝ) ^ (L - th) := by rw [mul_div_assoc, ← Real.rpow_sub hq0]
      _ ≤ (q : ℝ) ^ εE * (q : ℝ) ^ (L - th) := mul_le_mul_of_nonneg_right hε2 (by positivity)
      _ = (q : ℝ) ^ (L - th + εE) := by rw [← Real.rpow_add hq0]; congr 1; ring

set_option maxHeartbeats 6400000 in
/-- **Harman's comparison with stops in two variables, with a box of leaves cut in three.** `SieveTwoComp.prop6_two`
with the leaves cut at `d₁ ≤ q^{pA}` and `d₂ ≤ q^{th}`: the paper's lemma on the first two parts (the conditions at
`(pA, D₂)` and at `(D₁, th)`), the estimate in two variables on `LeafZoneX` on the third. -/
theorem prop6_two3 [RouteOK] {Rg : ℝ → ℝ → Prop} (hII : TypeIITwoAt L Rg) (j J₀ : ℕ) {Λ₁ a₀ : ℝ} (hΛ₁ : 0 ≤ Λ₁)
    (ha₀ : 0 < a₀) (lo hi : Fin j → ℝ) (S₀ Sr S₁ : Finset (Fin j)) (hdisj : Disjoint S₀ Sr) (hSr : Sr.Nonempty)
    (eIn₁ : Bool) {t u v ρ₁ ρ₂ ε : ℝ} (hu : 0 < u) (huv : u + a₀ < v) (hρ₁0 : 0 ≤ ρ₁) (hρ : ρ₁ ≤ ρ₂)
    (hvρ : v + ρ₂ < L) (hρlo : ρ₁ ≤ ∑ i ∈ Sr, lo i) (hρhi : ∑ i ∈ Sr, hi i ≤ ρ₂) (hε : 0 < ε)
    (hzone : ∀ m₁ m₂ : ℝ, u ≤ m₁ → m₁ ≤ v → L - ρ₂ - ε ≤ m₁ + m₂ → m₁ + m₂ ≤ L - ρ₁ + ε → Rg m₁ m₂)
    (hlo : u - ∑ i ∈ S₀, lo i ≤ t) (hhi : ∑ i ∈ S₀, hi i < v)
    {pA th εE : ℝ} (hpA : 0 ≤ pA) (hth : 0 ≤ th) (hεE : 0 < εE)
    (hDA₁ : pA < L - 1) (hDA₂ : max pA 1 + pA + 2 * (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t)) < 2 * L - 1)
    (hDB₁ : (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) < L - 1) (hDB₂ : max (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) 1 + (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) + 2 * th < 2 * L - 1)
    (hDL : (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) + (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t)) < L) (hD₁0 : 0 ≤ (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0))) (hD₂0 : 0 ≤ (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t)))
    (hzoneE : ∀ m₁ m₂ : ℝ, pA - εE ≤ m₁ → m₁ ≤ (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) + εE → L - (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t)) - εE ≤ m₁ + m₂ →
      m₁ + m₂ ≤ L - th + εE → SieveLeafTwo.LeafZoneX L m₁ m₂)
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
  rw [← hD₂def] at hDA₂ hDL hzoneE hD₂0
  rw [← hD₁def] at hDB₁ hDB₂ hDL hzoneE hD₁0
  -- the exponents of the two parts by the paper's lemma: `(pA, D₂)` and `(D₁, th)`
  obtain ⟨A₀A, hA₀Adef⟩ : ∃ A₀ : ℝ, A₀ = L - 1 - max pA 1 := ⟨_, rfl⟩
  obtain ⟨A₀B, hA₀Bdef⟩ : ∃ A₀ : ℝ, A₀ = L - 1 - max D₁ 1 := ⟨_, rfl⟩
  have hA₀A0 : 0 < A₀A := by
    rw [hA₀Adef]
    rcases le_total pA 1 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hA₀B0 : 0 < A₀B := by
    rw [hA₀Bdef]
    rcases le_total D₁ 1 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hA₀AL : A₀A ≤ L - 2 := by rw [hA₀Adef]; linarith [le_max_right pA 1]
  have hA₀BL : A₀B ≤ L - 2 := by rw [hA₀Bdef]; linarith [le_max_right D₁ 1]
  have hA₀AD : A₀A ≤ L - 1 - pA := by rw [hA₀Adef]; linarith [le_max_left pA 1]
  have hA₀BD : A₀B ≤ L - 1 - D₁ := by rw [hA₀Bdef]; linarith [le_max_left D₁ 1]
  obtain ⟨σA, hσAdef⟩ : ∃ σ : ℝ, σ = L + A₀A - pA - 2 * D₂ := ⟨_, rfl⟩
  obtain ⟨σB, hσBdef⟩ : ∃ σ : ℝ, σ = L + A₀B - D₁ - 2 * th := ⟨_, rfl⟩
  have hσA0 : 0 < σA := by rw [hσAdef, hA₀Adef]; linarith
  have hσB0 : 0 < σB := by rw [hσBdef, hA₀Bdef]; linarith
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min (1 / 32) (min (min (A₀A / 32) (σA / 32)) (min (A₀B / 32) (σB / 32))) :=
    ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hcdef]
    exact lt_min (by norm_num) (lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith)))
  have hc32 : c ≤ 1 / 32 := by rw [hcdef]; exact min_le_left _ _
  have hc16 : c ≤ 1 / 16 := by linarith
  have hcAA : c ≤ A₀A / 32 := by
    rw [hcdef]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hcσA : c ≤ σA / 32 := by
    rw [hcdef]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hcAB : c ≤ A₀B / 32 := by
    rw [hcdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcσB : c ≤ σB / 32 := by
    rw [hcdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨AWA, hAWAdef⟩ : ∃ AW : ℝ, AW = A₀A - 2 * c := ⟨_, rfl⟩
  obtain ⟨AWB, hAWBdef⟩ : ∃ AW : ℝ, AW = A₀B - 2 * c := ⟨_, rfl⟩
  -- the sums of `1/d`, and `k` and `ε_w`
  have ha₀L : a₀ ≤ L := by linarith
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
    chainOK2_of_zone hII hεw0 (j + smax + 1) (J₀ + 4 + smax * smax + 2 * smax + 4) hΛ₁'0
  obtain ⟨δ₃A, hδ₃A, q₃A, hq₃A⟩ := leavesOK_wide two_lt_L (a := AWA) (c := AWA - 20 * c) (δ' := 4 * c)
    (κ := 16 * c) (by linarith) (by rw [hAWAdef]; linarith) (by linarith) (by linarith) (by rw [hAWAdef]; linarith)
    (by linarith) (by linarith) (by rw [hAWAdef]; linarith) hεw0 hΛ₀0 (j + smax)
    (J₀ + 4 + smax * smax + 2 * smax + 4) hC₀ hC hkev (by omega) hkC (by rw [hεwc]; exact hc16)
  obtain ⟨δ₃B, hδ₃B, q₃B, hq₃B⟩ := leavesOK_wide two_lt_L (a := AWB) (c := AWB - 20 * c) (δ' := 4 * c)
    (κ := 16 * c) (by linarith) (by rw [hAWBdef]; linarith) (by linarith) (by linarith) (by rw [hAWBdef]; linarith)
    (by linarith) (by linarith) (by rw [hAWBdef]; linarith) hεw0 hΛ₀0 (j + smax)
    (J₀ + 4 + smax * smax + 2 * smax + 4) hC₀ hC hkev (by omega) hkC (by rw [hεwc]; exact hc16)
  obtain ⟨δ₄, hδ₄, q₅, hq₅⟩ := SieveLeafTwo.leavesE_of_zone L_pos L_le (SieveLeafTwo.typeIITwoAt_leafX L) hεw0
    (j + smax) (J₀ + 4 + smax * smax + 2 * smax + 4) hΛ₁'0
  obtain ⟨δ₃, hδ₃def⟩ : ∃ δ₃ : ℝ, δ₃ = min (min δ₃A δ₃B) δ₄ := ⟨_, rfl⟩
  have hδ₃ : 0 < δ₃ := by rw [hδ₃def]; exact lt_min (lt_min hδ₃A hδ₃B) hδ₄
  have hδ₃A' : δ₃ ≤ δ₃A := by rw [hδ₃def]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hδ₃B' : δ₃ ≤ δ₃B := by rw [hδ₃def]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hδ₄' : δ₃ ≤ δ₄ := by rw [hδ₃def]; exact min_le_right _ _
  -- the remainder's constant and the final `δ`
  obtain ⟨Mrem, hMrem⟩ : ∃ Mrem : ℝ, Mrem = 24 * 2 ^ (2 * k + 7) * (K₁ * (Real.exp 1 * a₀ / εw)) := ⟨_, rfl⟩
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀ : ℝ, δ₀ = min (min c δ₁) δ₃ / 2 := ⟨_, rfl⟩
  have hδ₀0 : 0 < δ₀ := by rw [hδ₀]; exact half_pos (lt_min (lt_min hc0 hδ₁) hδ₃)
  have hm : 2 * δ₀ ≤ c ∧ 2 * δ₀ ≤ δ₁ ∧ 2 * δ₀ ≤ δ₃ := by
    have h1 := min_le_left (min c δ₁) δ₃
    have h2 := min_le_right (min c δ₁) δ₃
    have h3 := min_le_left c δ₁
    have h4 := min_le_right c δ₁
    rw [hδ₀]
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  -- the conditions that hold for large `q`
  have hev : ∀ᶠ x : ℝ in Filter.atTop, 3 ≤ x ∧ 2 ≤ x ^ εw ∧
      ∑ p ∈ SieveRough.primesIn (x ^ εw) (x ^ a₀), 1 / (p : ℝ) ≤ Real.log a₀ - Real.log εw + 1 ∧
      ∑ p ∈ SieveRough.primesIn (x ^ a₀) (x ^ (L + 1 : ℝ)), 1 / (p : ℝ) ≤ Real.log (L + 1) - Real.log a₀ + 1 ∧
      Mrem ≤ x ^ c ∧ 4 * ((2 * smax : ℕ) : ℝ) + 5 ≤ x ^ δ₀ ∧ 6 ≤ x ^ (v - u - a₀) ∧
      2 ≤ x ^ (v - ∑ i ∈ S₀, hi i) ∧ 8 ≤ x ^ ε ∧ 2 ≤ x ^ (L - ρ₂) ∧
      4 * 2 ^ (2 * k + 4) ≤ x ^ (L - 1 - AWA - pA - c) ∧
      64 * 2 ^ (2 * k + 4) ≤ x ^ (L - -(AWA - 20 * c) - pA - 2 * D₂ - c) ∧
      4 * 2 ^ (2 * k + 4) ≤ x ^ (L - 1 - AWB - D₁ - c) ∧
      64 * 2 ^ (2 * k + 4) ≤ x ^ (L - -(AWB - 20 * c) - D₁ - 2 * th - c) ∧
      64 ≤ x ^ (L - D₁ - D₂) ∧ 64 ≤ x ^ εE :=
    (Filter.eventually_ge_atTop 3).and (((tendsto_rpow_atTop hεw0).eventually_ge_atTop _).and
      ((SieveRough.evLe_sum_inv hεw0 hεwa.le 1 one_pos).and ((SieveRough.evLe_sum_inv ha₀ ha₀L1 1 one_pos).and
      (((tendsto_rpow_atTop hc0).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop hδ₀0).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop (by linarith)).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop (by linarith)).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop hε).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop (by linarith)).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop (by rw [hAWAdef]; linarith)).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop (by rw [hσAdef] at hcσA; rw [hAWAdef]; linarith)).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop (by rw [hAWBdef]; linarith)).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop (by rw [hσBdef] at hcσB; rw [hAWBdef]; linarith)).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop (by linarith)).eventually_ge_atTop _).and
      ((tendsto_rpow_atTop hεE).eventually_ge_atTop _)))))))))))))))
  obtain ⟨q₄, hq₄⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨δ₀, hδ₀0, max q₁ (max (max q₃A q₃B) (max q₄ q₅)), ?_⟩
  intro q _ hq a ha Ω hΩlen hΩc hΩ
  obtain ⟨hx3, hxw, hM1, hM2, hMrem', hδ2, h6, h2hi, h8ε, h2ρ, hszA₁, hszA₂, hszB₁, hszB₂, h64D, h64ε⟩ :=
    hq₄ q (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hq)))
  have h2ε : 2 ≤ (q : ℝ) ^ ε := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hq1' : (1 : ℝ) < q := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  have hΩc' : ∀ C ∈ Ω, C.c 0 ≤ Λ₁' * Real.log q := fun C hC =>
    (hΩc C hC).trans (mul_le_mul_of_nonneg_right (by rw [hΛ₁']; linarith) hlogq.le)
  -- sizes against `x^{Λ₁'}` and `w^{s_max}`
  have hxL1 : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow hq1 L_pos.le
  have h4L : 4 * (q : ℝ) ^ L ≤ (q : ℝ) ^ (L + 2) := by
    have h9 : (4 : ℝ) ≤ (q : ℝ) ^ (2 : ℝ) := by
      have h33 := mul_le_mul hx3 hx3 (by norm_num : (0 : ℝ) ≤ 3) hq0.le
      rw [Real.rpow_two, pow_two]
      linarith
    calc 4 * (q : ℝ) ^ L ≤ (q : ℝ) ^ (2 : ℝ) * (q : ℝ) ^ L := mul_le_mul_of_nonneg_right h9 (by positivity)
      _ = (q : ℝ) ^ (L + 2) := by rw [Real.rpow_add hq0]; ring
  have hlogA : ∀ A : ℝ, 0 < A → A ≤ 4 * (q : ℝ) ^ L → Real.log A ≤ Λ₁' * Real.log q := fun A hA h => by
    rw [← Real.log_rpow hq0]
    exact Real.log_le_log hA (h.trans (h4L.trans (Real.rpow_le_rpow_of_exponent_le hq1 (by rw [hΛ₁']; linarith))))
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
  have hza : (q : ℝ) ^ εw ≤ (q : ℝ) ^ a₀ := Real.rpow_le_rpow_of_exponent_le hq1 hεwa.le
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
  have hΛ : Λ₁' * Real.log q + (j + smax) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q := by
    have hlN : Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ (L + 1) * Real.log q := by
      rw [← Real.log_rpow hq0]
      refine Real.log_le_log hN₂0 (hN₂r.trans ?_)
      calc 2 * (q : ℝ) ^ L ≤ (q : ℝ) * (q : ℝ) ^ L := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = (q : ℝ) ^ (L + 1) := by rw [Real.rpow_add hq0, Real.rpow_one]; ring
    have h1 := mul_le_mul_of_nonneg_left hlN (by positivity : (0 : ℝ) ≤ (j : ℝ) + smax)
    have h2 := mul_le_mul_of_nonneg_right hΛ₀.symm.le hlogq.le
    linarith
  have hX : 1 ≤ (q : ℝ) ^ (L - 1 - 4 * c) := Real.one_le_rpow hq1 (by linarith)
  have hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := Nat.floor_mono (by linarith)
  -- the window `(P₁, P₂]` and the rest `(Ar, Br]`
  have hqu1 : (1 : ℝ) ≤ (q : ℝ) ^ u := Real.one_le_rpow hq1 hu.le
  have hqρ₁1 : (1 : ℝ) ≤ (q : ℝ) ^ ρ₁ := Real.one_le_rpow hq1 hρ₁0
  have hqρ₂1 : (1 : ℝ) ≤ (q : ℝ) ^ ρ₂ := Real.one_le_rpow hq1 (by linarith)
  have hquv : 6 * (q : ℝ) ^ (u + a₀) ≤ (q : ℝ) ^ v := by
    have e : (q : ℝ) ^ v = (q : ℝ) ^ (v - u - a₀) * (q : ℝ) ^ (u + a₀) := by
      rw [← Real.rpow_add hq0]; congr 1; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h6 (by positivity)
  have hqua1 : (1 : ℝ) ≤ (q : ℝ) ^ (u + a₀) := Real.one_le_rpow hq1 (by linarith)
  have hqv6 : (6 : ℝ) ≤ (q : ℝ) ^ v := by linarith
  have hP₁ge : (q : ℝ) ^ u ≤ (⌈(q : ℝ) ^ u⌉₊ : ℝ) := Nat.le_ceil _
  have hP₁lt : (⌈(q : ℝ) ^ u⌉₊ : ℝ) < (q : ℝ) ^ u + 1 := Nat.ceil_lt_add_one (by positivity)
  have hP₂le : (⌊(q : ℝ) ^ v⌋₊ : ℝ) ≤ (q : ℝ) ^ v := Nat.floor_le (by positivity)
  have hP₂gt : (q : ℝ) ^ v - 1 < (⌊(q : ℝ) ^ v⌋₊ : ℝ) := Nat.sub_one_lt_floor _
  have hBrle : (⌊(q : ℝ) ^ ρ₂⌋₊ : ℝ) ≤ (q : ℝ) ^ ρ₂ := Nat.floor_le (by positivity)
  have hP₁1 : 1 ≤ ⌈(q : ℝ) ^ u⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hP₂1 : 1 ≤ ⌊(q : ℝ) ^ v⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hBr1 : 1 ≤ ⌊(q : ℝ) ^ ρ₂⌋₊ := Nat.le_floor (by exact_mod_cast hqρ₂1)
  have hAr1 : 1 ≤ ⌈(q : ℝ) ^ ρ₁⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hArge : (q : ℝ) ^ ρ₁ ≤ (⌈(q : ℝ) ^ ρ₁⌉₊ : ℝ) := Nat.le_ceil _
  have hAB : (⌈(q : ℝ) ^ u⌉₊ + 1) * ⌈(q : ℝ) ^ a₀⌉₊ ≤ ⌊(q : ℝ) ^ v⌋₊ := by
    refine Nat.le_floor ?_
    push_cast
    have ha1 : (1 : ℝ) ≤ (q : ℝ) ^ a₀ := Real.one_le_rpow hq1 ha₀.le
    have e : (q : ℝ) ^ (u + a₀) = (q : ℝ) ^ u * (q : ℝ) ^ a₀ := Real.rpow_add hq0 _ _
    have h1 : ((⌈(q : ℝ) ^ u⌉₊ : ℝ) + 1) * (⌈(q : ℝ) ^ a₀⌉₊ : ℝ) ≤ (3 * (q : ℝ) ^ u) * (2 * (q : ℝ) ^ a₀) :=
      mul_le_mul (by linarith) (by linarith) (Nat.cast_nonneg _) (by positivity)
    rw [e] at hquv
    linarith
  have hBBr : ⌊(q : ℝ) ^ v⌋₊ * ⌊(q : ℝ) ^ ρ₂⌋₊ ≤ ⌊(q : ℝ) ^ L⌋₊ := by
    refine Nat.le_floor ?_
    push_cast
    calc (⌊(q : ℝ) ^ v⌋₊ : ℝ) * (⌊(q : ℝ) ^ ρ₂⌋₊ : ℝ) ≤ (q : ℝ) ^ v * (q : ℝ) ^ ρ₂ :=
          mul_le_mul hP₂le hBrle (Nat.cast_nonneg _) (by positivity)
      _ = (q : ℝ) ^ (v + ρ₂) := (Real.rpow_add hq0 _ _).symm
      _ ≤ (q : ℝ) ^ L := Real.rpow_le_rpow_of_exponent_le hq1 hvρ.le
  -- the zone where a stop's first variable is in its window and the rest has its size
  have hR : ∀ u' v' : ℝ, Real.logb q (⌈(q : ℝ) ^ u⌉₊ : ℝ) ≤ u' → u' ≤ Real.logb q (⌊(q : ℝ) ^ v⌋₊ : ℝ) →
      ((⌊(q : ℝ) ^ L⌋₊ / ⌊(q : ℝ) ^ ρ₂⌋₊ : ℕ) : ℝ) ≤ 4 * (q : ℝ) ^ (u' + v') →
      (q : ℝ) ^ (u' + v') ≤ ((⌊2 * (q : ℝ) ^ L⌋₊ / (⌈(q : ℝ) ^ ρ₁⌉₊ - 1 + 1) : ℕ) : ℝ) → Rg u' v' := by
    intro u' v' h1 h2 h5 h6
    have hlogb : ∀ y : ℝ, Real.logb q ((q : ℝ) ^ y) = y := fun y => Real.logb_rpow hq0 hq1'.ne'
    refine hzone u' v' ?_ ?_ ?_ ?_
    · exact le_trans ((hlogb u).symm.le.trans (Real.logb_le_logb_of_le hq1' (by positivity) hP₁ge)) h1
    · exact h2.trans ((Real.logb_le_logb_of_le hq1' (by exact_mod_cast hP₂1) hP₂le).trans (hlogb v).le)
    · -- `4q^{L−ρ₂−ε} ≤ ⌊N₁/Br⌋`
      refine (Real.rpow_le_rpow_left_iff hq1').1 ?_
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
    · -- `⌊N₂/⌈q^{ρ₁}⌉⌋ ≤ q^{L−ρ₁+ε}`
      refine (Real.rpow_le_rpow_left_iff hq1').1 (h6.trans ?_)
      rw [Nat.sub_add_cancel hAr1]
      calc ((⌊2 * (q : ℝ) ^ L⌋₊ / ⌈(q : ℝ) ^ ρ₁⌉₊ : ℕ) : ℝ)
          ≤ (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) / (⌈(q : ℝ) ^ ρ₁⌉₊ : ℝ) := Nat.cast_div_le
        _ ≤ (2 * (q : ℝ) ^ L) / (q : ℝ) ^ ρ₁ := div_le_div₀ (by positivity) hN₂r (by positivity) hArge
        _ = 2 * (q : ℝ) ^ (L - ρ₁) := by rw [mul_div_assoc, ← Real.rpow_sub hq0]
        _ ≤ (q : ℝ) ^ ε * (q : ℝ) ^ (L - ρ₁) := mul_le_mul_of_nonneg_right h2ε (by positivity)
        _ = (q : ℝ) ^ (L - ρ₁ + ε) := by rw [← Real.rpow_add hq0]; congr 1; ring
  -- the chains and the leaves at `q`
  have hokC := hq₁ q (le_trans (le_max_left _ _) hq) a ha ⌈(q : ℝ) ^ u⌉₊ ⌊(q : ℝ) ^ v⌋₊ (⌈(q : ℝ) ^ ρ₁⌉₊ - 1)
    ⌊(q : ℝ) ^ ρ₂⌋₊ hP₁1 hP₂1 hBr1 hBBr hR
  have hqn : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq3' : max (max q₃A q₃B) (max q₄ q₅) ≤ q := le_trans (le_max_right _ _) hq
  have hokL := leavesOK_mono hqn
    (hq₃A q (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hq3')) a ha) hδ₃A'
  have hokL₂ := leavesOK_mono hqn
    (hq₃B q (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hq3')) a ha) hδ₃B'
  -- the third part's boxes, and its zone
  obtain ⟨hAE1, hBE1, hBrE1, hBBrE, hRE⟩ := leaf_window (L := L) hq1' hpA hth hD₁0 hD₂0 L_pos h64D h64ε hzoneE
  have hAEle : (⌊(q : ℝ) ^ pA⌋₊ : ℝ) ≤ (q : ℝ) ^ pA := Nat.floor_le (by positivity)
  have hokE := (hq₅ q (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hq3')) a ha ⌈(q : ℝ) ^ εw⌉₊
    hw2 hw ⌊(q : ℝ) ^ pA⌋₊ ⌊4 * (q : ℝ) ^ D₁⌋₊ ⌊(q : ℝ) ^ th⌋₊ ⌊4 * (q : ℝ) ^ D₂⌋₊ hAE1 hBE1 hBrE1 hBBrE
    hRE).mono hqn hδ₄' le_rfl
  have hP₁4 : (⌈(q : ℝ) ^ u⌉₊ : ℝ) + 1 ≤ 4 * (q : ℝ) ^ L := by
    have : (q : ℝ) ^ u ≤ (q : ℝ) ^ L := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    linarith
  have H := SieveTwoP6E.prop6_two_core3 ha Ω S₀ Sr S₁ hdisj hSr eIn₁ lo hi hokL hokL₂ hokE hokC hw2
    hwle hwz hz₀ hz₀q hΛ₁'0 hlz hΛ hX hN
    (by omega) le_rfl le_rfl hP₁1 hAB (hsmA _ hP₁4) (hlogA _ (by positivity) hP₁4)
    (fun s hs => by
      have e : (q : ℝ) ^ (t + ∑ i ∈ S₀, lo i) = (q : ℝ) ^ t * (q : ℝ) ^ (∑ i ∈ S₀, lo i) := Real.rpow_add hq0 _ _
      have h1 : (q : ℝ) ^ u ≤ (q : ℝ) ^ (t + ∑ i ∈ S₀, lo i) :=
        Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
      have h2 : (q : ℝ) ^ t * (q : ℝ) ^ (∑ i ∈ S₀, lo i) ≤ (q : ℝ) ^ t * s :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      linarith)
    (by
      have e : (q : ℝ) ^ v = (q : ℝ) ^ (v - ∑ i ∈ S₀, hi i) * (q : ℝ) ^ (∑ i ∈ S₀, hi i) := by
        rw [← Real.rpow_add hq0]; congr 1; ring
      have h1 : 2 * (q : ℝ) ^ (∑ i ∈ S₀, hi i) ≤ (q : ℝ) ^ v := by
        rw [e]
        exact mul_le_mul_of_nonneg_right h2hi (by positivity)
      have h2 : (0 : ℝ) < (q : ℝ) ^ (∑ i ∈ S₀, hi i) := by positivity
      linarith)
    hεwc hpA (by rw [hΛ₁']; linarith) hth (by rw [hΛ₁']; linarith [le_max_right D₁ 1]) hszA₁
    (by rw [← hD₂def]; exact hszA₂) (by rw [← hD₁def]; exact hszB₁) (by rw [← hD₁def]; exact hszB₂) hAEle
    (by rw [← hD₁def]; exact Nat.lt_floor_add_one _) (Nat.floor_le (by positivity))
    (by rw [← hD₂def]; exact Nat.lt_floor_add_one _) hC₀ hC hkev (by omega) hkC hΩc'
    (fun rt hp hΩ' => by
      obtain ⟨hsa, hz, hb⟩ := hΩ rt hp hΩ'
      obtain ⟨hrl, hrh⟩ := box_prod hq0 Sr hb
      refine ⟨hsa, hz, hb, ?_, ?_⟩
      · have h1 : (q : ℝ) ^ ρ₁ ≤ ((∏ i ∈ Sr, rt i : ℕ) : ℝ) := by
          push_cast
          exact (Real.rpow_le_rpow_of_exponent_le hq1 hρlo).trans hrl
        have h2 : ⌈(q : ℝ) ^ ρ₁⌉₊ ≤ ∏ i ∈ Sr, rt i := Nat.ceil_le.2 h1
        omega
      · refine Nat.le_floor ?_
        push_cast
        exact hrh.trans (Real.rpow_le_rpow_of_exponent_le hq1 hρhi))
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
        have := mul_lt_mul_of_pos_left (show (2 : ℝ) < q by linarith) hX0
        linarith
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
  have hfin : (4 * ((2 * smax : ℕ) : ℝ) + 5) * (q : ℝ) ^ (L - 2 * δ₀) ≤ (q : ℝ) ^ (L - δ₀) := by
    have e : (q : ℝ) ^ (L - δ₀) = (q : ℝ) ^ δ₀ * (q : ℝ) ^ (L - 2 * δ₀) := by
      rw [← Real.rpow_add hq0]; ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_right hδ2 (by positivity)
  have hφi : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hs0 : (0 : ℝ) ≤ (smax : ℝ) := Nat.cast_nonneg _
  have he₁ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₁) := by positivity
  have he₃ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₃) := by positivity
  refine final_bound (le_trans H ?_) hsd
    (mul_nonneg (mul_nonneg zero_le_two hζ) (div_nonneg hN0 (mul_pos hφ hlogw0).le))
    (mul_nonneg (mul_nonneg zero_le_two (SieveProp6.rem_nonneg _ _ k)) (Real.rpow_nonneg hq0.le _)) hmain hrem
    (by positivity) (by positivity) (hle c hm.1) (hle δ₁ hm.2.1) (hle δ₁ hm.2.1) (hle δ₃ hm.2.2) hfin
  have h1 := mul_nonneg hs0 he₃
  have h2 := mul_nonneg hs0 he₁
  push_cast
  linarith


omit [Route] in
/-- **Harman's comparison with stops in two variables with a box of leaves cut in three, for an exponent
`2 < L ≤ 5/2`**: `prop6_two3` with no route. -/
theorem prop6_two3_at {L : ℝ} (hL2 : 2 < L) (hL : L ≤ 5 / 2) {Rg : ℝ → ℝ → Prop} (hII : TypeIITwoAt L Rg) (j J₀ : ℕ) {Λ₁ a₀ : ℝ} (hΛ₁ : 0 ≤ Λ₁)
    (ha₀ : 0 < a₀) (lo hi : Fin j → ℝ) (S₀ Sr S₁ : Finset (Fin j)) (hdisj : Disjoint S₀ Sr) (hSr : Sr.Nonempty)
    (eIn₁ : Bool) {t u v ρ₁ ρ₂ ε : ℝ} (hu : 0 < u) (huv : u + a₀ < v) (hρ₁0 : 0 ≤ ρ₁) (hρ : ρ₁ ≤ ρ₂)
    (hvρ : v + ρ₂ < L) (hρlo : ρ₁ ≤ ∑ i ∈ Sr, lo i) (hρhi : ∑ i ∈ Sr, hi i ≤ ρ₂) (hε : 0 < ε)
    (hzone : ∀ m₁ m₂ : ℝ, u ≤ m₁ → m₁ ≤ v → L - ρ₂ - ε ≤ m₁ + m₂ → m₁ + m₂ ≤ L - ρ₁ + ε → Rg m₁ m₂)
    (hlo : u - ∑ i ∈ S₀, lo i ≤ t) (hhi : ∑ i ∈ S₀, hi i < v)
    {pA th εE : ℝ} (hpA : 0 ≤ pA) (hth : 0 ≤ th) (hεE : 0 < εE)
    (hDA₁ : pA < L - 1) (hDA₂ : max pA 1 + pA + 2 * (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t)) < 2 * L - 1)
    (hDB₁ : (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) < L - 1) (hDB₂ : max (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) 1 + (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) + 2 * th < 2 * L - 1)
    (hDL : (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) + (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t)) < L) (hD₁0 : 0 ≤ (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0))) (hD₂0 : 0 ≤ (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t)))
    (hzoneE : ∀ m₁ m₂ : ℝ, pA - εE ≤ m₁ → m₁ ≤ (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) + εE → L - (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t)) - εE ≤ m₁ + m₂ →
      m₁ + m₂ ≤ L - th + εE → SieveLeafTwo.LeafZoneX L m₁ m₂)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ Ω : List (GCmp j), Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      (∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
        StrictAnti rt ∧ (∀ i, ⌈(q : ℝ) ^ a₀⌉₊ ≤ rt i) ∧ ∀ i, (q : ℝ) ^ lo i ≤ rt i ∧ (rt i : ℝ) ≤ (q : ℝ) ^ hi i) →
      ‖∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
          dw q a n * (if (∏ i, rt i) ∣ n ∧ rough ⌈(q : ℝ) ^ a₀⌉₊ n then 1 else 0)‖ ≤
        η * (q : ℝ) ^ L / (q.totient * Real.log q) + (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  let _ : Route := SieveTwoTerm.routeOf L
  have _ : RouteOK := SieveTwoTerm.routeOK_of hL2 hL
  exact prop6_two3 hII j J₀ hΛ₁ ha₀ lo hi S₀ Sr S₁ hdisj hSr eIn₁ hu huv hρ₁0 hρ hvρ hρlo hρhi hε hzone hlo hhi
    hpA hth hεE hDA₁ hDA₂ hDB₁ hDB₂ hDL hD₁0 hD₂0 hzoneE hη

end SieveTwoCompE
