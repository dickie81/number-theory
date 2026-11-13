/-
# The tests with no window are sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveAdFillDefs.lean`'s test `okJ3` of a box at a floor, by Harman's comparison in two variables with the rest
among the primes of the tree below the floor (`SieveFillComp.prop6_fill_at`), and the tests `fillTests` of a
decomposition with no window.

* `evJ_fillE`: if `chkJ3` passes a box at a floor, the terms of the box at the floor are evaluated under `m` more
  atoms, uniformly in the atoms, when the box's atoms and those are at most `40`; `evJ_fill` with none.
* `fillTests_sound`, `fillTests_soundX`: **the tests with no window are sound**, and sound under two more atoms
  on the boxes of at most twelve primes.

The proof of `evJ_fillE` is `SieveAdTwo.evJ_twoE`'s: the box's cells give the exponents of `q`, `κ = L/DEN` for a
unit; the rest's range is `[κr₁, κr₂]` in place of the sums over a set of the box's primes, and the leaves' growth
`κ(t + r₂)`.

* `evJ_fill_core3`: **the comparison on the sums of a box, the leaves cut in three**, by
  `SieveFillCompE.prop6_fill3_at` (as `SieveAd.evJ_two_core3` for the rest among the box's primes); `evJ_fillE` takes
  it where `chkJ3`'s leaves are cut in three.

The file imports `SieveAdTwo.lean`, `SieveAdFillDefs.lean`, `SieveFillComp.lean` and `SieveFillCompE.lean`.
-/
import SieveAdTwo
import SieveAdFillDefs
import SieveFillComp
import SieveFillCompE

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRoute SieveChain SieveFamily

namespace SieveAd

open Classical
open SieveCert (DEN DEN_pos')

variable [Route] [RouteOK] [SieveCert.IBPar] [IBFits]

open SieveCert.IBPar (Lnum Lden)

set_option maxHeartbeats 1600000 in
/-- **The comparison with the rest among the tree's primes, on the sums of a box, the leaves cut in three, under
more atoms.** For a box `bx` with `f ≤ lo ≤ hi ≤ DEN`, sets `S₀`, `S₁` of its indices and numbers that bound their
sums as for `SieveAd.evJ_fill_core` and pass its checks but those of the leaves at the floor `f`, the leaves' sizes
with the growth `t + r₂` passing `leavesE`: the terms of the box at the floor `x^{f/DEN}` are evaluated under `m`
more atoms, uniformly in the atoms. -/
theorem evJ_fill_core3 {k : ℕ} (bx : Fin k → Cell) (f : ℕ) (S₀ S₁ : Finset (Fin k)) (e : Bool)
    (u v t r1 r2 c0lo c0hi h1s h2s : ℕ) (hf0 : 0 < f) (z1 : Lden * DEN + 2000 * Lnum ≤ 2000 * Lnum * r1)
    (z2 : 2 * Lden * DEN ≤ 3 * Lnum * u) (z3 : 2 * Lden * DEN + 3 * Lnum * (r2 + 1 + v) ≤ 3 * Lnum * DEN)
    (z4 : 62505 * Lden * DEN + 27637 * Lnum ≤ 62500 * Lnum * u + 27637 * Lnum * r1)
    (z5 : 62505 * Lden * DEN + 62500 * Lnum * v + 34863 * Lnum * (r2 + 1) ≤ 62500 * Lnum * DEN)
    (z6 : 125005 * Lden * DEN + 34863 * Lnum * (r2 + 1) ≤ 62500 * Lnum * DEN) (q1 : r1 + f < r2) (p1 : u + f < v)
    (p2 : u ≤ t + c0lo) (p3 : c0hi < v) (hE : leavesE (h1s + cond e (t + r2) 0) (h2s + cond e 0 (t + r2)) = true)
    (hbxc : ∀ i, f ≤ (bx i).1 ∧ (bx i).1 ≤ (bx i).2 ∧ (bx i).2 ≤ DEN)
    (h0lo : c0lo ≤ ∑ i ∈ S₀, (bx i).1) (h0hi : ∑ i ∈ S₀, (bx i).2 ≤ c0hi) (h1 : ∑ i ∈ S₁, (bx i).2 ≤ h1s)
    (h2 : ∑ i ∈ S₁ᶜ, (bx i).2 ≤ h2s) {m J₀ : ℕ} (hm : 3 * k + m ≤ J₀) :
    ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a → ∀ E : List (Atom k), E.length ≤ m →
      ThrOK q E → |dJP q a f bx (fun rt => ∀ A ∈ E, A.sem rt)| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q) := by
  set D₁ := h1s + cond e (t + r2) 0 with hD₁def
  set D₂ := h2s + cond e 0 (t + r2) with hD₂def
  obtain ⟨P, θ, hLP, hLθ, hDD, hP1, hθ1, hxr⟩ := leavesE_cuts hE
  have hLP' := leavesL_real hLP
  have hLθ' := leavesL_real hLθ
  -- the reals
  have hD := DEN_pos'
  have hL0 : 0 < L := L_pos
  obtain ⟨hden, hLnum⟩ := lnum_eq
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = L / DEN := ⟨_, rfl⟩
  rw [← hκdef] at hLnum hLP' hLθ'
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
  have Z1 : 1 + 2000 * κ ≤ 2000 * (κ * r1) := conv (by
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
  have Z3 : 2 + 3 * (κ * (r2 + 1 + v)) ≤ 3 * L := conv (by
    have := cast z3
    push_cast at this
    rw [hLnum'] at this
    have e1 : (2 : ℝ) * Lden * DEN = 2 * M := by rw [hMdef]; ring
    rw [e1] at this
    have e2 : M * (3 * L) = 3 * (M * κ) * DEN := by rw [← hκD]; ring
    rw [e2]
    linarith)
  have Z4 : 62505 + 27637 * κ ≤ 62500 * (κ * u) + 27637 * (κ * r1) := conv (by
    have := cast z4
    push_cast at this
    rw [hLnum'] at this
    have e1 : (62505 : ℝ) * Lden * DEN = 62505 * M := by rw [hMdef]; ring
    rw [e1] at this
    linarith)
  have Z5 : 62505 + 62500 * (κ * v) + 34863 * (κ * (r2 + 1)) ≤ 62500 * L := conv (by
    have := cast z5
    push_cast at this
    rw [hLnum'] at this
    have e1 : (62505 : ℝ) * Lden * DEN = 62505 * M := by rw [hMdef]; ring
    rw [e1] at this
    have e2 : M * (62500 * L) = 62500 * (M * κ) * DEN := by rw [← hκD]; ring
    rw [e2]
    linarith)
  have Z6 : 125005 + 34863 * (κ * (r2 + 1)) ≤ 62500 * L := conv (by
    have := cast z6
    push_cast at this
    rw [hLnum'] at this
    have e1 : (125005 : ℝ) * Lden * DEN = 125005 * M := by rw [hMdef]; ring
    rw [e1] at this
    have e2 : M * (62500 * L) = 62500 * (M * κ) * DEN := by rw [← hκD]; ring
    rw [e2]
    linarith)
  -- the sums over the sets
  have hs0lo : κ * (c0lo : ℝ) ≤ ∑ i ∈ S₀, κ * ((bx i).1 : ℝ) := by
    rw [← Finset.mul_sum, ← Nat.cast_sum]
    exact mul_le_mul_of_nonneg_left (cast h0lo) hκ.le
  have hs0hi : ∑ i ∈ S₀, κ * ((bx i).2 : ℝ) ≤ κ * (c0hi : ℝ) := by
    rw [← Finset.mul_sum, ← Nat.cast_sum]
    exact mul_le_mul_of_nonneg_left (cast h0hi) hκ.le
  have hs1 : ∑ i ∈ S₁, κ * ((bx i).2 : ℝ) ≤ κ * (h1s : ℝ) := by
    rw [← Finset.mul_sum, ← Nat.cast_sum]
    exact mul_le_mul_of_nonneg_left (cast h1) hκ.le
  have hs2 : ∑ i ∈ S₁ᶜ, κ * ((bx i).2 : ℝ) ≤ κ * (h2s : ℝ) := by
    rw [← Finset.mul_sum, ← Nat.cast_sum]
    exact mul_le_mul_of_nonneg_left (cast h2) hκ.le
  have hs1' : 0 ≤ ∑ i ∈ S₁, κ * ((bx i).2 : ℝ) := Finset.sum_nonneg fun i _ => by positivity
  have hs2' : 0 ≤ ∑ i ∈ S₁ᶜ, κ * ((bx i).2 : ℝ) := Finset.sum_nonneg fun i _ => by positivity
  -- the conditions of the comparison
  have hu : 0 < κ * (u : ℝ) := by linarith
  have huv : κ * (u : ℝ) + κ * (f : ℝ) < κ * (v : ℝ) := by
    have := mul_lt_mul_of_pos_left (castlt p1) hκ
    push_cast at this
    linarith
  have hτ : 0 < κ * (r1 : ℝ) := by linarith
  have hτρ : κ * (r1 : ℝ) + κ * (f : ℝ) < κ * (r2 : ℝ) := by
    have := mul_lt_mul_of_pos_left (castlt q1) hκ
    push_cast at this
    linarith
  have hvρ : κ * (v : ℝ) + κ * (r2 : ℝ) < L := by linarith
  have hzone : ∀ m₁ m₂ : ℝ, κ * (u : ℝ) ≤ m₁ → m₁ ≤ κ * (v : ℝ) → L - κ * (r2 : ℝ) - κ ≤ m₁ + m₂ →
      m₁ + m₂ ≤ L - κ * (r1 : ℝ) + κ → SieveTwoZone7D.Zone7d L m₁ m₂ := by
    intro m₁ m₂ h1 h2 h3 h4
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have ht : 0 ≤ κ * (t : ℝ) := by positivity
  have hlo : κ * (u : ℝ) - ∑ i ∈ S₀, κ * ((bx i).1 : ℝ) ≤ κ * (t : ℝ) := by
    have := mul_le_mul_of_nonneg_left (cast p2) hκ.le
    push_cast at this
    linarith
  have hhi : ∑ i ∈ S₀, κ * ((bx i).2 : ℝ) < κ * (v : ℝ) :=
    lt_of_le_of_lt hs0hi (mul_lt_mul_of_pos_left (castlt p3) hκ)
  -- the leaves' sizes
  have hk1 : κ * (h1s : ℝ) + (if e then κ * (t : ℝ) + κ * (r2 : ℝ) else 0) = κ * (D₁ : ℝ) := by
    rw [hD₁def]
    cases e <;> simp [mul_add]
  have hk2 : κ * (h2s : ℝ) + (if e then 0 else κ * (t : ℝ) + κ * (r2 : ℝ)) = κ * (D₂ : ℝ) := by
    rw [hD₂def]
    cases e <;> simp [mul_add]
  have ht0 : 0 ≤ κ * (t : ℝ) + κ * (r2 : ℝ) := by positivity
  have hif1 : 0 ≤ (if e then κ * (t : ℝ) + κ * (r2 : ℝ) else 0) := by cases e <;> simp [ht0]
  have hif2 : 0 ≤ (if e then 0 else κ * (t : ℝ) + κ * (r2 : ℝ)) := by cases e <;> simp [ht0]
  have hX : ∑ i ∈ S₁, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) + κ * (r2 : ℝ) else 0) ≤ κ * (D₁ : ℝ) := by linarith
  have hY : ∑ i ∈ S₁ᶜ, κ * ((bx i).2 : ℝ) + (if e then 0 else κ * (t : ℝ) + κ * (r2 : ℝ)) ≤ κ * (D₂ : ℝ) := by linarith
  have hD₁0 : 0 ≤ ∑ i ∈ S₁, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) + κ * (r2 : ℝ) else 0) := by linarith
  have hD₂0 : 0 ≤ ∑ i ∈ S₁ᶜ, κ * ((bx i).2 : ℝ) + (if e then 0 else κ * (t : ℝ) + κ * (r2 : ℝ)) := by linarith
  obtain ⟨a4, a5, a6⟩ := hLP'
  obtain ⟨b4, b5, b6⟩ := hLθ'
  have hpA : 0 ≤ κ * (P : ℝ) := by positivity
  have hth : 0 ≤ κ * (θ : ℝ) := by positivity
  have hDA₁ : κ * (P : ℝ) < L - 1 := by linarith
  have hDA₂ : max (κ * (P : ℝ)) 1 + κ * (P : ℝ) +
      2 * (∑ i ∈ S₁ᶜ, κ * ((bx i).2 : ℝ) + (if e then 0 else κ * (t : ℝ) + κ * (r2 : ℝ))) < 2 * L - 1 := by
    rcases le_total (κ * (P : ℝ)) 1 with hle | hle
    · rw [max_eq_right hle]
      linarith
    · rw [max_eq_left hle]
      linarith
  have hDB₁ : ∑ i ∈ S₁, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) + κ * (r2 : ℝ) else 0) < L - 1 := by linarith
  have hDB₂ : max (∑ i ∈ S₁, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) + κ * (r2 : ℝ) else 0)) 1 +
      (∑ i ∈ S₁, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) + κ * (r2 : ℝ) else 0)) + 2 * (κ * (θ : ℝ)) <
        2 * L - 1 := by
    have hmax : max (∑ i ∈ S₁, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) + κ * (r2 : ℝ) else 0)) 1 ≤
        max (κ * (D₁ : ℝ)) 1 :=
      max_le_max hX le_rfl
    rcases le_total (κ * (D₁ : ℝ)) 1 with hle | hle
    · rw [max_eq_right hle] at hmax
      linarith
    · rw [max_eq_left hle] at hmax
      linarith
  have hDL : (∑ i ∈ S₁, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) + κ * (r2 : ℝ) else 0)) +
      (∑ i ∈ S₁ᶜ, κ * ((bx i).2 : ℝ) + (if e then 0 else κ * (t : ℝ) + κ * (r2 : ℝ))) < L := by
    have h12 : κ * ((D₁ : ℝ) + D₂) < κ * DEN := mul_lt_mul_of_pos_left (by exact_mod_cast hDD) hκ
    linarith
  -- the region on the rectangle
  have hz : ∀ {m₁ ρ : ℝ}, κ * ((P - 1 : ℕ) : ℝ) ≤ m₁ → m₁ ≤ κ * ((D₁ + 1 : ℕ) : ℝ) → κ * ((θ - 1 : ℕ) : ℝ) ≤ ρ →
      ρ ≤ κ * ((D₂ + 1 : ℕ) : ℝ) → SieveLeafZoneX.LeafZoneXL L m₁ (L - m₁ - ρ) := fun h1 h2 h3 h4 => by
    have := SieveLeafZoneX.leafXR_sound (Ln := Lnum) (Ld := Lden) (D := DEN) (κ := κ) (by exact_mod_cast hden)
      (by exact_mod_cast hD) (by rw [hLnum]) hxr h1 h2 h3 h4
    rwa [hκD] at this
  have hPc : ((P - 1 : ℕ) : ℝ) = (P : ℝ) - 1 := by rw [Nat.cast_sub hP1]; norm_num
  have hθc : ((θ - 1 : ℕ) : ℝ) = (θ : ℝ) - 1 := by rw [Nat.cast_sub hθ1]; norm_num
  have hεE : 0 < κ / 2 := by positivity
  have hzoneE : ∀ m₁ m₂ : ℝ, κ * (P : ℝ) - κ / 2 ≤ m₁ →
      m₁ ≤ (∑ i ∈ S₁, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) + κ * (r2 : ℝ) else 0)) + κ / 2 →
      L - (∑ i ∈ S₁ᶜ, κ * ((bx i).2 : ℝ) + (if e then 0 else κ * (t : ℝ) + κ * (r2 : ℝ))) - κ / 2 ≤ m₁ + m₂ →
      m₁ + m₂ ≤ L - κ * (θ : ℝ) + κ / 2 → SieveLeafTwo.LeafZoneX L m₁ m₂ := by
    intro m₁ m₂ h1 h2 h3 h4
    have hr := hz (m₁ := m₁) (ρ := L - m₁ - m₂) (by rw [hPc]; linarith) (by push_cast; linarith)
      (by rw [hθc]; linarith) (by push_cast; linarith)
    have e3 : L - m₁ - (L - m₁ - m₂) = m₂ := by ring
    rw [e3] at hr
    exact SieveLeafZoneX.leafZoneX_of_XL hr
  intro η hη
  obtain ⟨δ, hδ, q₀, hq₀⟩ := SieveFillCompE.prop6_fill3_at two_lt_L L_le (SieveFamilyTwo.typeIITwoAt_hx L) k J₀
    (Λ₁ := L + 1) (a₀ := κ * (f : ℝ)) (by linarith) (mul_pos hκ (by exact_mod_cast hf0))
    (fun i => κ * ((bx i).1 : ℝ)) (fun i => κ * ((bx i).2 : ℝ)) S₀ S₁ e
    hu huv hτ hτρ hvρ hκ hzone ht hlo hhi rfl rfl hpA hth hεE hDA₁ hDA₂ hDB₁ hDB₂ hDL hD₁0 hD₂0 hzoneE
    (η := η / (2 * L)) (by positivity)
  filter_upwards [eventually_ge_atTop q₀, eventually_ge_atTop 2, le_Xq hδ (half_pos hη)] with q hq hq2 hX a ha
    E hEl hEt
  have : NeZero q := ⟨by omega⟩
  have hq1 : 1 ≤ q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hx1 : 1 ≤ xq q := Real.one_le_rpow hq1' hL0.le
  have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (show 0 < q by omega)
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hthr : ThrOK q (specB q bx ++ E) :=
    thrOK_append (thrOK_specB hq1 hL0.le bx fun i => ⟨(hbxc i).2.1.trans (hbxc i).2.2, (hbxc i).2.2⟩) hEt
  have hmain := hq₀ q hq a ha ((specB q bx ++ E).map Atom.toG)
    (by rw [List.length_map, List.length_append]; have := specB_length q bx; omega) (c_le_of_thrOK hq1 hthr)
    (fun rt hp hΩ => by
      obtain ⟨hsa, hcc⟩ := (sem_specB q bx rt).1
        fun A hA => (holds_iff_sem hthr hp).1 hΩ A (List.mem_append_left _ hA)
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
  rw [dJP_eq_famSet, ← qpow_eq q f, ← hκdef]
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

set_option maxHeartbeats 1600000 in
/-- **The comparison with the rest among the tree's primes, on a box, under more atoms.** If `chkJ3` passes the
box at the floor `f`, for the sets `s0`, `s1`, the flag `e`, the window `[u, v]`, the growth `t` and the rests'
range `[r₁, r₂]`, then the terms of the box at the floor `x^{f/DEN}` are evaluated under `m` more atoms, uniformly
in the atoms, when the box's atoms and those are at most `40`. -/
theorem evJ_fillE (bl : List Cell) (k : ℕ) (h : bl.length = k) (f s0 s1 : ℕ) (e : Bool) (u v t r1 r2 : ℕ)
    (hok : chkJ3 bl f s0 s1 e u v t r1 r2 = true) {m : ℕ} (hm : 3 * min k 13 + m ≤ 40) :
    ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a → ∀ E : List (Atom k), E.length ≤ m →
      ThrOK q E → |dJP q a f (boxFn bl k h) (fun rt => ∀ A ∈ E, A.sem rt)| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q) := by
  simp only [chkJ3, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hf0, hlen⟩, hcells⟩, z1⟩, z2⟩, z3⟩, z4⟩, z5⟩, z6⟩, q1⟩, p1⟩, p2⟩, p3⟩, hlv⟩ := hok
  have hc := (cellsFrom_iff f bl).1 hcells
  set bx := boxFn bl k h with hbx
  have hbxc : ∀ i, f ≤ (bx i).1 ∧ (bx i).1 ≤ (bx i).2 ∧ (bx i).2 ≤ DEN := fun i => hc _ (boxFn_mem bl k h i)
  -- the leaves cut in three
  rcases hlv with hlv | hE
  swap
  · exact evJ_fill_core3 bx f (mset k s0) (mset k s1) e u v t r1 r2 _ _ _ _ hf0 z1 z2 z3 z4 z5 z6 q1 p1 p2 p3 hE
      hbxc (sum_mset (fun c => c.1) bl k h s0).ge (sum_mset (fun c => c.2) bl k h s0).le
      (sum_mset (fun c => c.2) bl k h s1).le (sum_mset_compl bl k h s1).le (J₀ := 40) (by omega)
  simp only [leavesL, Bool.and_eq_true, Nat.blt_eq, Nat.mul_eq, Nat.add_eq] at hlv
  obtain ⟨⟨p4, p5⟩, p6⟩ := hlv
  -- the sums of the test
  set c0lo := mSum (fun c => c.1) bl s0 with hc0lo
  set c0hi := mSum (fun c => c.2) bl s0 with hc0hi
  set h1s := mSum (fun c => c.2) bl s1 with hh1s
  set D₁ := h1s + cond e (t + r2) 0 with hD₁def
  set D₂ := hiSum bl - h1s + cond e 0 (t + r2) with hD₂def
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
  have Z1 : 1 + 2000 * κ ≤ 2000 * (κ * r1) := conv (by
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
  have Z3 : 2 + 3 * (κ * (r2 + 1 + v)) ≤ 3 * L := conv (by
    have := cast z3
    push_cast at this
    rw [hLnum'] at this
    have e1 : (2 : ℝ) * Lden * DEN = 2 * M := by rw [hMdef]; ring
    rw [e1] at this
    have e2 : M * (3 * L) = 3 * (M * κ) * DEN := by rw [← hκD]; ring
    rw [e2]
    linarith)
  have Z4 : 62505 + 27637 * κ ≤ 62500 * (κ * u) + 27637 * (κ * r1) := conv (by
    have := cast z4
    push_cast at this
    rw [hLnum'] at this
    have e1 : (62505 : ℝ) * Lden * DEN = 62505 * M := by rw [hMdef]; ring
    rw [e1] at this
    linarith)
  have Z5 : 62505 + 62500 * (κ * v) + 34863 * (κ * (r2 + 1)) ≤ 62500 * L := conv (by
    have := cast z5
    push_cast at this
    rw [hLnum'] at this
    have e1 : (62505 : ℝ) * Lden * DEN = 62505 * M := by rw [hMdef]; ring
    rw [e1] at this
    have e2 : M * (62500 * L) = 62500 * (M * κ) * DEN := by rw [← hκD]; ring
    rw [e2]
    linarith)
  have Z6 : 125005 + 34863 * (κ * (r2 + 1)) ≤ 62500 * L := conv (by
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
  -- the sums over the sets
  have hsumlo : ∀ m : ℕ, ∑ i ∈ mset k m, κ * ((bx i).1 : ℝ) = κ * ((mSum (fun c => c.1) bl m : ℕ) : ℝ) :=
    fun m => by rw [← Finset.mul_sum, ← Nat.cast_sum, hbx, sum_mset (fun c => c.1) bl k h m]
  have hsumhi : ∀ m : ℕ, ∑ i ∈ mset k m, κ * ((bx i).2 : ℝ) = κ * ((mSum (fun c => c.2) bl m : ℕ) : ℝ) :=
    fun m => by rw [← Finset.mul_sum, ← Nat.cast_sum, hbx, sum_mset (fun c => c.2) bl k h m]
  have hsumc : ∑ i ∈ (mset k s1)ᶜ, κ * ((bx i).2 : ℝ) = κ * ((hiSum bl - h1s : ℕ) : ℝ) := by
    rw [← Finset.mul_sum, ← Nat.cast_sum, hbx, sum_mset_compl bl k h s1]
  -- the conditions of the comparison
  have hu : 0 < κ * (u : ℝ) := by linarith
  have huv : κ * (u : ℝ) + κ * (f : ℝ) < κ * (v : ℝ) := by
    have := mul_lt_mul_of_pos_left (castlt p1) hκ
    push_cast at this
    linarith
  have hτ : 0 < κ * (r1 : ℝ) := by linarith
  have hτρ : κ * (r1 : ℝ) + κ * (f : ℝ) < κ * (r2 : ℝ) := by
    have := mul_lt_mul_of_pos_left (castlt q1) hκ
    push_cast at this
    linarith
  have hvρ : κ * (v : ℝ) + κ * (r2 : ℝ) < L := by linarith
  have hzone : ∀ m₁ m₂ : ℝ, κ * (u : ℝ) ≤ m₁ → m₁ ≤ κ * (v : ℝ) → L - κ * (r2 : ℝ) - κ ≤ m₁ + m₂ →
      m₁ + m₂ ≤ L - κ * (r1 : ℝ) + κ → SieveTwoZone7D.Zone7d L m₁ m₂ := by
    intro m₁ m₂ h1 h2 h3 h4
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have ht : 0 ≤ κ * (t : ℝ) := by positivity
  have hlo : κ * (u : ℝ) - ∑ i ∈ mset k s0, κ * ((bx i).1 : ℝ) ≤ κ * (t : ℝ) := by
    rw [hsumlo s0, ← hc0lo]
    have := mul_le_mul_of_nonneg_left (cast p2) hκ.le
    push_cast at this
    linarith
  have hhi : ∑ i ∈ mset k s0, κ * ((bx i).2 : ℝ) < κ * (v : ℝ) := by
    rw [hsumhi s0, ← hc0hi]
    exact mul_lt_mul_of_pos_left (castlt p3) hκ
  have hk1 : κ * (h1s : ℝ) + (if e then κ * (t : ℝ) + κ * (r2 : ℝ) else 0) = κ * (D₁ : ℝ) := by
    rw [hD₁def]
    cases e <;> simp [mul_add]
  have hk2 : κ * ((hiSum bl - h1s : ℕ) : ℝ) + (if e then 0 else κ * (t : ℝ) + κ * (r2 : ℝ)) = κ * (D₂ : ℝ) := by
    rw [hD₂def]
    cases e <;> simp [mul_add]
  have hD₁ : ∑ i ∈ mset k s1, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) + κ * (r2 : ℝ) else 0) < L - 1 := by
    rw [hsumhi s1, ← hh1s, hk1]
    linarith
  have hD₂ : max (∑ i ∈ mset k s1, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) + κ * (r2 : ℝ) else 0)) 1 +
      (∑ i ∈ mset k s1, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) + κ * (r2 : ℝ) else 0)) +
        2 * (∑ i ∈ (mset k s1)ᶜ, κ * ((bx i).2 : ℝ) + (if e then 0 else κ * (t : ℝ) + κ * (r2 : ℝ))) <
          2 * L - 1 := by
    rw [hsumhi s1, ← hh1s, hk1, hsumc, hk2]
    rcases le_total (κ * (D₁ : ℝ)) 1 with hle | hle
    · rw [max_eq_right hle]
      linarith
    · rw [max_eq_left hle]
      linarith
  intro η hη
  obtain ⟨δ, hδ, q₀, hq₀⟩ := SieveFillComp.prop6_fill_at two_lt_L L_le (SieveFamilyTwo.typeIITwoAt_hx L) k 40
    (Λ₁ := L + 1) (a₀ := κ * (f : ℝ)) (by linarith) (mul_pos hκ (by exact_mod_cast hf0))
    (fun i => κ * ((bx i).1 : ℝ)) (fun i => κ * ((bx i).2 : ℝ)) (mset k s0) (mset k s1) e
    hu huv hτ hτρ hvρ hκ hzone ht hlo hhi hD₁ hD₂ (η := η / (2 * L)) (by positivity)
  filter_upwards [eventually_ge_atTop q₀, eventually_ge_atTop 2, le_Xq hδ (half_pos hη)] with q hq hq2 hX a ha
    E hEl hEt
  have : NeZero q := ⟨by omega⟩
  have hq1 : 1 ≤ q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hx1 : 1 ≤ xq q := Real.one_le_rpow hq1' hL0.le
  have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (show 0 < q by omega)
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hthr : ThrOK q (specB q bx ++ E) :=
    thrOK_append (thrOK_specB hq1 hL0.le bx fun i => ⟨(hbxc i).2.1.trans (hbxc i).2.2, (hbxc i).2.2⟩) hEt
  have hmain := hq₀ q hq a ha ((specB q bx ++ E).map Atom.toG)
    (by rw [List.length_map, List.length_append]; have := specB_length q bx; omega) (c_le_of_thrOK hq1 hthr)
    (fun rt hp hΩ => by
      obtain ⟨hsa, hcc⟩ := (sem_specB q bx rt).1
        fun A hA => (holds_iff_sem hthr hp).1 hΩ A (List.mem_append_left _ hA)
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
  rw [dJP_eq_famSet, ← qpow_eq q f, ← hκdef]
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

/-- **The comparison with the rest among the tree's primes, on a box.** If `chkJ3` passes the box at the floor
`f`, then the terms of the box at the floor `x^{f/DEN}` are evaluated. -/
theorem evJ_fill (bl : List Cell) (k : ℕ) (h : bl.length = k) (f s0 s1 : ℕ) (e : Bool) (u v t r1 r2 : ℕ)
    (hok : chkJ3 bl f s0 s1 e u v t r1 r2 = true) : EvJ f (boxFn bl k h) := by
  intro η hη
  filter_upwards [evJ_fillE bl k h f s0 s1 e u v t r1 r2 hok (m := 0) (by omega) η hη] with q hq a ha
  have h' := hq a ha [] le_rfl (thrOK_nil q)
  rwa [dJP_nil] at h'

/-- **The tests with no window are sound**: a box that passes one has its term, or its terms at the floor,
evaluated. -/
theorem fillTests_sound : (fillTests).Sound := by
  refine ⟨fun bl cfg k' h hok => evI_okI2 bl cfg k' h hok, fun bl f cfg k h hok => ?_⟩
  simp only [fillTests] at hok
  cases hk : Nat.beq cfg.kind 2
  · rw [hk] at hok
    exact evJ_okJ2 bl f cfg k h hok
  · rw [hk] at hok
    exact evJ_fill bl k h f cfg.s0 cfg.s1 cfg.e _ _ _ _ _ hok

/-- **The tests with no window are sound under two more atoms**, on the boxes of at most twelve primes. -/
theorem fillTests_soundX : (fillTests).SoundX := by
  refine ⟨fun bl cfg k' h hk hok => evI_twoE bl k' h cfg.s0 cfg.sr hok (m := 2) (by omega),
    fun bl f cfg k h hk hok => ?_⟩
  simp only [fillTests] at hok
  cases hk2 : Nat.beq cfg.kind 2
  · rw [hk2] at hok
    exact evJ_twoE bl k h f cfg.s0 cfg.sr cfg.s1 cfg.e _ _ _ hok (m := 2) (by omega)
  · rw [hk2] at hok
    exact evJ_fillE bl k h f cfg.s0 cfg.s1 cfg.e _ _ _ _ _ hok (m := 2) (by omega)

end SieveAd

#print axioms SieveAd.fillTests_sound
#print axioms SieveAd.fillTests_soundX
