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

The file imports `SieveAdTwo.lean`, `SieveAdFillDefs.lean` and `SieveFillComp.lean`.
-/
import SieveAdTwo
import SieveAdFillDefs
import SieveFillComp

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRoute SieveChain SieveFamily

namespace SieveAd

open Classical
open SieveCert (DEN DEN_pos')

variable [Route] [RouteOK] [SieveCert.IBPar] [IBFits]

open SieveCert.IBPar (Lnum Lden)

set_option maxHeartbeats 1600000 in
/-- **The comparison with the rest among the tree's primes, on a box, under more atoms.** If `chkJ3` passes the
box at the floor `f`, for the sets `s0`, `s1`, the flag `e`, the window `[u, v]`, the growth `t` and the rests'
range `[r₁, r₂]`, then the terms of the box at the floor `x^{f/DEN}` are evaluated under `m` more atoms, uniformly
in the atoms, when the box's atoms and those are at most `40`. -/
theorem evJ_fillE (bl : List Cell) (k : ℕ) (h : bl.length = k) (f s0 s1 : ℕ) (e : Bool) (u v t r1 r2 : ℕ)
    (hok : chkJ3 bl f s0 s1 e u v t r1 r2 = true) {m : ℕ} (hm : 3 * min k 13 + m ≤ 40) :
    ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a → ∀ E : List (Atom k), E.length ≤ m →
      ThrOK q E → |dJP q a f (boxFn bl k h) (fun rt => ∀ A ∈ E, A.sem rt)| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q) := by
  simp only [chkJ3, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hf0, hlen⟩, hcells⟩, z1⟩, z2⟩, z3⟩, z4⟩, z5⟩, z6⟩, q1⟩, p1⟩, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩ := hok
  have hc := (cellsFrom_iff f bl).1 hcells
  set bx := boxFn bl k h with hbx
  have hbxc : ∀ i, f ≤ (bx i).1 ∧ (bx i).1 ≤ (bx i).2 ∧ (bx i).2 ≤ DEN := fun i => hc _ (boxFn_mem bl k h i)
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
