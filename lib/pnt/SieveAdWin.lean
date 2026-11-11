/-
# The window's tests for a tree of Buchstab steps are sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. The setting is `SieveQ`'s: a route with `RouteOK`, a grid of the certificate with `GridOK`, the two
fitting (`Fits`), the bilinear Type I rule's exponent the route's (`IBFits`), and the route's Type II estimate as a
hypothesis (`hII`). The tests are `SieveAdWinDefs.lean`'s.

* `evI_win`: the term of a box of at most 13 primes whose cells lie in `[V, DEN]` and that is surely evaluable is
  evaluated (`SieveAd.EvI`): `SieveQ.box_leaf_gen` on the box's atoms, with the windows' estimates
  (`SieveLeaves.TL_spec`, `TR_spec`).
* `evJ_win`: the terms at the floor `x^{V/DEN}` of a box of at most 13 primes whose cells lie in `[V, DEN]` and that
  the bilinear rule passes are evaluated (`SieveAd.EvJ`): `SieveQ.P6IB_box` on the box's atoms.
* `winTests_sound`: so the window's tests are sound (`SieveAd.Tests.Sound`), and `SieveAd.linnik_tree` applies to a
  tree that passes them.

The file imports `SieveAdSpec.lean` and `SieveAdWinDefs.lean`.
-/
import SieveAdSpec
import SieveAdWinDefs

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN V surelyEval ibOK DEN_pos')

theorem cellsIn_iff (lo : ℕ) (bl : List Cell) :
    cellsIn lo bl = true ↔ ∀ c ∈ bl, lo ≤ c.1 ∧ c.1 ≤ DEN ∧ c.2 ≤ DEN := by
  induction bl with
  | nil => simp [cellsIn]
  | cons x bl ih => simp [cellsIn, ih, Nat.ble_eq, and_assoc]

variable [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits]

omit [RouteOK] [SieveCert.GridOK] [Fits] in
/-- The floor: `⌈q^{a₀}⌉ = ⌈x^{V/DEN}⌉`. -/
theorem z₀_eq (q : ℕ) : ⌈(q : ℝ) ^ a0⌉₊ = ⌈xq q ^ ((V : ℝ) / DEN)⌉₊ := by
  unfold a0
  rw [xpow]

omit [RouteOK] [SieveCert.GridOK] [Fits] in
/-- A prime of a box whose cells start at `V` or above is at least the floor. -/
theorem floor_le {q : ℕ} (hx : 1 ≤ xq q) {k : ℕ} {bx : Fin k → Cell} {rt : Fin k → ℕ} (hV : ∀ i, V ≤ (bx i).1)
    (hc : ∀ i, xq q ^ (((bx i).1 : ℝ) / DEN) ≤ rt i ∧ (rt i : ℝ) < xq q ^ (((bx i).2 : ℝ) / DEN)) (i : Fin k) :
    ⌈(q : ℝ) ^ a0⌉₊ ≤ rt i := by
  rw [z₀_eq]
  exact Nat.ceil_le.2 ((pow_mono hx (hV i)).trans (hc i).1)

/-- **A box surely evaluable, under more atoms.** The term of a box with cells in `[V, DEN]` that is surely
evaluable is evaluated under `m` more atoms, uniformly in the atoms, when the box's atoms and those are at most
`40`. -/
theorem evI_winE (hII : TypeIIAt) {k' : ℕ} (bx : Fin (k' + 1) → Cell)
    (hb : ∀ i, V ≤ (bx i).1 ∧ (bx i).1 ≤ DEN ∧ (bx i).2 ≤ DEN) (hsE : surelyEval (List.ofFn bx) = true) {m : ℕ}
    (hm : 3 * (k' + 1) + m ≤ 40) :
    ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a → ∀ E : List (Atom (k' + 1)), E.length ≤ m →
      ThrOK q E → |dIP q a bx (fun rt => ∀ A ∈ E, A.sem rt)| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q) := by
  intro η hη
  obtain ⟨d1, hd1, q1, h1⟩ := TL_spec a0 hII a0_pos k'
  obtain ⟨d2, hd2, q2, h2⟩ := TR_spec a0 hII a0_pos k'
  have hd : 0 < min d1 d2 := lt_min hd1 hd2
  filter_upwards [largeQ_ev, le_Xq hd hη, eventually_ge_atTop q1, eventually_ge_atTop q2] with q hL hX hq1 hq2 a ha
    E hEl hEt
  have hq3 := hL.q3
  have : NeZero q := ⟨by omega⟩
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hx1 : 1 ≤ xq q := Real.one_le_rpow hq1' L_pos.le
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hm1 : (q : ℝ) ^ (L - d1) ≤ (q : ℝ) ^ (L - min d1 d2) :=
    Real.rpow_le_rpow_of_exponent_le hq1' (by linarith [min_le_left d1 d2])
  have hm2 : (q : ℝ) ^ (L - d2) ≤ (q : ℝ) ^ (L - min d1 d2) :=
    Real.rpow_le_rpow_of_exponent_le hq1' (by linarith [min_le_right d1 d2])
  have hTL : TLat q a k' ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - min d1 d2)) :=
    fun spec S P₁ P₂ hlen hthr hP₁ hP₂ hreg =>
      (h1 q hq1 a ha spec S P₁ P₂ hlen hthr hP₁ hP₂ hreg).trans (mul_le_mul_of_nonneg_left hm1 hφ)
  have hTR : TRat q a k' ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - min d1 d2)) :=
    fun spec U W₀ W₁ hlen hthr hreg hW₁ hP₁ hP₂ =>
      (h2 q hq2 a ha spec U W₀ W₁ hlen hthr hreg hW₁ hP₁ hP₂).trans (mul_le_mul_of_nonneg_left hm2 hφ)
  have hmain := box_leaf_gen hL hTL hTR (spec := specB q bx ++ E)
    (by rw [List.length_append]; have := specB_length q bx; omega)
    (thrOK_append (thrOK_specB (by omega) L_pos.le bx fun i => ⟨(hb i).2.1, (hb i).2.2⟩) hEt) bx
    (fun rt _ hs => by
      obtain ⟨hsa, hc⟩ := (sem_specB q bx rt).1 fun A hA => hs A (List.mem_append_left _ hA)
      exact ⟨hsa, fun i => floor_le hx1 (fun i => (hb i).1) hc i, hc⟩) hsE
  rw [dIP_eq_famSet]
  exact hmain.trans (mul_le_mul_of_nonneg_left hX hφ)

/-- **A box surely evaluable.** The term of a box of at most 13 primes, with cells in `[V, DEN]`, that is surely
evaluable is evaluated. -/
theorem evI_win (hII : TypeIIAt) {k' : ℕ} (bx : Fin (k' + 1) → Cell) (hk : k' + 1 ≤ 13)
    (hb : ∀ i, V ≤ (bx i).1 ∧ (bx i).1 ≤ DEN ∧ (bx i).2 ≤ DEN) (hsE : surelyEval (List.ofFn bx) = true) :
    EvI bx := by
  intro η hη
  filter_upwards [evI_winE hII bx hb hsE (m := 0) (by omega) η hη] with q hq a ha
  have h := hq a ha [] le_rfl (thrOK_nil q)
  rwa [dIP_nil] at h

/-- **A box that the bilinear rule passes, under more atoms.** The terms at the floor `x^{V/DEN}` of a box with
cells in `[V, DEN]` that `ibOK` passes are evaluated under `m` more atoms, uniformly in the atoms, when the box's
atoms and those are at most `40`. -/
theorem evJ_winE [SieveCert.IBPar] [IBFits] (hII : TypeIIAt) {k : ℕ} (bx : Fin k → Cell)
    (hb : ∀ i, V ≤ (bx i).1 ∧ (bx i).1 ≤ DEN ∧ (bx i).2 ≤ DEN) (hib : ibOK (List.ofFn bx) = true) {m : ℕ}
    (hm : 3 * k + m ≤ 40) :
    ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a → ∀ E : List (Atom k), E.length ≤ m →
      ThrOK q E → |dJP q a V bx (fun rt => ∀ A ∈ E, A.sem rt)| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q) := by
  intro η hη
  have hL0 : 0 < L := L_pos
  obtain ⟨δ, hδ, q₀, h⟩ := P6IB_box hII bx hib (η := η / (2 * L)) (by positivity)
  filter_upwards [largeQ_ev, le_Xq hδ (half_pos hη), eventually_ge_atTop q₀] with q hL hX hq a ha E hEl hEt
  have hq3 := hL.q3
  have : NeZero q := ⟨by omega⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hx1 : 1 ≤ xq q := Real.one_le_rpow hq1' hL0.le
  have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (show 0 < q by omega)
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hmain := h q hq a ha (specB q bx ++ E) (by rw [List.length_append]; have := specB_length q bx; omega)
    (thrOK_append (thrOK_specB (by omega) hL0.le bx fun i => ⟨(hb i).2.1, (hb i).2.2⟩) hEt)
    (fun rt _ hs => by
      obtain ⟨hsa, hc⟩ := (sem_specB q bx rt).1 fun A hA => hs A (List.mem_append_left _ hA)
      exact ⟨hsa, fun i => floor_le hx1 (fun i => (hb i).1) hc i, hc⟩)
  rw [dJP_eq_famSet, ← z₀_eq]
  refine hmain.trans ?_
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hlogx : Real.log ((q : ℝ) ^ L) = L * Real.log q := Real.log_rpow hq0 _
  have e1 : η / (2 * L) * (q : ℝ) ^ L / (q.totient * Real.log q) = (q.totient : ℝ)⁻¹ * (η / 2 * Xq q) := by
    unfold Xq
    rw [hlogx]
    field_simp
  have e2 : (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) ≤ (q.totient : ℝ)⁻¹ * (η / 2 * Xq q) :=
    mul_le_mul_of_nonneg_left hX hφ
  unfold Err
  rw [e1]
  have e3 : (q.totient : ℝ)⁻¹ * (η * Xq q) =
      (q.totient : ℝ)⁻¹ * (η / 2 * Xq q) + (q.totient : ℝ)⁻¹ * (η / 2 * Xq q) := by ring
  linarith

/-- **A box that the bilinear rule passes.** The terms at the floor `x^{V/DEN}` of a box of at most 13 primes, with
cells in `[V, DEN]`, that `ibOK` passes are evaluated. -/
theorem evJ_win [SieveCert.IBPar] [IBFits] (hII : TypeIIAt) {k : ℕ} (bx : Fin k → Cell) (hk : k ≤ 13)
    (hb : ∀ i, V ≤ (bx i).1 ∧ (bx i).1 ≤ DEN ∧ (bx i).2 ≤ DEN) (hib : ibOK (List.ofFn bx) = true) :
    EvJ V bx := by
  intro η hη
  filter_upwards [evJ_winE hII bx hb hib (m := 0) (by omega) η hη] with q hq a ha
  have h := hq a ha [] le_rfl (thrOK_nil q)
  rwa [dJP_nil] at h

/-- **The window's tests are sound.** -/
theorem winTests_sound [SieveCert.IBPar] [IBFits] (hII : TypeIIAt) : (winTests).Sound := by
  refine ⟨fun bl cfg k' h hok => ?_, fun bl f cfg k h hok => ?_⟩
  · simp only [winTests, okIW, Bool.and_eq_true, Nat.ble_eq] at hok
    obtain ⟨⟨hlen, hcells⟩, hsE⟩ := hok
    have hc := (cellsIn_iff V bl).1 hcells
    exact evI_win hII _ (by omega) (fun i => hc _ (boxFn_mem bl _ h i)) (by rw [ofFn_boxFn]; exact hsE)
  · simp only [winTests, okJW, Bool.and_eq_true, Nat.ble_eq] at hok
    obtain ⟨⟨⟨hf, hlen⟩, hcells⟩, hib⟩ := hok
    have hfV : f = V := Nat.eq_of_beq_eq_true hf
    subst hfV
    have hc := (cellsIn_iff V bl).1 hcells
    exact evJ_win hII _ (by omega) (fun i => hc _ (boxFn_mem bl _ h i)) (by rw [ofFn_boxFn]; exact hib)

/-- **The window's tests are sound under two more atoms**, on the boxes of at most twelve primes. -/
theorem winTests_soundX [SieveCert.IBPar] [IBFits] (hII : TypeIIAt) : (winTests).SoundX := by
  refine ⟨fun bl cfg k' h hk hok => ?_, fun bl f cfg k h hk hok => ?_⟩
  · simp only [winTests, okIW, Bool.and_eq_true, Nat.ble_eq] at hok
    obtain ⟨⟨hlen, hcells⟩, hsE⟩ := hok
    have hc := (cellsIn_iff V bl).1 hcells
    exact evI_winE hII _ (fun i => hc _ (boxFn_mem bl _ h i)) (by rw [ofFn_boxFn]; exact hsE) (m := 2) (by omega)
  · simp only [winTests, okJW, Bool.and_eq_true, Nat.ble_eq] at hok
    obtain ⟨⟨⟨hf, hlen⟩, hcells⟩, hib⟩ := hok
    have hfV : f = V := Nat.eq_of_beq_eq_true hf
    subst hfV
    have hc := (cellsIn_iff V bl).1 hcells
    exact evJ_winE hII _ (fun i => hc _ (boxFn_mem bl _ h i)) (by rw [ofFn_boxFn]; exact hib) (m := 2) (by omega)

end SieveAd
