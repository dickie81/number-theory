/-
# The comparison with the rest among the tree's primes, on the sums of a box

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveAd.evJ_fillE` (`SieveAdFill.lean`) evaluates the terms at a floor of a box that passes the test `chkJ3`,
which reads the box through sums over sets of its primes given by the bits of their positions in a list. Here the
same statement is made for a box as a function and sets of its indices, with numbers that bound the sums
(`SieveAd.coreJ3`, `SieveAdCoreDefs.lean`): for the boxes that the tuples of a reversed term fall into, which are
not the boxes of the search's lists.

* `evJ_fill_core`: for a box `bx` with `f ≤ lo ≤ hi ≤ DEN`, sets `S₀`, `S₁` of its indices (where the leaves are cut
  in three, by `SieveAd.evJ_fill_core3`), and numbers
  `c0lo ≤ Σ_{S₀} lo`, `c0hi ≥ Σ_{S₀} hi`, `h1s ≥ Σ_{S₁} hi`, `h2s ≥ Σ_{S₁ᶜ} hi` that pass `coreJ3` at the floor
  `f`: the terms of the box at the floor `x^{f/DEN}` are evaluated under `m` more atoms, uniformly in the atoms,
  for any number `k` of primes.

* `evJ_two_core`: the same for the comparison with the rest among the box's primes (`SieveAd.evJ_twoE`,
  `SieveAd.coreJ2`), with a set `Sr ≠ ∅` of indices for the rest, disjoint from `S₀`, and numbers `ρ₁ ≤ Σ_{Sr} lo`,
  `ρ₂ ≥ Σ_{Sr} hi`; where the leaves are cut in three, by `SieveAd.evJ_two_core3`.

* `evJ_fill_core_at`, `evJ_two_core_at`: the two with the route and its exponent as variables.

The proofs are `evJ_fillE`'s and `evJ_twoE`'s, with the sums bounded in place of computed.

The file imports `SieveAdFill.lean` and `SieveAdCoreDefs.lean`.
-/
import SieveAdFill
import SieveAdCoreDefs

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRoute SieveChain SieveFamily

namespace SieveAd

open Classical
open SieveCert (DEN DEN_pos')

variable [Route] [RouteOK] [SieveCert.IBPar] [IBFits]

open SieveCert.IBPar (Lnum Lden)

set_option maxHeartbeats 1600000 in
/-- **The comparison with the rest among the tree's primes, on the sums of a box, under more atoms.** For a box
`bx` with `f ≤ lo ≤ hi ≤ DEN`, sets `S₀`, `S₁` of its indices and numbers that bound their sums and pass `coreJ3`
at the floor `f`: the terms of the box at the floor `x^{f/DEN}` are evaluated under `m` more atoms, uniformly in
the atoms, when the box's `3k` atoms and those are at most `J₀`. -/
theorem evJ_fill_core {k : ℕ} (bx : Fin k → Cell) (f : ℕ) (S₀ S₁ : Finset (Fin k)) (e : Bool)
    (u v t r1 r2 c0lo c0hi h1s h2s : ℕ) (hok : coreJ3 f e u v t r1 r2 c0lo c0hi h1s h2s = true)
    (hbxc : ∀ i, f ≤ (bx i).1 ∧ (bx i).1 ≤ (bx i).2 ∧ (bx i).2 ≤ DEN)
    (h0lo : c0lo ≤ ∑ i ∈ S₀, (bx i).1) (h0hi : ∑ i ∈ S₀, (bx i).2 ≤ c0hi) (h1 : ∑ i ∈ S₁, (bx i).2 ≤ h1s)
    (h2 : ∑ i ∈ S₁ᶜ, (bx i).2 ≤ h2s) {m J₀ : ℕ} (hm : 3 * k + m ≤ J₀) :
    ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a → ∀ E : List (Atom k), E.length ≤ m →
      ThrOK q E → |dJP q a f bx (fun rt => ∀ A ∈ E, A.sem rt)| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q) := by
  simp only [coreJ3, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hf0, z1⟩, z2⟩, z3⟩, z4⟩, z5⟩, z6⟩, q1⟩, p1⟩, p2⟩, p3⟩, hlv⟩ := hok
  -- the leaves cut in three
  rcases hlv with hlv | hE
  swap
  · exact evJ_fill_core3 bx f S₀ S₁ e u v t r1 r2 c0lo c0hi h1s h2s hf0 z1 z2 z3 z4 z5 z6 q1 p1 p2 p3 hE hbxc h0lo
      h0hi h1 h2 hm
  simp only [leavesL, Bool.and_eq_true, Nat.blt_eq, Nat.mul_eq, Nat.add_eq] at hlv
  obtain ⟨⟨p4, p5⟩, p6⟩ := hlv
  set D₁ := h1s + cond e (t + r2) 0 with hD₁def
  set D₂ := h2s + cond e 0 (t + r2) with hD₂def
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
  have hk1 : κ * (h1s : ℝ) + (if e then κ * (t : ℝ) + κ * (r2 : ℝ) else 0) = κ * (D₁ : ℝ) := by
    rw [hD₁def]
    cases e <;> simp [mul_add]
  have hk2 : κ * (h2s : ℝ) + (if e then 0 else κ * (t : ℝ) + κ * (r2 : ℝ)) = κ * (D₂ : ℝ) := by
    rw [hD₂def]
    cases e <;> simp [mul_add]
  have hX : ∑ i ∈ S₁, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) + κ * (r2 : ℝ) else 0) ≤ κ * (D₁ : ℝ) := by
    linarith
  have hY : ∑ i ∈ S₁ᶜ, κ * ((bx i).2 : ℝ) + (if e then 0 else κ * (t : ℝ) + κ * (r2 : ℝ)) ≤ κ * (D₂ : ℝ) := by
    linarith
  have hD₁ : ∑ i ∈ S₁, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) + κ * (r2 : ℝ) else 0) < L - 1 := by
    linarith
  have hD₂ : max (∑ i ∈ S₁, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) + κ * (r2 : ℝ) else 0)) 1 +
      (∑ i ∈ S₁, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) + κ * (r2 : ℝ) else 0)) +
        2 * (∑ i ∈ S₁ᶜ, κ * ((bx i).2 : ℝ) + (if e then 0 else κ * (t : ℝ) + κ * (r2 : ℝ))) <
          2 * L - 1 := by
    have hmax : max (∑ i ∈ S₁, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) + κ * (r2 : ℝ) else 0)) 1 ≤
        max (κ * (D₁ : ℝ)) 1 := max_le_max hX le_rfl
    rcases le_total (κ * (D₁ : ℝ)) 1 with hle | hle
    · rw [max_eq_right hle] at hmax
      linarith
    · rw [max_eq_left hle] at hmax
      linarith
  intro η hη
  obtain ⟨δ, hδ, q₀, hq₀⟩ := SieveFillComp.prop6_fill_at two_lt_L L_le (SieveFamilyTwo.typeIITwoAt_hx L) k J₀
    (Λ₁ := L + 1) (a₀ := κ * (f : ℝ)) (by linarith) (mul_pos hκ (by exact_mod_cast hf0))
    (fun i => κ * ((bx i).1 : ℝ)) (fun i => κ * ((bx i).2 : ℝ)) S₀ S₁ e
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

set_option maxHeartbeats 1600000 in
/-- **The comparison in two variables on the sums of a box, under more atoms.** For a box `bx` with
`f ≤ lo ≤ hi ≤ DEN`, disjoint sets `S₀`, `Sr ≠ ∅` and a set `S₁` of its indices, and numbers that bound their sums
and pass `coreJ2` at the floor `f`: the terms of the box at the floor `x^{f/DEN}` are evaluated under `m` more
atoms, uniformly in the atoms, when the box's `3k` atoms and those are at most `J₀`. -/
theorem evJ_two_core {k : ℕ} (bx : Fin k → Cell) (f : ℕ) (S₀ Sr S₁ : Finset (Fin k)) (hdisj : Disjoint S₀ Sr)
    (hSr : Sr.Nonempty) (e : Bool) (u v t ρ₁ ρ₂ c0lo c0hi h1s h2s : ℕ)
    (hok : coreJ2 f e u v t ρ₁ ρ₂ c0lo c0hi h1s h2s = true)
    (hbxc : ∀ i, f ≤ (bx i).1 ∧ (bx i).1 ≤ (bx i).2 ∧ (bx i).2 ≤ DEN)
    (hrlo : ρ₁ ≤ ∑ i ∈ Sr, (bx i).1) (hrhi : ∑ i ∈ Sr, (bx i).2 ≤ ρ₂)
    (h0lo : c0lo ≤ ∑ i ∈ S₀, (bx i).1) (h0hi : ∑ i ∈ S₀, (bx i).2 ≤ c0hi) (h1 : ∑ i ∈ S₁, (bx i).2 ≤ h1s)
    (h2 : ∑ i ∈ S₁ᶜ, (bx i).2 ≤ h2s) {m J₀ : ℕ} (hm : 3 * k + m ≤ J₀) :
    ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a → ∀ E : List (Atom k), E.length ≤ m →
      ThrOK q E → |dJP q a f bx (fun rt => ∀ A ∈ E, A.sem rt)| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q) := by
  simp only [coreJ2, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hf0, z1⟩, z2⟩, z3⟩, z4⟩, z5⟩, z6⟩, p1⟩, p2⟩, p3⟩, hlv⟩ := hok
  -- the leaves cut in three
  rcases hlv with hlv | hE
  swap
  · exact evJ_two_core3 bx f S₀ Sr S₁ hdisj hSr e u v t ρ₁ ρ₂ c0lo c0hi h1s h2s hf0 z1 z2 z3 z4 z5 z6 p1 p2 p3 hE hbxc
      hrlo hrhi h0lo h0hi h1 h2 hm
  simp only [leavesL, Bool.and_eq_true, Nat.blt_eq, Nat.mul_eq, Nat.add_eq] at hlv
  obtain ⟨⟨p4, p5⟩, p6⟩ := hlv
  set D₁ := h1s + cond e t 0 with hD₁def
  set D₂ := h2s + cond e 0 t with hD₂def
  have hρ12 : ρ₁ ≤ ρ₂ := hrlo.trans ((Finset.sum_le_sum fun i _ => (hbxc i).2.1).trans hrhi)
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
  -- the conditions of the comparison
  have hu : 0 < κ * (u : ℝ) := by linarith
  have huv : κ * (u : ℝ) + κ * (f : ℝ) < κ * (v : ℝ) := by
    have := mul_lt_mul_of_pos_left (castlt p1) hκ
    push_cast at this
    linarith
  have hρ₁0 : 0 ≤ κ * (ρ₁ : ℝ) := by positivity
  have hρ : κ * (ρ₁ : ℝ) ≤ κ * (ρ₂ : ℝ) := mul_le_mul_of_nonneg_left (cast hρ12) hκ.le
  have hvρ : κ * (v : ℝ) + κ * (ρ₂ : ℝ) < L := by linarith
  have hρlo : κ * (ρ₁ : ℝ) ≤ ∑ i ∈ Sr, κ * ((bx i).1 : ℝ) := by
    rw [← Finset.mul_sum, ← Nat.cast_sum]
    exact mul_le_mul_of_nonneg_left (cast hrlo) hκ.le
  have hρhi : ∑ i ∈ Sr, κ * ((bx i).2 : ℝ) ≤ κ * (ρ₂ : ℝ) := by
    rw [← Finset.mul_sum, ← Nat.cast_sum]
    exact mul_le_mul_of_nonneg_left (cast hrhi) hκ.le
  have hzone : ∀ m₁ m₂ : ℝ, κ * (u : ℝ) ≤ m₁ → m₁ ≤ κ * (v : ℝ) → L - κ * (ρ₂ : ℝ) - κ ≤ m₁ + m₂ →
      m₁ + m₂ ≤ L - κ * (ρ₁ : ℝ) + κ → SieveTwoZone7D.Zone7d L m₁ m₂ := by
    intro m₁ m₂ h1 h2 h3 h4
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have hlo : κ * (u : ℝ) - ∑ i ∈ S₀, κ * ((bx i).1 : ℝ) ≤ κ * (t : ℝ) := by
    have := mul_le_mul_of_nonneg_left (cast p2) hκ.le
    push_cast at this
    linarith
  have hhi : ∑ i ∈ S₀, κ * ((bx i).2 : ℝ) < κ * (v : ℝ) :=
    lt_of_le_of_lt hs0hi (mul_lt_mul_of_pos_left (castlt p3) hκ)
  have hk1 : κ * (h1s : ℝ) + (if e then κ * (t : ℝ) else 0) = κ * (D₁ : ℝ) := by
    rw [hD₁def]
    cases e <;> simp [mul_add]
  have hk2 : κ * (h2s : ℝ) + (if e then 0 else κ * (t : ℝ)) = κ * (D₂ : ℝ) := by
    rw [hD₂def]
    cases e <;> simp [mul_add]
  have hX : ∑ i ∈ S₁, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) else 0) ≤ κ * (D₁ : ℝ) := by linarith
  have hY : ∑ i ∈ S₁ᶜ, κ * ((bx i).2 : ℝ) + (if e then 0 else κ * (t : ℝ)) ≤ κ * (D₂ : ℝ) := by linarith
  have hD₁ : ∑ i ∈ S₁, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) else 0) < L - 1 := by linarith
  have hD₂ : max (∑ i ∈ S₁, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) else 0)) 1 +
      (∑ i ∈ S₁, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) else 0)) +
        2 * (∑ i ∈ S₁ᶜ, κ * ((bx i).2 : ℝ) + (if e then 0 else κ * (t : ℝ))) < 2 * L - 1 := by
    have hmax : max (∑ i ∈ S₁, κ * ((bx i).2 : ℝ) + (if e then κ * (t : ℝ) else 0)) 1 ≤ max (κ * (D₁ : ℝ)) 1 :=
      max_le_max hX le_rfl
    rcases le_total (κ * (D₁ : ℝ)) 1 with hle | hle
    · rw [max_eq_right hle] at hmax
      linarith
    · rw [max_eq_left hle] at hmax
      linarith
  intro η hη
  obtain ⟨δ, hδ, q₀, hq₀⟩ := SieveTwoComp.prop6_two_at two_lt_L L_le (SieveFamilyTwo.typeIITwoAt_hx L) k J₀
    (Λ₁ := L + 1) (a₀ := κ * (f : ℝ)) (by linarith) (mul_pos hκ (by exact_mod_cast hf0))
    (fun i => κ * ((bx i).1 : ℝ)) (fun i => κ * ((bx i).2 : ℝ)) S₀ Sr S₁ hdisj hSr e
    hu huv hρ₁0 hρ hvρ hρlo hρhi hκ hzone hlo hhi hD₁ hD₂ (η := η / (2 * L)) (by positivity)
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

omit [Route] [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- **The comparison with the rest among the tree's primes, on the sums of a box, for any route**:
`evJ_fill_core` with the route and its exponent as variables. -/
theorem evJ_fill_core_at (Rt : Route) (hRt : @RouteOK Rt) (Pr : SieveCert.IBPar) (hPr : @IBFits Rt Pr) {k : ℕ}
    (bx : Fin k → Cell) (f : ℕ) (S₀ S₁ : Finset (Fin k)) (e : Bool) (u v t r1 r2 c0lo c0hi h1s h2s : ℕ)
    (hok : @coreJ3 Pr f e u v t r1 r2 c0lo c0hi h1s h2s = true)
    (hbxc : ∀ i, f ≤ (bx i).1 ∧ (bx i).1 ≤ (bx i).2 ∧ (bx i).2 ≤ DEN)
    (h0lo : c0lo ≤ ∑ i ∈ S₀, (bx i).1) (h0hi : ∑ i ∈ S₀, (bx i).2 ≤ c0hi) (h1 : ∑ i ∈ S₁, (bx i).2 ≤ h1s)
    (h2 : ∑ i ∈ S₁ᶜ, (bx i).2 ≤ h2s) {m J₀ : ℕ} (hm : 3 * k + m ≤ J₀) :
    ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a → ∀ E : List (Atom k), E.length ≤ m →
      @ThrOK Rt q k E →
        |@dJP Rt q a f k bx (fun rt => ∀ A ∈ E, A.sem rt)| ≤ (q.totient : ℝ)⁻¹ * (η * @Xq Rt q) :=
  @evJ_fill_core Rt hRt Pr hPr k bx f S₀ S₁ e u v t r1 r2 c0lo c0hi h1s h2s hok hbxc h0lo h0hi h1 h2 m J₀ hm

omit [Route] [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- **The comparison in two variables on the sums of a box, for any route**: `evJ_two_core` with the route and its
exponent as variables. -/
theorem evJ_two_core_at (Rt : Route) (hRt : @RouteOK Rt) (Pr : SieveCert.IBPar) (hPr : @IBFits Rt Pr) {k : ℕ}
    (bx : Fin k → Cell) (f : ℕ) (S₀ Sr S₁ : Finset (Fin k)) (hdisj : Disjoint S₀ Sr) (hSr : Sr.Nonempty) (e : Bool)
    (u v t ρ₁ ρ₂ c0lo c0hi h1s h2s : ℕ) (hok : @coreJ2 Pr f e u v t ρ₁ ρ₂ c0lo c0hi h1s h2s = true)
    (hbxc : ∀ i, f ≤ (bx i).1 ∧ (bx i).1 ≤ (bx i).2 ∧ (bx i).2 ≤ DEN)
    (hrlo : ρ₁ ≤ ∑ i ∈ Sr, (bx i).1) (hrhi : ∑ i ∈ Sr, (bx i).2 ≤ ρ₂)
    (h0lo : c0lo ≤ ∑ i ∈ S₀, (bx i).1) (h0hi : ∑ i ∈ S₀, (bx i).2 ≤ c0hi) (h1 : ∑ i ∈ S₁, (bx i).2 ≤ h1s)
    (h2 : ∑ i ∈ S₁ᶜ, (bx i).2 ≤ h2s) {m J₀ : ℕ} (hm : 3 * k + m ≤ J₀) :
    ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a → ∀ E : List (Atom k), E.length ≤ m →
      @ThrOK Rt q k E →
        |@dJP Rt q a f k bx (fun rt => ∀ A ∈ E, A.sem rt)| ≤ (q.totient : ℝ)⁻¹ * (η * @Xq Rt q) :=
  @evJ_two_core Rt hRt Pr hPr k bx f S₀ Sr S₁ hdisj hSr e u v t ρ₁ ρ₂ c0lo c0hi h1s h2s hok hbxc hrlo hrhi h0lo h0hi
    h1 h2 m J₀ hm

end SieveAd

#print axioms SieveAd.evJ_fill_core_at
#print axioms SieveAd.evJ_two_core_at
