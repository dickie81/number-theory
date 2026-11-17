/-
# The number of primes that a bound of the first term gives, and every `x ≥ K·q^L`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. For a route (`x = q^L`) and a bound `C < 1` of the first term, `SieveAd.linnik_large_bd` proves
`S(𝒜, z_top) ≥ φ(q)⁻¹·(1 − C)/2·x/log x` for large `q`, and keeps one prime of it. Here the number is kept, and
carried from `x = q^L` to every `x ≥ K·q^L`.

* `count_of_large` (no route): let `L > 0` and `c₀ ≥ 0`. If for every large modulus `Q` each unit class mod `Q` has
  at least `φ(Q)⁻¹·c₀·Q^L/log Q^L` primes in `(Q^L, 2Q^L]`, then there is `K` such that for every `q ≥ 1`, every `a`
  prime to `q` and every `x ≥ K·q^L` the primes `p ≤ x` with `p ≡ a (mod q)` number at least
  `φ(q)⁻¹·c₀/2^{L+1}·x/log x`. The moduli are the multiples of `q`: for `Q = qm` with `x/2^{L+1} ≤ Q^L ≤ x/2`, the
  `φ(Q)/φ(q)` unit classes mod `Q` above `a` have their primes of `(Q^L, 2Q^L]` below `x`, in the class of `a` mod
  `q`, and apart. That every modulus and every class is allowed is what the step uses.
* `count_large_bd`: for a route with `RouteOK`, if the terms at the floor of the box with no prime are evaluated and
  the term of the box of one prime with the cell `(f₀, DEN/2 + 1)` is bounded at `C < 1`, then for large `q` and
  every unit `a` mod `q` the primes `p ≡ a (mod q)` with `q^L < p ≤ 2q^L` number at least
  `φ(q)⁻¹·(1 − C)/2·q^L/log q^L`. The proof is `linnik_large_bd`'s, with its last step counting.
* `count_bd`, `count_pr`: the two together, from a bound of the first term and from a search's cost `c < K`: for
  every `q ≥ 1`, every `a` prime to `q` and every `x ≥ K'·q^L`, at least `φ(q)⁻¹·(1 − C)/2^{L+2}·x/log x` primes
  `p ≤ x` with `p ≡ a (mod q)`. `count_large_pr`: `count_large_bd` from a search's cost, for `a` prime to `q`.

The file imports `SieveAdRevSearch.lean`.
-/
import SieveAdRevSearch

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K DEN_pos' K_pos')

/-! ### Every `x ≥ K·q^L`, from the count at `Q^L` for every large modulus -/

/-- The unit classes mod `Q` above a unit class mod `q`, for `q ∣ Q`: there are `φ(Q)/φ(q)` of them. -/
theorem card_units_above {q Q : ℕ} [NeZero q] [NeZero Q] (hd : q ∣ Q) (u₀ : (ZMod q)ˣ) :
    (univ.filter fun v : (ZMod Q)ˣ => ZMod.unitsMap hd v = u₀).card * q.totient = Q.totient := by
  have hsurj := ZMod.unitsMap_surjective hd
  have hfib : ∀ u : (ZMod q)ˣ, (univ.filter fun v : (ZMod Q)ˣ => ZMod.unitsMap hd v = u).card =
      (univ.filter fun v : (ZMod Q)ˣ => ZMod.unitsMap hd v = u₀).card := fun u =>
    MonoidHom.card_fiber_eq_of_mem_range (ZMod.unitsMap hd) (hsurj u) (hsurj u₀)
  have hsum : (univ : Finset (ZMod Q)ˣ).card =
      ∑ u : (ZMod q)ˣ, (univ.filter fun v : (ZMod Q)ˣ => ZMod.unitsMap hd v = u).card :=
    Finset.card_eq_sum_card_fiberwise (f := ZMod.unitsMap hd) (s := univ) (t := univ) fun _ _ => Finset.mem_coe.2
      (Finset.mem_univ _)
  rw [Finset.sum_congr rfl fun u _ => hfib u, Finset.sum_const, Finset.card_univ, Finset.card_univ,
    ZMod.card_units_eq_totient, ZMod.card_units_eq_totient, smul_eq_mul] at hsum
  rw [hsum, mul_comm]

/-- **Every `x ≥ K·q^L`, from the count at `Q^L` for every large modulus.** Let `L > 0` and `c₀ ≥ 0`. If for every
large modulus `Q` each unit class mod `Q` has at least `φ(Q)⁻¹·c₀·Q^L/log Q^L` primes in `(Q^L, 2Q^L]`, then there is
`K'` such that for every `q ≥ 1`, every `a` prime to `q` and every `x ≥ K'·q^L` the primes `p ≤ x` with
`p ≡ a (mod q)` number at least `φ(q)⁻¹·c₀/2^{L+1}·x/log x`. -/
theorem count_of_large {L : ℝ} (hL : 0 < L) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hlarge : ∃ q₀ : ℕ, ∀ (Q : ℕ) [NeZero Q], q₀ ≤ Q → ∀ b : ZMod Q, IsUnit b →
      (Q.totient : ℝ)⁻¹ * (c₀ * ((Q : ℝ) ^ L / Real.log ((Q : ℝ) ^ L))) ≤
        (((Ioc ⌊(Q : ℝ) ^ L⌋₊ ⌊2 * (Q : ℝ) ^ L⌋₊).filter fun p : ℕ => p.Prime ∧ (p : ZMod Q) = b).card : ℝ)) :
    ∃ K' : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q → ∀ x : ℝ, K' * (q : ℝ) ^ L ≤ x →
      (q.totient : ℝ)⁻¹ * (c₀ / 2 ^ (L + 1) * (x / Real.log x)) ≤
        (((Finset.range (⌊x⌋₊ + 1)).filter fun p : ℕ => p.Prime ∧ p ≡ a [MOD q]).card : ℝ) := by
  obtain ⟨q₀, hq₀⟩ := hlarge
  refine ⟨max (2 ^ (L + 2)) (2 * (2 * (q₀ : ℝ)) ^ L), fun q _ a ha x hx => ?_⟩
  have hLne : L ≠ 0 := hL.ne'
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hqL : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow hq1 hL.le
  have h2L : (0 : ℝ) < 2 ^ L := Real.rpow_pos_of_pos two_pos _
  have h2L1 : (2 : ℝ) ^ (L + 1) = 2 ^ L * 2 := Real.rpow_add_one two_ne_zero L
  have h2L2 : (2 : ℝ) ^ (L + 2) = 2 ^ L * 4 := by
    rw [show L + 2 = L + 1 + 1 by ring, Real.rpow_add_one two_ne_zero, h2L1]
    ring
  have h1L : (1 : ℝ) ≤ 2 ^ L := Real.one_le_rpow one_le_two hL.le
  -- `x` is large: `2^{L+2}q^L ≤ x` and `2(2q₀)^L ≤ x`
  have hx1 : (2 : ℝ) ^ (L + 2) * (q : ℝ) ^ L ≤ x :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hx
  have hx2 : 2 * (2 * (q₀ : ℝ)) ^ L ≤ x := by
    have h0 : (0 : ℝ) ≤ 2 * (2 * (q₀ : ℝ)) ^ L := by positivity
    calc 2 * (2 * (q₀ : ℝ)) ^ L = 2 * (2 * (q₀ : ℝ)) ^ L * 1 := (mul_one _).symm
      _ ≤ 2 * (2 * (q₀ : ℝ)) ^ L * (q : ℝ) ^ L := mul_le_mul_of_nonneg_left hqL h0
      _ ≤ max (2 ^ (L + 2)) (2 * (2 * (q₀ : ℝ)) ^ L) * (q : ℝ) ^ L :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ ≤ x := hx
  have hx4 : (2 : ℝ) ^ L * 4 ≤ x := by
    rw [h2L2] at hx1
    nlinarith
  have hx0 : 0 < x := by nlinarith
  -- `t = (x/2)^{1/L}`, with `t^L = x/2`, `2q ≤ t` and `2q₀ ≤ t`
  set t : ℝ := (x / 2) ^ L⁻¹ with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg (by positivity) _
  have htL : t ^ L = x / 2 := Real.rpow_inv_rpow (by positivity) hLne
  have hroot : ∀ y : ℝ, 0 ≤ y → y ^ L ≤ x / 2 → y ≤ t := fun y hy h => by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hy L) h (inv_nonneg.2 hL.le)
    rwa [Real.rpow_rpow_inv hy hLne] at this
  have h2q : 2 * (q : ℝ) ≤ t := by
    refine hroot _ (by positivity) ?_
    rw [Real.mul_rpow two_pos.le hq0.le]
    rw [h2L2] at hx1
    nlinarith
  have h2q₀ : 2 * (q₀ : ℝ) ≤ t := by
    refine hroot _ (by positivity) ?_
    linarith
  -- the modulus `Q = q·⌊t/q⌋`, with `t/2 ≤ Q ≤ t`
  set m : ℕ := ⌊t / q⌋₊ with hm
  have hm1 : (m : ℝ) ≤ t / q := Nat.floor_le (by positivity)
  have hm2 : t / q < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hQle : ((q * m : ℕ) : ℝ) ≤ t := by
    push_cast
    calc (q : ℝ) * m ≤ q * (t / q) := mul_le_mul_of_nonneg_left hm1 hq0.le
      _ = t := by field_simp
  have hQge : t / 2 ≤ ((q * m : ℕ) : ℝ) := by
    push_cast
    have h1 : t < (q : ℝ) * ((m : ℝ) + 1) := by
      have := mul_lt_mul_of_pos_left hm2 hq0
      rwa [mul_div_cancel₀ _ hq0.ne'] at this
    nlinarith
  set Q : ℕ := q * m with hQ
  have hQq₀ : q₀ ≤ Q := by
    have : (q₀ : ℝ) ≤ Q := by linarith
    exact_mod_cast this
  have hQ1 : 1 ≤ Q := by
    have : (1 : ℝ) ≤ Q := by linarith
    exact_mod_cast this
  have hQne : NeZero Q := ⟨by omega⟩
  have hd : q ∣ Q := Dvd.intro m rfl
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  -- `x/2^{L+1} ≤ Q^L ≤ x/2`
  have hQL1 : (Q : ℝ) ^ L ≤ x / 2 := by
    rw [← htL]
    exact Real.rpow_le_rpow hQ0 hQle hL.le
  have hQL2 : x / 2 ^ (L + 1) ≤ (Q : ℝ) ^ L := by
    have := Real.rpow_le_rpow (by positivity) hQge hL.le
    rwa [Real.div_rpow ht0 two_pos.le, htL, div_div, mul_comm, ← h2L1] at this
  have hQL3 : (2 : ℝ) ≤ (Q : ℝ) ^ L := by
    refine le_trans ?_ hQL2
    rw [le_div_iff₀ (by positivity), h2L1]
    linarith
  -- the classes mod `Q` above `a`, and their primes
  set u₀ : (ZMod q)ˣ := ZMod.unitOfCoprime a ha with hu₀
  set F : Finset (ZMod Q)ˣ := univ.filter fun v : (ZMod Q)ˣ => ZMod.unitsMap hd v = u₀ with hF
  set S : ZMod Q → Finset ℕ := fun b =>
    (Ioc ⌊(Q : ℝ) ^ L⌋₊ ⌊2 * (Q : ℝ) ^ L⌋₊).filter fun p : ℕ => p.Prime ∧ (p : ZMod Q) = b with hS
  set T : Finset ℕ := (Finset.range (⌊x⌋₊ + 1)).filter fun p : ℕ => p.Prime ∧ p ≡ a [MOD q] with hT
  have hsub : F.biUnion (fun v => S (v : ZMod Q)) ⊆ T := by
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨v, hv, hpv⟩ := hp
    rw [hS, Finset.mem_filter, Finset.mem_Ioc] at hpv
    obtain ⟨⟨-, hp2⟩, hpp, hpb⟩ := hpv
    rw [hF, Finset.mem_filter] at hv
    rw [hT, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hpp, ?_⟩
    · have : ⌊2 * (Q : ℝ) ^ L⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor (by linarith)
      omega
    · rw [← ZMod.natCast_eq_natCast_iff]
      have h1 : ((p : ZMod Q).cast : ZMod q) = (p : ZMod q) := ZMod.cast_natCast hd p
      have h2 : (((v : ZMod Q)).cast : ZMod q) = ((ZMod.unitsMap hd v : (ZMod q)ˣ) : ZMod q) :=
        (ZMod.unitsMap_val hd v).symm
      rw [← h1, hpb, h2, hv.2, hu₀, ZMod.coe_unitOfCoprime]
  have hdisj : (F : Set (ZMod Q)ˣ).PairwiseDisjoint fun v => S (v : ZMod Q) := by
    intro v _ v' _ hne
    refine Finset.disjoint_left.2 fun p hp hp' => hne ?_
    rw [hS, Finset.mem_filter] at hp hp'
    exact Units.ext (hp.2.2.symm.trans hp'.2.2)
  have hcard : ∑ v ∈ F, ((S (v : ZMod Q)).card : ℝ) ≤ (T.card : ℝ) := by
    have := Finset.card_le_card hsub
    rw [Finset.card_biUnion hdisj] at this
    exact_mod_cast this
  have hφQ : (0 : ℝ) < (Q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hφq : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  have hFc : (F.card : ℝ) * (q.totient : ℝ) = (Q.totient : ℝ) := by
    exact_mod_cast card_units_above hd u₀
  -- each class has its primes
  have hterm : ∀ v ∈ F, (Q.totient : ℝ)⁻¹ * (c₀ * ((Q : ℝ) ^ L / Real.log ((Q : ℝ) ^ L))) ≤
      ((S (v : ZMod Q)).card : ℝ) := fun v _ => hq₀ Q hQq₀ (v : ZMod Q) v.isUnit
  have hsum : (F.card : ℝ) * ((Q.totient : ℝ)⁻¹ * (c₀ * ((Q : ℝ) ^ L / Real.log ((Q : ℝ) ^ L)))) ≤
      (T.card : ℝ) := by
    refine le_trans ?_ hcard
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hterm
  have hFpos : (0 : ℝ) < (F.card : ℝ) := by
    by_contra h
    have h0 : (F.card : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    rw [h0, zero_mul] at hFc
    linarith
  have hF' : (F.card : ℝ) * (Q.totient : ℝ)⁻¹ = (q.totient : ℝ)⁻¹ := by
    rw [← hFc]
    field_simp
  -- `Q^L/log Q^L ≥ (x/2^{L+1})/log x`
  have hlogQ : 0 < Real.log ((Q : ℝ) ^ L) := Real.log_pos (by linarith)
  have hlogle : Real.log ((Q : ℝ) ^ L) ≤ Real.log x := Real.log_le_log (by linarith) (by linarith)
  have hX : x / 2 ^ (L + 1) / Real.log x ≤ (Q : ℝ) ^ L / Real.log ((Q : ℝ) ^ L) :=
    le_trans (div_le_div_of_nonneg_right hQL2 (hlogQ.le.trans hlogle))
      (div_le_div_of_nonneg_left (by linarith) hlogQ hlogle)
  calc (q.totient : ℝ)⁻¹ * (c₀ / 2 ^ (L + 1) * (x / Real.log x))
      = (q.totient : ℝ)⁻¹ * (c₀ * (x / 2 ^ (L + 1) / Real.log x)) := by ring
    _ ≤ (q.totient : ℝ)⁻¹ * (c₀ * ((Q : ℝ) ^ L / Real.log ((Q : ℝ) ^ L))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX hc₀) (inv_nonneg.2 hφq.le)
    _ = (F.card : ℝ) * ((Q.totient : ℝ)⁻¹ * (c₀ * ((Q : ℝ) ^ L / Real.log ((Q : ℝ) ^ L)))) := by
      rw [← hF']
      ring
    _ ≤ (T.card : ℝ) := hsum

/-! ### The count at `x = q^L` -/

variable [Route]

/-- **The count at `x = q^L`, for large `q`, from a bound of the first term.** For a route with `RouteOK`: if the
terms at the floor `x^{f₀/DEN}` of the box with no prime are evaluated, and the term of the box of one prime with the
cell `(f₀, DEN/2 + 1)` is at most `(C + o(1))x/(φ(q) log x)` in `𝒜` minus the comparison set, with `C < 1`, then
there is `q₀` such that for `q ≥ q₀` and `a` a unit mod `q` the primes `p ≡ a (mod q)` with `q^L < p ≤ 2q^L` number
at least `φ(q)⁻¹·(1 − C)/2·q^L/log q^L`. -/
theorem count_large_bd [RouteOK] (f₀ : ℕ) (hf₀ : f₀ ≤ DEN / 2 + 1) (hJ0 : EvJ f₀ (boxFn [] 0 rfl)) {C : ℝ}
    (hC1 : C < 1) (hBd : Bd false C (boxFn [(f₀, DEN / 2 + 1)] 1 rfl)) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      (q.totient : ℝ)⁻¹ * ((1 - C) / 2 * ((q : ℝ) ^ L / Real.log ((q : ℝ) ^ L))) ≤
        (((Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊).filter fun p : ℕ => p.Prime ∧ (p : ZMod q) = a).card : ℝ) := by
  have hL0 : 0 < L := L_pos
  have hD := DEN_pos'
  set ε : ℝ := (1 - C) / 8 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hJ := hJ0 ε hε0
  have hI := hBd ε hε0
  have hlog := SieveMain.ev_log_le (c := ε / L) (r := L - 1) (by positivity) (by linarith [two_lt_L])
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 (hJ.and (hI.and ((Ttop_gB_ge hε0).and (big_ev.and hlog))))
  refine ⟨q₀, fun q _ hq a ha => ?_⟩
  obtain ⟨h1, h2, hTB, hbig, hlg⟩ := hq₀ q hq
  obtain ⟨hq2, hx3, hN1, hN2, hy3⟩ := big_facts hbig
  have hX := Xq_pos hbig
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hx0 : 0 < xq q := by linarith
  have hφ : (0 : ℝ) < (q.totient : ℝ)⁻¹ := by
    have : 0 < q.totient := Nat.totient_pos.2 (by omega)
    positivity
  have h1' := h1 a ha
  have h2' : -((q.totient : ℝ)⁻¹ * ((C + ε) * Xq q)) ≤ sg false * dI q a (boxFn [(f₀, DEN / 2 + 1)] 1 rfl) :=
    h2 a ha
  have hdiff : Ttop q (gA q a) - Ttop q (gB q) =
      dJ q a f₀ (boxFn [] 0 rfl) - dI q a (boxFn [(f₀, DEN / 2 + 1)] 1 rfl) := by
    rw [Ttop_eq hbig (gA q a) hf₀, Ttop_eq hbig (gB q) hf₀]
    unfold dJ dI
    ring
  -- `q ≤ εX`
  have hqX : (q : ℝ) ≤ ε * Xq q := by
    have hlogx : Real.log (xq q) = L * Real.log q := Real.log_rpow hq0 _
    have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
    unfold Xq
    rw [hlogx, ← mul_div_assoc, le_div_iff₀ (by positivity)]
    have h2'' : L * Real.log q ≤ ε * (q : ℝ) ^ (L - 1) := by
      have := hlg
      rw [div_mul_eq_mul_div, le_div_iff₀ hL0] at this
      linarith
    have hsplit : (q : ℝ) * (q : ℝ) ^ (L - 1) = xq q := by
      rw [← Real.rpow_one_add' hq0.le (by rw [add_sub_cancel]; exact hL0.ne'), add_sub_cancel]
    calc (q : ℝ) * (L * Real.log q) ≤ (q : ℝ) * (ε * (q : ℝ) ^ (L - 1)) := mul_le_mul_of_nonneg_left h2'' hq0.le
      _ = ε * xq q := by rw [← hsplit]; ring
  -- `S(𝒜, z_top) ≥ φ(q)⁻¹·(1 − C)/2·x/log x`
  have hge : (q.totient : ℝ)⁻¹ * ((1 - C) / 2 * Xq q) ≤ Ttop q (gA q a) := by
    have h3 := neg_abs_le_sg true (dJ q a f₀ (boxFn [] 0 rfl))
    simp only [sg, ite_true, one_mul, Bool.false_eq_true, ite_false, neg_mul] at h3 h2'
    have e1 : (q.totient : ℝ)⁻¹ * ((1 - ε) * Xq q - q) - (q.totient : ℝ)⁻¹ * (ε * Xq q) -
        (q.totient : ℝ)⁻¹ * ((C + ε) * Xq q) ≤ Ttop q (gA q a) := by linarith
    have e2 : (q.totient : ℝ)⁻¹ * ((1 - C) / 2 * Xq q) ≤ (q.totient : ℝ)⁻¹ * ((1 - ε) * Xq q - q) -
        (q.totient : ℝ)⁻¹ * (ε * Xq q) - (q.totient : ℝ)⁻¹ * ((C + ε) * Xq q) := by
      have : (1 - C) / 2 * Xq q ≤ ((1 - ε) * Xq q - q) - (ε * Xq q) - ((C + ε) * Xq q) := by
        rw [hε] at hqX ⊢
        linarith
      nlinarith
    linarith
  -- `N₂ < z_top²`
  have hz : N2 q < (ztop q) ^ 2 := by
    set y := xq q ^ (((DEN / 2 + 1 : ℕ) : ℝ) / DEN) with hy
    have hy0 : 0 ≤ y := Real.rpow_nonneg hx0.le _
    have h4 : y ≤ (ztop q : ℝ) := Nat.le_ceil _
    have h5 : xq q ^ (((DEN : ℝ) + 1) / DEN) ≤ y * y := by
      rw [hy, ← Real.rpow_add hx0]
      refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
      rw [← add_div, div_le_div_iff_of_pos_right hD]
      have : (DEN : ℝ) + 1 ≤ 2 * ((DEN / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast half_DEN.2
      linarith
    have h6 : (N2 q : ℝ) < ((ztop q) ^ 2 : ℕ) := by
      push_cast
      nlinarith
    exact_mod_cast h6
  have hN1' : 1 ≤ N1 q := Nat.le_floor (by simpa using (show (1 : ℝ) ≤ xq q by linarith))
  -- every term of `S(𝒜, z_top)` is a prime `≡ a`
  have hle : Ttop q (gA q a) ≤
      (((Ioc (N1 q) (N2 q)).filter fun p : ℕ => p.Prime ∧ (p : ZMod q) = a).card : ℝ) := by
    rw [← Finset.sum_boole]
    unfold Ttop
    refine Finset.sum_le_sum fun m hm => ?_
    rw [Finset.mem_Ioc] at hm
    by_cases hmA : (m : ZMod q) = a
    · by_cases hmr : SieveTree.rough (ztop q) m
      · have hm2 : 2 ≤ m := by omega
        have hmp : m.Prime := by
          by_contra hnp
          have hsq := Nat.minFac_sq_le_self (by omega) hnp
          have hmin := (SieveStops2.rough_iff_le_minFac hm2).1 hmr
          have : (ztop q) ^ 2 ≤ m.minFac ^ 2 := Nat.pow_le_pow_left hmin 2
          omega
        simp [gA, hmA, hmr, hmp]
      · simp only [hmr, ite_false, mul_zero]
        split_ifs <;> norm_num
    · simp [gA, hmA]
  unfold Xq at hge
  exact hge.trans hle

/-- **Every `x ≥ K'·q^L`, from a bound of the first term.** For a route with `RouteOK`, under the hypotheses of
`count_large_bd`: there is `K'` such that for every `q ≥ 1`, every `a` prime to `q` and every `x ≥ K'·q^L` the primes
`p ≤ x` with `p ≡ a (mod q)` number at least `φ(q)⁻¹·(1 − C)/2^{L+2}·x/log x`. -/
theorem count_bd [RouteOK] (f₀ : ℕ) (hf₀ : f₀ ≤ DEN / 2 + 1) (hJ0 : EvJ f₀ (boxFn [] 0 rfl)) {C : ℝ}
    (hC1 : C < 1) (hBd : Bd false C (boxFn [(f₀, DEN / 2 + 1)] 1 rfl)) :
    ∃ K' : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q → ∀ x : ℝ, K' * (q : ℝ) ^ L ≤ x →
      (q.totient : ℝ)⁻¹ * ((1 - C) / 2 / 2 ^ (L + 1) * (x / Real.log x)) ≤
        (((Finset.range (⌊x⌋₊ + 1)).filter fun p : ℕ => p.Prime ∧ p ≡ a [MOD q]).card : ℝ) :=
  count_of_large L_pos (by linarith) (count_large_bd f₀ hf₀ hJ0 hC1 hBd)

/-- **The count at `x = q^L` from a search.** For a route with `RouteOK` and sound tests: if the terms at the floor
`x^{f₀/DEN}` of the box with no prime pass `okJ`, and the term of the box of one prime with the cell
`(f₀, DEN/2 + 1)`, of the sign `−`, has a bound at a cost `c < K`, then for large `q` and every `a` prime to `q` the
primes `p ≡ a (mod q)` with `q^L < p ≤ 2q^L` number at least `(1 − c/K)/2·q^L/(φ(q) log q^L)`. -/
theorem count_large_pr [RouteOK] {τ : Tests} (hτ : τ.Sound) (f₀ : ℕ) (cfg₀ : Cfg) (hf₀ : f₀ ≤ DEN / 2 + 1)
    (hroot : τ.okJ [] f₀ cfg₀ = true) {c : ℕ} (h : PR [(f₀, DEN / 2 + 1)] false c) (hc : c < K) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ a : ℕ, a.Coprime q →
      (1 - (c : ℝ) / K) / 2 * (q : ℝ) ^ L / (q.totient * Real.log ((q : ℝ) ^ L)) ≤
        (((Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊).filter fun p : ℕ => p.Prime ∧ p ≡ a [MOD q]).card : ℝ) := by
  have hC : (c : ℝ) / K < 1 := by
    rw [div_lt_one K_pos']
    exact_mod_cast hc
  obtain ⟨q₀, hq₀⟩ := count_large_bd f₀ hf₀ (hτ.soundJ [] f₀ cfg₀ 0 rfl hroot) hC (h 0 rfl)
  refine ⟨q₀, fun q _ hq a ha => ?_⟩
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha
  have := hq₀ q hq (a : ZMod q) hu
  have hset : ((Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊).filter fun p : ℕ => p.Prime ∧ p ≡ a [MOD q]) =
      (Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊).filter fun p : ℕ => p.Prime ∧ (p : ZMod q) = (a : ZMod q) :=
    Finset.filter_congr fun p _ => by rw [ZMod.natCast_eq_natCast_iff]
  rw [hset]
  refine le_trans (le_of_eq ?_) this
  rw [div_eq_mul_inv, mul_inv]
  ring

/-- **Primes in every class, in number, from a search.** For a route with `RouteOK` and sound tests, under the
hypotheses of `count_large_pr`: there are `c' > 0` and `K'` such that for every `q ≥ 1`, every `a` prime to `q` and
every `x ≥ K'·q^L` the primes `p ≤ x` with `p ≡ a (mod q)` number at least `c'·x/(φ(q) log x)`. -/
theorem count_pr [RouteOK] {τ : Tests} (hτ : τ.Sound) (f₀ : ℕ) (cfg₀ : Cfg) (hf₀ : f₀ ≤ DEN / 2 + 1)
    (hroot : τ.okJ [] f₀ cfg₀ = true) {c : ℕ} (h : PR [(f₀, DEN / 2 + 1)] false c) (hc : c < K) :
    ∃ c' K' : ℝ, 0 < c' ∧ ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q → ∀ x : ℝ, K' * (q : ℝ) ^ L ≤ x →
      c' * x / (q.totient * Real.log x) ≤
        (((Finset.range (⌊x⌋₊ + 1)).filter fun p : ℕ => p.Prime ∧ p ≡ a [MOD q]).card : ℝ) := by
  have hC : (c : ℝ) / K < 1 := by
    rw [div_lt_one K_pos']
    exact_mod_cast hc
  obtain ⟨K', hK'⟩ := count_bd f₀ hf₀ (hτ.soundJ [] f₀ cfg₀ 0 rfl hroot) hC (h 0 rfl)
  refine ⟨(1 - (c : ℝ) / K) / 2 / 2 ^ (L + 1), K', ?_, fun q _ a ha x hx => ?_⟩
  · have : (0 : ℝ) < 2 ^ (L + 1) := Real.rpow_pos_of_pos two_pos _
    have h1 : (0 : ℝ) < (1 - (c : ℝ) / K) / 2 := by linarith
    exact div_pos h1 this
  · refine le_trans (le_of_eq ?_) (hK' q a ha x hx)
    rw [div_eq_mul_inv, mul_inv, div_eq_mul_inv x]
    ring

end SieveAd

#print axioms SieveAd.card_units_above
#print axioms SieveAd.count_of_large
#print axioms SieveAd.count_large_bd
#print axioms SieveAd.count_bd
#print axioms SieveAd.count_large_pr
#print axioms SieveAd.count_pr
