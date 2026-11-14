/-
# Type II families with sharp prime ranges, each prime with its own lower bound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveUnwGen.unw_gen` asks for the Type II estimate at each frequency (`hbox`) on the scales `Q_i ≥ q^{e₁}` with
`∏Q_i ≤ 2^{K₀+1}q^L/P_b`, the scales of the dyadic pieces of the primes' ranges on which the family has a term. When
each prime has its own lower bound, `x_i ≥ 2q^{lo i}` wherever the comparisons hold, a piece with a scale
`Q_i < q^{lo i}` has no term either, and the estimate is asked for only on the scales with `Q_i ≥ q^{lo i}`. The
resonant window's estimate (`SieveTypeIIHM.typeII_res`) holds on such scales: its condition is on the exponents of
the rest's prime sums, each at least that of its prime's cell.

* `unw_gen_lo`: `unw_gen` with the numbers `lo i`: in the hypothesis of the support each `x_i ≥ 2q^{lo i}`, and
  in `hbox` the scales `Q_i ≥ q^{lo i}`. The proof is `unw_gen`'s, with the bound `Q_i ≥ q^{lo i}` among those of a
  piece that has a term.

The file imports `SieveUnwGen.lean`.
-/
import SieveUnwGen

open Real Finset Filter Asymptotics SieveFamily SieveFamilyGen SieveTypeIIU SieveUnwGen

namespace SieveUnwGen


open Classical

/-- **`unw_gen` with a lower bound on each prime's range.** As `unw_gen`, with numbers `lo i` such that wherever all
the comparisons hold each `x_i ≥ 2q^{lo i}`: the estimate at each frequency (`hbox`) is asked for the scales with
`Q_i ≥ q^{lo i}` besides `Q_i ≥ q^{e₁}`, for a piece whose scales are not so vanishes. -/
theorem unw_gen_lo {ι κ : Type*} [DecidableEq κ] (K₀ J₀ c₀ : ℕ) {L e₁ E₀ Λ₁ : ℝ} (hL0 : 0 < L) (hL : L ≤ 5 / 2)
    (he₁ : 0 < e₁) (hE₀ : 0 ≤ E₀) (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (Xs : Finset ι) (nv : ι → ℕ) (cf : ι → ℂ) (A₀ : ℝ), 0 ≤ A₀ →
      ∀ (blk : ι → κ) (T : Finset κ) (Pb : κ → ℝ), (∀ m ∈ Xs, blk m ∈ T) →
      (T.card : ℝ) ≤ (3 + 4 * Real.log q) ^ c₀ → (∀ b ∈ T, 0 < Pb b) → (∀ m ∈ Xs, Pb (blk m) < (nv m : ℝ)) →
      (∀ b ∈ T, ∑ m ∈ Xs.filter (fun m => blk m = b), ‖cf m‖ ≤ Pb b * A₀) →
      ∀ (n : ℕ), n + 1 ≤ K₀ → ∀ lo : ℕ → ℝ,
      ∀ {J : ℕ}, J ≤ J₀ → ∀ (φ : Fin J → ι → ℝ) (e : Fin J → Fin (n + 1) → ℝ)
        (Pr : Fin J → ι → (Fin (n + 1) → ℕ) → Prop), (∀ j i, |e j i| ≤ E₀) →
      (∀ j m x, (0 < φ j m + ∑ i, e j i * Real.log (x i) → Pr j m x) ∧
        (Pr j m x → 0 ≤ φ j m + ∑ i, e j i * Real.log (x i))) →
      (∀ j, ∀ m ∈ Xs, φ j m ≤ Λ₁ * Real.log q) →
      ∀ piv : Fin J → Fin (n + 1), (∀ j, e j (piv j) = 1 ∨ e j (piv j) = -1) →
      (∀ m ∈ Xs, ∀ x : Fin (n + 1) → ℕ, (∀ i, (x i).Prime) → (∀ j, Pr j m x) →
        (∀ i, 2 * (q : ℝ) ^ e₁ ≤ x i) ∧ (∀ i : Fin (n + 1), 2 * (q : ℝ) ^ lo i ≤ x i) ∧
          (nv m : ℝ) * ∏ i, (x i : ℝ) ≤ 2 * (q : ℝ) ^ L) →
      (∀ b ∈ T, ∀ Q : ℕ → ℝ, (∀ j < n + 1, (q : ℝ) ^ e₁ ≤ Q j) → (∀ j < n + 1, (q : ℝ) ^ lo j ≤ Q j) →
        ∏ j ∈ Finset.range (n + 1), Q j ≤ 2 ^ (K₀ + 1) * (q : ℝ) ^ L / Pb b →
        ∀ c' : ι → ℂ, (c' = cf ∨ c' = fun m => ((‖cf m‖ : ℝ) : ℂ)) → ∀ (ξ : Fin J → ℝ) (κ' : ℝ) (hh : ℕ → ℝ),
        (∀ j < n + 1, |hh j| ≤ (q : ℝ) ^ (1 / 100000 : ℝ)) →
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖∑ m ∈ Xs.filter (fun m => blk m = b),
              c' m * Complex.exp (2 * π * Complex.I * ((κ' + ∑ j, ξ j * φ j m : ℝ) : ℂ)) * χ (nv m)‖ *
            ‖∏ j ∈ Finset.range (n + 1), SieveWeight.Sp χ SieveDyadic.bump (Q j) (hh j)‖ ≤
          A₀ * (q : ℝ) ^ (L - 1 / 50000)) →
      ‖Dsum q a (Xs ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe ⌊2 * (q : ℝ) ^ L⌋₊))
          (fun mx => nv mx.1 * ∏ i, mx.2 i)
          (fun mx => cf mx.1 * ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ))‖ ≤
        (q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ (L - δ)) := by
  have hΛ₀0 : 0 ≤ Λ₁ + K₀ * E₀ * (L + 3) := by positivity
  obtain ⟨δ, hδ, q₁, hq₁⟩ := sharp_gen (ι := ι) (f0 := SieveDyadic.bump) SieveDyadic.bump_nonneg (F₀ := 1)
    SieveDyadic.bump_le_one (K₀ + 1) J₀ L he₁ hE₀ hΛ₀0
  obtain ⟨q₂, hq₂⟩ := Filter.eventually_atTop.1
    (tendsto_natCast_atTop_atTop.eventually (ev_log_pow_le (K₀ + c₀) (half_pos hδ)))
  refine ⟨δ / 2, half_pos hδ, max (max q₁ q₂) 2, ?_⟩
  intro q _ hq a ha Xs nv cf A₀ hA0 blk T Pb hblk hTcard hPbpos hPblt hsumb n hn lo J hJ φ e Pr he hP hφ piv
    hpiv hsupp hbox
  have hq1 : q₁ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hq2 : q₂ ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hq3 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hqR
  have hqL0 : 0 < (q : ℝ) ^ L := Real.rpow_pos_of_pos hq0 _
  have hqL1 : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow (by linarith) hL0.le
  set Y : ℕ := ⌊2 * (q : ℝ) ^ L⌋₊ with hY
  have hY0 : Y ≠ 0 := by
    have : 1 ≤ Y := Nat.le_floor (by push_cast; linarith)
    omega
  have hYle : (Y : ℝ) ≤ 2 * (q : ℝ) ^ L := Nat.floor_le (by positivity)
  set M : ℕ := Nat.log 2 Y + 1 with hM
  -- a nonzero weight has every `x_i ≤ Y`
  have hFY : ∀ m ∈ Xs, ∀ x : Fin (n + 1) → ℕ, (∀ i, (x i).Prime) →
      cf m * ∏ j, ((if Pr j m x then 1 else 0 : ℝ) : ℂ) ≠ 0 → ∀ i, x i ≤ Y := by
    intro m hm x hx hne i
    have hall : ∀ j, Pr j m x := by
      intro j
      by_contra hj
      exact hne (by rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), mul_zero])
    have h2 := (hsupp m hm x hx hall).2.2
    have hm1 : (1 : ℝ) ≤ nv m := by
      have h0 : (0 : ℝ) < nv m := lt_trans (hPbpos _ (hblk m hm)) (hPblt m hm)
      have h1 : 0 < nv m := by exact_mod_cast h0
      exact_mod_cast h1
    have hxi : x i ≤ ∏ i, x i :=
      Nat.le_of_dvd (Finset.prod_pos fun j _ => (hx j).pos) (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
    have hxi' : (x i : ℝ) ≤ ∏ i, (x i : ℝ) := by exact_mod_cast hxi
    have hprod0 : (0 : ℝ) ≤ ∏ i, (x i : ℝ) := Finset.prod_nonneg fun j _ => Nat.cast_nonneg _
    apply Nat.le_floor
    nlinarith
  -- the blocks of `m`
  rw [Dsum_fiber_gen a _ _ _ (fun mx => blk mx.1) T (fun mx hmx => hblk mx.1 (Finset.mem_product.1 hmx).1)]
  -- one block
  have hblock : ∀ b ∈ T,
      ‖Dsum q a ((Xs ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe Y)).filter
          (fun mx => blk mx.1 = b)) (fun mx => nv mx.1 * ∏ i, mx.2 i)
          (fun mx => cf mx.1 * ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ))‖ ≤
        ((M + 1 : ℕ) : ℝ) ^ (n + 1) * ((q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ (L - δ))) := by
    intro b hb
    set Sb := Xs.filter (fun m => blk m = b) with hSb
    have hfilt : (Xs ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe Y)).filter
        (fun mx => blk mx.1 = b) =
        Sb ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe Y) := by
      ext mx
      simp only [hSb, Finset.mem_filter, Finset.mem_product]
      tauto
    rw [hfilt]
    have hbound0 : (0 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) ^ (n + 1) *
        ((q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ (L - δ))) := by positivity
    set P' : ℝ := Pb b with hP'
    have hP'pos : (0 : ℝ) < P' := hPbpos b hb
    -- the dyadic scales of the primes
    set Kset := Fintype.piFinset (fun _ : Fin (n + 1) => Finset.range (M + 1)) with hKset
    have hdy : Dsum q a (Sb ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe Y))
        (fun mx => nv mx.1 * ∏ i, mx.2 i)
        (fun mx => cf mx.1 * ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ)) =
        ∑ k ∈ Kset, Dsum q a (Sb ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe Y))
          (fun mx => nv mx.1 * ∏ i, mx.2 i)
          (fun mx => (cf mx.1 * ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ)) *
            ∏ i, ((SieveDyadic.bump ((mx.2 i : ℝ) / 2 ^ (k i)) : ℝ) : ℂ)) := by
      rw [← Dsum_sum]
      refine Dsum_congr a _ _ fun mx hmx => ?_
      rw [← Finset.mul_sum]
      have hx := Fintype.mem_piFinset.1 (Finset.mem_product.1 hmx).2
      have hone : ∑ k ∈ Kset, ∏ i, ((SieveDyadic.bump ((mx.2 i : ℝ) / 2 ^ (k i)) : ℝ) : ℂ) = 1 := by
        have h := Finset.prod_univ_sum (fun _ : Fin (n + 1) => Finset.range (M + 1))
          (fun i k => ((SieveDyadic.bump ((mx.2 i : ℝ) / 2 ^ k) : ℝ) : ℂ))
        rw [hKset, ← h]
        refine Finset.prod_eq_one fun i _ => ?_
        rw [← Complex.ofReal_sum, SieveDyadic.sum_bump, Complex.ofReal_one]
        · exact_mod_cast (mem_primesLe.1 (hx i)).2.one_lt.le
        · have h1 := (mem_primesLe.1 (hx i)).1
          have hYM : Y < 2 ^ M := Nat.lt_pow_succ_log_self (by norm_num) Y
          exact_mod_cast (show mx.2 i ≤ 2 ^ M by omega)
      rw [hone, mul_one]
    rw [hdy]
    refine (norm_sum_le _ _).trans ?_
    have hcard : (Kset.card : ℝ) = ((M + 1 : ℕ) : ℝ) ^ (n + 1) := by
      rw [hKset, Fintype.card_piFinset]
      simp
    rw [← hcard, ← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun k hk => ?_
    have hkM : ∀ i, k i ≤ M := fun i => Nat.lt_succ_iff.1 (Finset.mem_range.1 (Fintype.mem_piFinset.1 hk i))
    set Q : ℕ → ℝ := fun j => if h : j < n + 1 then (2 : ℝ) ^ (k ⟨j, h⟩) else 1 with hQ
    have hQi : ∀ i : Fin (n + 1), Q i = (2 : ℝ) ^ (k i) := fun i => by rw [hQ]; exact dite_eq_left i.isLt
    have hQpos : ∀ i : Fin (n + 1), 0 < Q i := fun i => by rw [hQi]; positivity
    have hfam : Dsum q a (Sb ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe Y))
        (fun mx => nv mx.1 * ∏ i, mx.2 i)
        (fun mx => (cf mx.1 * ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ)) *
          ∏ i, ((SieveDyadic.bump ((mx.2 i : ℝ) / 2 ^ (k i)) : ℝ) : ℂ)) =
        Dsum q a (Sb ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i))) (fun mx => nv mx.1 * ∏ i, mx.2 i)
          (fun mx => (cf mx.1 * ∏ i, ((SieveDyadic.bump ((mx.2 i : ℝ) / Q i) : ℝ) : ℂ)) *
            ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ)) := by
      have hbc := box_change_gen a Sb nv Y (fun i => Q i) hQpos
        (fun m x => cf m * ∏ j, ((if Pr j m x then 1 else 0 : ℝ) : ℂ))
        (fun m hm x hx hne => hFY m (Finset.mem_filter.1 hm).1 x hx hne)
      calc _ = Dsum q a (Sb ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe Y))
            (fun mx => nv mx.1 * ∏ i, mx.2 i)
            (fun mx => (cf mx.1 * ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ)) *
              ∏ i, ((SieveDyadic.bump ((mx.2 i : ℝ) / Q i) : ℝ) : ℂ)) :=
            Dsum_congr a _ _ fun mx _ => by simp only [hQi]
        _ = _ := hbc
        _ = _ := Dsum_congr a _ _ fun mx _ => by ring
    rw [hfam]
    -- the comparisons' forms on the box
    have hℓ : ∀ j, ∀ m ∈ Sb, ∀ x ∈ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
        φ j m + ∑ i, e j i * Real.log (x i) ≤ (Λ₁ + K₀ * E₀ * (L + 3)) * Real.log q := by
      intro j m hm x hx
      rw [Fintype.mem_piFinset] at hx
      have hlogx : ∀ i, 0 ≤ Real.log (x i) ∧ Real.log (x i) ≤ (L + 3) * Real.log q := by
        intro i
        obtain ⟨hxle, hxp⟩ := (mem_primesTo (hQpos i).le).1 (hx i)
        have hx1 : (1 : ℝ) ≤ x i := by exact_mod_cast hxp.one_lt.le
        refine ⟨Real.log_nonneg hx1, ?_⟩
        have h2M : (2 : ℝ) ^ M ≤ 4 * (q : ℝ) ^ L := by
          have h1 : ((2 ^ Nat.log 2 Y : ℕ) : ℝ) ≤ Y := by exact_mod_cast Nat.pow_log_le_self 2 hY0
          push_cast at h1
          rw [hM, pow_succ]
          linarith
        have hxi : (x i : ℝ) ≤ 8 * (q : ℝ) ^ L := by
          have : (2 : ℝ) ^ (k i) ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) (hkM i)
          rw [hQi] at hxle
          linarith
        calc Real.log (x i) ≤ Real.log (8 * (q : ℝ) ^ L) := Real.log_le_log (by linarith) hxi
          _ = Real.log 8 + L * Real.log q := by
              rw [Real.log_mul (by norm_num) hqL0.ne', Real.log_rpow hq0]
          _ ≤ (L + 3) * Real.log q := by
              have : Real.log 8 = 3 * Real.log 2 := by
                rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
              nlinarith
      have hsum : ∑ i, e j i * Real.log (x i) ≤ ∑ _i : Fin (n + 1), E₀ * ((L + 3) * Real.log q) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := hlogx i
        have h2 : e j i ≤ E₀ := le_trans (le_abs_self _) (he j i)
        exact le_trans (mul_le_mul_of_nonneg_right h2 h1.1) (mul_le_mul_of_nonneg_left h1.2 hE₀)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
      push_cast at hsum
      have hφm := hφ j m (Finset.mem_filter.1 hm).1
      have hlq0 : 0 ≤ Real.log q := by linarith
      have hn' : ((n + 1 : ℕ) : ℝ) ≤ K₀ := by exact_mod_cast hn
      push_cast at hn'
      have h3 : ((n : ℝ) + 1) * (E₀ * ((L + 3) * Real.log q)) ≤
          (K₀ : ℝ) * (E₀ * ((L + 3) * Real.log q)) :=
        mul_le_mul_of_nonneg_right hn' (by positivity)
      linarith
    by_cases hgood : (∀ j < n + 1, (q : ℝ) ^ e₁ ≤ Q j) ∧ (∀ j < n + 1, (q : ℝ) ^ lo j ≤ Q j) ∧
        ∏ j ∈ Finset.range (n + 1), Q j ≤ 2 ^ (K₀ + 1) * (q : ℝ) ^ L / P'
    · exact hq₁ q hq1 a ha Sb nv cf P' A₀ hP'pos hA0 (hsumb b hb) n (by omega) Q hgood.1 hgood.2.2 hJ φ e Pr he
        hP hℓ piv hpiv (hbox b hb Q hgood.1 hgood.2.1 hgood.2.2)
    · have hz : ∀ mx ∈ Sb ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
          (cf mx.1 * ∏ i, ((SieveDyadic.bump ((mx.2 i : ℝ) / Q i) : ℝ) : ℂ)) *
            ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ) = 0 := by
        intro mx hmx
        obtain ⟨hm, hx⟩ := Finset.mem_product.1 hmx
        rw [Fintype.mem_piFinset] at hx
        by_contra hne
        have hall : ∀ j, Pr j mx.1 mx.2 := by
          intro j
          by_contra hj
          exact hne (by rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), mul_zero])
        have hbump : ∀ i : Fin (n + 1), Q i / 2 ≤ mx.2 i := by
          intro i
          by_contra hlt
          push Not at hlt
          apply hne
          have hb0 : SieveDyadic.bump ((mx.2 i : ℝ) / Q i) = 0 := by
            by_contra hb
            have h1 := (SieveDyadic.bump_support (Function.mem_support.2 hb)).1
            rw [le_div_iff₀ (hQpos i)] at h1
            linarith
          rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hb0, Complex.ofReal_zero]), mul_zero, zero_mul]
        have hpr : ∀ i, (mx.2 i).Prime := fun i => ((mem_primesTo (hQpos i).le).1 (hx i)).2
        obtain ⟨hlow, hlowlo, hhigh⟩ := hsupp mx.1 (Finset.mem_filter.1 hm).1 mx.2 hpr hall
        apply hgood
        refine ⟨fun j hj => ?_, fun j hj => ?_, ?_⟩
        · have h1 := ((mem_primesTo (hQpos ⟨j, hj⟩).le).1 (hx ⟨j, hj⟩)).1
          have h2 := hlow ⟨j, hj⟩
          have : Q (⟨j, hj⟩ : Fin (n + 1)) = Q j := rfl
          linarith
        · have h1 := ((mem_primesTo (hQpos ⟨j, hj⟩).le).1 (hx ⟨j, hj⟩)).1
          have h2 := hlowlo ⟨j, hj⟩
          have : Q (⟨j, hj⟩ : Fin (n + 1)) = Q j := rfl
          have : lo (⟨j, hj⟩ : Fin (n + 1)) = lo j := rfl
          linarith
        · rw [← Fin.prod_univ_eq_prod_range]
          have hprodQ : ∏ i : Fin (n + 1), Q i ≤ ∏ i : Fin (n + 1), (2 * (mx.2 i : ℝ)) :=
            Finset.prod_le_prod₀ (fun i _ => (hQpos i).le) (fun i _ => by linarith [hbump i])
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprodQ
          have hmP : P' < (nv mx.1 : ℝ) := by
            have h := hPblt mx.1 (Finset.mem_filter.1 hm).1
            rwa [(Finset.mem_filter.1 hm).2] at h
          have hprod0 : (0 : ℝ) ≤ ∏ i, (mx.2 i : ℝ) := Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
          have hprodx : ∏ i, (mx.2 i : ℝ) ≤ 2 * (q : ℝ) ^ L / P' := by
            rw [le_div_iff₀ hP'pos]
            nlinarith
          have h2pow : (2 : ℝ) ^ (n + 2) ≤ 2 ^ (K₀ + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
          calc ∏ i : Fin (n + 1), Q ↑i ≤ 2 ^ (n + 1) * ∏ i, (mx.2 i : ℝ) := hprodQ
            _ ≤ 2 ^ (n + 1) * (2 * (q : ℝ) ^ L / P') := by gcongr
            _ = 2 ^ (n + 2) * ((q : ℝ) ^ L / P') := by ring
            _ ≤ 2 ^ (K₀ + 1) * ((q : ℝ) ^ L / P') :=
                mul_le_mul_of_nonneg_right h2pow (by positivity)
            _ = 2 ^ (K₀ + 1) * (q : ℝ) ^ L / P' := by ring
      have hz' : Dsum q a (Sb ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)))
          (fun mx => nv mx.1 * ∏ i, mx.2 i)
          (fun mx => (cf mx.1 * ∏ i, ((SieveDyadic.bump ((mx.2 i : ℝ) / Q i) : ℝ) : ℂ)) *
            ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ)) = 0 :=
        Finset.sum_eq_zero fun mx hmx => by beta_reduce; rw [hz mx hmx, zero_mul]
      rw [hz', norm_zero]
      positivity
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ hblock).trans ?_)
  rw [nsmul_eq_mul]
  have hNlog : (Nat.log 2 Y : ℝ) ≤ 1 + 4 * Real.log q := by
    have h1 : ((2 ^ Nat.log 2 Y : ℕ) : ℝ) ≤ Y := by exact_mod_cast Nat.pow_log_le_self 2 hY0
    push_cast at h1
    have h3 : Real.log ((2 : ℝ) ^ Nat.log 2 Y) ≤ Real.log (2 * (q : ℝ) ^ L) :=
      Real.log_le_log (by positivity) (h1.trans hYle)
    rw [Real.log_pow, Real.log_mul (by norm_num) hqL0.ne', Real.log_rpow hq0] at h3
    have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hlq0 : 0 ≤ Real.log q := by linarith
    refine le_of_mul_le_mul_right ?_ hlog2
    nlinarith [hL, hL0]
  have hcount : (T.card : ℝ) * ((M + 1 : ℕ) : ℝ) ^ (n + 1) ≤ (q : ℝ) ^ (δ / 2) := by
    have hM1 : ((M + 1 : ℕ) : ℝ) ≤ 3 + 4 * Real.log q := by
      rw [hM]; push_cast; linarith
    have hM0 : (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have h34 : (1 : ℝ) ≤ 3 + 4 * Real.log q := hM0.trans hM1
    calc (T.card : ℝ) * ((M + 1 : ℕ) : ℝ) ^ (n + 1)
        ≤ (3 + 4 * Real.log q) ^ c₀ * (3 + 4 * Real.log q) ^ (n + 1) :=
          mul_le_mul hTcard (pow_le_pow_left₀ (by linarith) hM1 _) (by positivity) (by positivity)
      _ = (3 + 4 * Real.log q) ^ (c₀ + (n + 1)) := by rw [← pow_add]
      _ ≤ (3 + 4 * Real.log q) ^ (K₀ + c₀) := pow_le_pow_right₀ h34 (by omega)
      _ ≤ (q : ℝ) ^ (δ / 2) := hq₂ q hq2
  calc (T.card : ℝ) * (((M + 1 : ℕ) : ℝ) ^ (n + 1) *
        ((q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ (L - δ))))
      = ((T.card : ℝ) * ((M + 1 : ℕ) : ℝ) ^ (n + 1)) *
          ((q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ (L - δ))) := by ring
    _ ≤ (q : ℝ) ^ (δ / 2) * ((q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ (L - δ))) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (q.totient : ℝ)⁻¹ * (A₀ * ((q : ℝ) ^ (δ / 2) * (q : ℝ) ^ (L - δ))) := by ring
    _ = (q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ (L - δ / 2)) := by
        rw [← Real.rpow_add hq0]
        congr 3
        ring


end SieveUnwGen

#print axioms SieveUnwGen.unw_gen_lo
