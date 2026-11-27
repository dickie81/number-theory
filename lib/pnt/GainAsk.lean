import GainOrbit

/-!
# The ask

A step of the proof of the sharp frontier (`SharpInputs`, the piece `gain`; module M-G7b of the gain's numbers): the
frontier's ask `Σ_t Σ_j ASK(a_t, t, w_{u,j})` as a finite sum over the prime powers, in the frontier's (untwisted)
coordinates; its bridge to the gain's (twisted) coordinates of `GainOrbit` at an even `κ`; and the size of the gain at
an admissible design, which the fallback of the colength reads.

**Definitions.** The primes of the ask, `p ≤ 2X″` with `p ∤ N` and `p` not split (`Setting.askSupp`); the ask of a top
at such a `p` in the frontier's coordinates, `Σ_{e ∈ gainExps} (a_t/p^e − w_j(ρ_t(p^e)))⁺` with the partner
`ρ_t(n) = ((−n/q), [n]_A·t)` of `Setting.partner` (`askU`); and the ask at `d`,
`Σ_{1 ≤ e ≤ log_d⌈2a⌉ + 1} (a_t/d^e − w_j(ρ_t(d^e)))⁺` (`askAtD`).

**The ask as a finite sum** (`Setting.ASK_eq_sum`, `ask_eq_sum`). For `a_t ≤ 2a` and weights `W ≥ 1` with
`a_t ≤ 2X″·W`, `ASK(a_t, t, W) = Σ_{p ∈ askSupp} 2 log p·Σ_{e ∈ gainExps} (a_t/p^e − W(ρ_t(p^e)))⁺ +
log d·Σ_{e ≤ log_d⌈2a⌉ + 1} (a_t/d^e − W(ρ_t(d^e)))⁺`. A term `n` of the series is nonzero only if `n = p^e` is a
prime power (`Λ(n) ≠ 0`) prime to `QS·q` with `n < a_t/W ≤ 2X″` and `n < a_t ≤ 2a` (as `W ≥ 1`). At `p = d`,
`(d^e/d) = 0`, the weight is `1` and `d^e ≤ ⌈2a⌉` puts `e ≤ log_d⌈2a⌉`. At `p ≠ d`, `(p^e/d) = (p/d)^e`: the weight
`1 − (p/d)^e` vanishes at a split `p` and at even `e`, and is `2` at odd `e` and `(p/d) = −1`, that is at `p` not
split; then `p ∤ N`, `p ≤ 2X″`, and an odd `e ∉ gainExps` would have `p^e > 2a` (`lt_pow_of_notMem_gainExps`). So
the series is a sum over the prime powers `p^e`, `p ∈ askSupp`, `e ∈ gainExps`, and `d^e`, which are distinct.
At an admissible design every weight is in `[w″, 2b]` with `w″ ≥ x^{437} ≥ 1` and `a_t ≤ 2a = 2X″·w″` (`X″ = a/w″`),
and the lifts `j < m` of the frontier are those of the ranks (`Dg.hm`).

**The two coordinates** (`askU_eq_askE`). At an odd `e` and a non-split `p ∤ N`, `ρ_t(p^e) = pos_p(1, t; e)` at the
twist `1` (`Setting.partner_pow_eq_pos`): `[p^e]_A = [p]_A^e` (`Setting.clsA_pow`), and
`(−p^e/q) = (−1/q)(p/q)^e = −(p/q)` (`q ≡ 3 (mod 4)`) is `−1` at a signal `p` (`(p/q) = 1`) and `1` at an inert one,
the sign of `pos_p` at odd steps. So at an even `κ` (`twA κ = 1`) the ask `askU` is the gain's `askE`.

**The size of the gain** (`gain_le_of_adm`, `fallback_le`): `0 ≤ G_j(p) ≤ 4|TT|·a/p` at an admissible design, and so
`Σ_{p ∈ P} 2 log p·Σ_j G_j(p) ≤ 8m|TT|·a·Σ_{p ∈ P} log p/p`. The hypotheses of `gain_le` hold there: the shift
`κ_j = (k + (2j − 1)(t + 1))/2` is at most `x^{403}` (`Adm.shift_le`: `k ≤ 2x^5`, `m ≤ 2x`, `t ≤ x^{401}`), so the
caps `w̃_j + c₀ ≥ w″ − κ_j` are nonnegative, and so are the penalties of the served orbits (a non-V top has
`w̃_j(1, s) − b_s ≥ b′/x − κ_j ≥ x^{440} − x^{403}` by the top window); and `0 ≤ 2c₀ ≤ a_t ≤ 2a`.

**Against the spec.**
* The statements are the spec's. The generic identity `Setting.ASK_eq_sum` (any `a ≤ 2a`, any `W ≥ 1` with
  `a ≤ 2X″·W`) is stated apart from the design, and `Setting.inertPrimes_subset_askSupp` (Step A of the losses) is
  added.
* Only the even case of the bridge is proved (`twA κ = 1`). For an odd `κ` the sign of `pos_p` is the same, and the
  `A`-coordinate of `pos_p(1, t; e)` is `[−1]_A` times that of `ρ_t(p^e)`; that case is left to its own module.
-/

open Finset

namespace ZetaBalance

noncomputable section

/-- **The Legendre symbol of a power**: `(a^e/p) = (a/p)^e`. -/
theorem legendreSym_pow (p : ℕ) [Fact p.Prime] (a : ℤ) (e : ℕ) : legendreSym p (a ^ e) = legendreSym p a ^ e := by
  simpa using map_pow (legendreSym.hom p) a e

namespace Setting

variable (S : Setting)

/-- **The primes of the ask**: `p ≤ 2X″`, `p ∤ N`, not split (the support of `ASK` at `a_t ≤ 2a` and weights
`≥ w″`, as `a/w″ = X″`). -/
def askSupp (x ε : ℝ) : Finset ℕ :=
  (range (⌊2 * S.cutX x ε⌋₊ + 1)).filter fun p => p.Prime ∧ ¬ p ∣ S.N ∧ S.cls p ≠ .split

/-- **The inert and signal primes `p ≤ X″` are primes of the ask**, as `X″ ≤ 2X″`. -/
theorem inertPrimes_subset_askSupp {x ε : ℝ} (hx : 0 ≤ x) :
    Ranks.inertPrimes (S := S) (S.cutX x ε) ⊆ S.askSupp x ε := by
  intro p hp
  obtain ⟨hpX, hp', hN, hcls⟩ := mem_filter.1 hp
  have hX : 0 ≤ S.cutX x ε := by unfold cutX; positivity
  have h1 : ⌊S.cutX x ε⌋₊ ≤ ⌊2 * S.cutX x ε⌋₊ := Nat.floor_le_floor (by linarith)
  have h2 := mem_range.1 hpX
  exact mem_filter.2 ⟨mem_range.2 (by omega), hp', hN, hcls⟩

/-- **The ask as a finite sum over the prime powers**: for `a ≤ 2a` (the design's `a = scA x ε`) and weights
`W ≥ 1` with `a ≤ 2X″·W`, `ASK(a, t, W) = Σ_{p ∈ askSupp} 2 log p·Σ_{e ∈ gainExps} (a/p^e − W(ρ_t(p^e)))⁺ +
log d·Σ_{1 ≤ e ≤ log_d⌈2a⌉ + 1} (a/d^e − W(ρ_t(d^e)))⁺`. -/
theorem ASK_eq_sum {x ε a : ℝ} (t : S.A) {W : Φ S.A → ℝ} (ha : a ≤ 2 * scA x ε) (hW : ∀ ρ, 1 ≤ W ρ)
    (hX : ∀ ρ, a ≤ 2 * S.cutX x ε * W ρ) :
    S.ASK a t W = (∑ p ∈ S.askSupp x ε, 2 * Real.log p *
        ∑ e ∈ gainExps x ε p, max (a / (p : ℝ) ^ e - W (S.partner t (p ^ e))) 0) +
      Real.log S.d * ∑ e ∈ Icc 1 (Nat.log S.d ⌈2 * scA x ε⌉₊ + 1),
        max (a / (S.d : ℝ) ^ e - W (S.partner t (S.d ^ e))) 0 := by
  classical
  have hd : S.d.Prime := Fact.out
  have hq : S.q.Prime := Fact.out
  set L := Nat.log S.d ⌈2 * scA x ε⌉₊ + 1
  set f : ℕ → ℝ := fun n => if n.Coprime (S.QS * S.q) then
    ArithmeticFunction.vonMangoldt n * (1 - legendreSym S.d n) * max (a / n - W (S.partner t n)) 0 else 0
    with hf
  set U₁ := (S.askSupp x ε).biUnion fun p => (gainExps x ε p).image (p ^ ·)
  set U₂ := (Icc 1 L).image (S.d ^ ·)
  have hASK : S.ASK a t W = ∑' n, f n := rfl
  -- the support: the prime powers `p^e` (`p ∈ askSupp`, `e ∈ gainExps`) and `d^e` (`e ≤ L`)
  have hsupp : ∀ n ∉ U₁ ∪ U₂, f n = 0 := by
    intro n hn
    by_contra hne
    by_cases hc : n.Coprime (S.QS * S.q)
    swap
    · exact hne (ite_eq_right hc)
    simp only [hf] at hne
    rw [ite_eq_left hc] at hne
    obtain ⟨hΛl, hmax⟩ := mul_ne_zero_iff.1 hne
    obtain ⟨hΛ, hleg⟩ := mul_ne_zero_iff.1 hΛl
    obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff n).1 (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hΛ)
    have hpe0 : (0 : ℝ) < ((p ^ e : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos e
    have hWpos : 0 < W (S.partner t (p ^ e)) := lt_of_lt_of_le one_pos (hW _)
    have hgt : W (S.partner t (p ^ e)) < a / ((p ^ e : ℕ) : ℝ) := by
      by_contra h
      exact hmax (max_eq_right (by linarith [not_lt.1 h]))
    have hlt : W (S.partner t (p ^ e)) * ((p ^ e : ℕ) : ℝ) < a := (lt_div_iff₀ hpe0).1 hgt
    have hlt1 : ((p ^ e : ℕ) : ℝ) < a := by nlinarith [hW (S.partner t (p ^ e))]
    have hlt2 : ((p ^ e : ℕ) : ℝ) < 2 * S.cutX x ε := by
      have := hX (S.partner t (p ^ e))
      nlinarith
    apply hn
    by_cases hpd : p = S.d
    · subst hpd
      refine mem_union_right _ (mem_image.2 ⟨e, mem_Icc.2 ⟨he, ?_⟩, rfl⟩)
      have h1 : S.d ^ e < ⌈2 * scA x ε⌉₊ := Nat.lt_ceil.2 (by linarith)
      have := Nat.le_log_of_pow_le hd.one_lt h1.le
      omega
    · -- `p ≠ d`: the symbol is `(p/d)^e`, so `(p/d) = −1` and `e` is odd
      have hpd' : ((p : ℤ) : ZMod S.d) ≠ 0 := by
        rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
        exact fun h => hpd ((Nat.prime_dvd_prime_iff_eq hd hp).1 h).symm
      have hpow : legendreSym S.d ((p ^ e : ℕ) : ℤ) = legendreSym S.d p ^ e := by
        rw [Nat.cast_pow, legendreSym_pow]
      have hm1 : legendreSym S.d p = -1 := by
        rcases legendreSym.eq_one_or_neg_one S.d hpd' with h | h
        · exfalso
          apply hleg
          rw [hpow, h, one_pow]
          norm_num
        · exact h
      have hodd : Odd e := by
        by_contra hev
        apply hleg
        rw [hpow, hm1, (Nat.not_odd_iff_even.1 hev).neg_one_pow]
        norm_num
      have hcls : S.cls p ≠ .split := by
        simp only [cls, frob, sgn, hm1, ↓reduceIte, show (-1 : ℤˣ) ≠ 1 by decide]
        split_ifs <;> decide
      have hpc : ¬ p ∣ S.QS * S.q := fun h =>
        (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_dvd_left (dvd_pow_self p he.ne') hc) h
      have hN : ¬ p ∣ S.N := fun h => by
        rcases (Nat.Prime.dvd_mul hp).1 (show p ∣ S.QS * S.q * S.d from h) with h1 | h1
        · exact hpc h1
        · exact hpd ((Nat.prime_dvd_prime_iff_eq hp hd).1 h1)
      have hpX : p ≤ ⌊2 * S.cutX x ε⌋₊ := by
        refine Nat.le_floor ?_
        have : (p : ℝ) ≤ ((p ^ e : ℕ) : ℝ) := by exact_mod_cast Nat.le_self_pow he.ne' p
        linarith
      have heE : e ∈ gainExps x ε p := by
        by_contra h
        have := lt_pow_of_notMem_gainExps hp.two_le hodd h
        push_cast at hlt1
        linarith
      exact mem_union_left _ (mem_biUnion.2 ⟨p, mem_filter.2 ⟨mem_range.2 (by omega), hp, hN, hcls⟩,
        mem_image.2 ⟨e, heE, rfl⟩⟩)
  -- the two kinds of prime powers are disjoint, and so are the powers of distinct primes
  have hdisj : Disjoint U₁ U₂ := by
    refine disjoint_left.2 fun n h1 h2 => ?_
    obtain ⟨p, hp, hpn⟩ := mem_biUnion.1 h1
    obtain ⟨e, he, rfl⟩ := mem_image.1 hpn
    obtain ⟨e', -, hee'⟩ := mem_image.1 h2
    obtain ⟨-, hp, hN, -⟩ := mem_filter.1 hp
    have h1 : p ∣ S.d ^ e' := by
      rw [show S.d ^ e' = p ^ e from hee']
      exact dvd_pow_self p (Nat.one_le_iff_ne_zero.1 (one_le_of_mem_gainExps he))
    exact hN ((Nat.prime_dvd_prime_iff_eq hp hd).1 (hp.dvd_of_dvd_pow h1) ▸ S.d_dvd_N)
  have hpd : (S.askSupp x ε : Set ℕ).PairwiseDisjoint fun p => (gainExps x ε p).image (p ^ ·) := by
    intro p hp p' hp' hne
    refine disjoint_left.2 fun n h1 h2 => hne ?_
    obtain ⟨e, he, rfl⟩ := mem_image.1 h1
    obtain ⟨e', -, hee'⟩ := mem_image.1 h2
    have hp1 := (mem_filter.1 (mem_coe.1 hp)).2.1
    have hp2 := (mem_filter.1 (mem_coe.1 hp')).2.1
    have h3 : p ∣ p' ^ e' := by
      rw [show p' ^ e' = p ^ e from hee']
      exact dvd_pow_self p (Nat.one_le_iff_ne_zero.1 (one_le_of_mem_gainExps he))
    exact (Nat.prime_dvd_prime_iff_eq hp1 hp2).1 (hp1.dvd_of_dvd_pow h3)
  rw [hASK, tsum_eq_sum hsupp, sum_union hdisj, sum_biUnion hpd,
    sum_image fun e _ e' _ h => Nat.pow_right_injective hd.two_le h]
  congr 1
  · -- at `p ∈ askSupp`: `Λ(p^e) = log p` and `1 − (p^e/d) = 2` at odd `e`
    refine sum_congr rfl fun p hp => ?_
    obtain ⟨-, hp, hN, hcls⟩ := mem_filter.1 hp
    rw [sum_image fun e _ e' _ h => Nat.pow_right_injective hp.two_le h, mul_sum]
    refine sum_congr rfl fun e he => ?_
    have he0 : e ≠ 0 := Nat.one_le_iff_ne_zero.1 (one_le_of_mem_gainExps he)
    have hcop : (p ^ e).Coprime (S.QS * S.q) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h =>
        hN (h.trans (show S.QS * S.q ∣ S.N from dvd_mul_right _ _)))
    have hΛ : ArithmeticFunction.vonMangoldt (p ^ e) = Real.log p := by
      rw [ArithmeticFunction.vonMangoldt_apply_pow he0, ArithmeticFunction.vonMangoldt_apply_prime hp]
    have hleg : legendreSym S.d ((p ^ e : ℕ) : ℤ) = -1 := by
      rw [Nat.cast_pow, legendreSym_pow, S.legendreSym_eq_neg_one_of_cls hcls,
        (odd_of_mem_gainExps he).neg_one_pow]
    simp only [hf]
    rw [ite_eq_left hcop, hΛ, hleg]
    push_cast
    ring
  · -- at `d`: `Λ(d^e) = log d` and `(d^e/d) = 0`
    rw [mul_sum]
    refine sum_congr rfl fun e he => ?_
    have he0 : e ≠ 0 := by have := (mem_Icc.1 he).1; omega
    have hcop : (S.d ^ e).Coprime (S.QS * S.q) :=
      Nat.Coprime.pow_left _ (Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hd).2 S.d_not_dvd)
        ((Nat.coprime_primes hd hq).2 S.q_ne_d.symm))
    have hΛ : ArithmeticFunction.vonMangoldt (S.d ^ e) = Real.log S.d := by
      rw [ArithmeticFunction.vonMangoldt_apply_pow he0, ArithmeticFunction.vonMangoldt_apply_prime hd]
    have hleg : legendreSym S.d ((S.d ^ e : ℕ) : ℤ) = 0 := by
      rw [legendreSym.eq_zero_iff]
      push_cast
      simp [he0]
    simp only [hf]
    rw [ite_eq_left hcop, hΛ, hleg]
    push_cast
    ring

/-- **The class of a power**: `[n^e]_A = [n]_A^e` for `n` prime to `QS`. -/
theorem clsA_pow {n : ℕ} (hn : IsUnit (n : ZMod S.QS)) (e : ℕ) : S.clsA (n ^ e) = S.clsA n ^ e := by
  have hne : IsUnit ((n ^ e : ℕ) : ZMod S.QS) := by rw [Nat.cast_pow]; exact hn.pow e
  rw [clsA, dite_eq_left hne, clsA, dite_eq_left hn, ← map_pow]
  congr 1
  ext
  simp

/-- **The untwisted partner is the orbit position at the twist `1`**: for a non-split prime `p ∤ N` and an odd `e`,
`ρ_t(p^e) = pos_p(1, t; e)` at `c = 1`. The `A`-coordinates are `[p^e]_A·t = t·[p]_A^e`; the signs are
`(−p^e/q) = (−1/q)(p/q)^e = −(p/q)`, which is `−1` at a signal `p` and `1` at an inert `p`, as is the sign of
`pos_p` at an odd step. -/
theorem partner_pow_eq_pos {p : ℕ} (hp : p.Prime) (hN : ¬ p ∣ S.N) (hcls : S.cls p ≠ .split) (t : S.A) {e : ℕ}
    (he : Odd e) : S.partner t (p ^ e) = S.pos 1 p (1, t) e := by
  have hq : S.q.Prime := Fact.out
  have hpQ : ¬ p ∣ S.QS := fun h => hN (h.trans S.QS_dvd_N)
  have hpq : p ≠ S.q := fun h => hN (h ▸ S.q_dvd_N)
  have hunit : IsUnit (p : ZMod S.QS) :=
    (ZMod.isUnit_iff_coprime p S.QS).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpQ)
  have hq3 : legendreSym S.q (-1) = -1 := by
    rw [legendreSym.at_neg_one S.q_ne_two, ZMod.χ₄_nat_three_mod_four S.q_mod_four]
  have hpq' : ((p : ℤ) : ZMod S.q) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 h).symm
  have h1 : (S.frob p).1 ≠ 1 := fun h' => hcls (by rw [cls, ite_eq_left h'])
  have hcl : S.cls p = if sgn S.q p = 1 then .signal else .inert := by rw [cls, ite_eq_right h1]; rfl
  refine Prod.ext ?_ ?_
  · show sgn S.q (-((p ^ e : ℕ) : ℤ)) = (1 : ℤˣ) * (if S.cls p = .signal ∧ Odd e then -1 else 1)
    rw [one_mul, hcl]
    unfold sgn
    rw [neg_eq_neg_one_mul, legendreSym.mul, hq3, Nat.cast_pow, legendreSym_pow]
    rcases legendreSym.eq_one_or_neg_one S.q hpq' with h | h <;> rw [h] <;> simp [he, he.neg_one_pow]
  · show S.clsA (p ^ e) * t = t * S.hPtw 1 p ^ e
    rw [hPtw, one_mul, hP, frob, S.clsA_pow hunit, mul_comm]

end Setting

namespace SharpDesign

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X)

/-! ## The ask in the frontier's coordinates -/

/-- **The ask of a top at `p`**, in the frontier's (untwisted) coordinates: `Σ_{e ∈ gainExps} (a_t/p^e −
w_j(ρ_t(p^e)))⁺`, with the partner `ρ_t(n) = ((−n/q), [n]_A·t)` of `Setting.partner`. -/
def askU (u : S.A) (J : Fin Dg.R.m) (p : ℕ) (t : S.A) : ℝ :=
  ∑ e ∈ gainExps x ε p, max (Dg.a t / (p : ℝ) ^ e - Dg.wt u J (S.partner t (p ^ e))) 0

/-- **The ask at `d`**: every `e ≥ 1` with `d^e ≤ 2a`, and beyond, up to `log_d⌈2a⌉ + 1`. -/
def askAtD (u : S.A) (J : Fin Dg.R.m) (t : S.A) : ℝ :=
  ∑ e ∈ Icc 1 (Nat.log S.d ⌈2 * scA x ε⌉₊ + 1),
    max (Dg.a t / (S.d : ℝ) ^ e - Dg.wt u J (S.partner t (S.d ^ e))) 0

variable {Dg}

/-- **The shift of the weights is small**: `κ_j = (k + (2j − 1)(t + 1))/2 ≤ x^{403}` at the lift `j = J + 1`, as
`k ≤ 2x^5`, `j ≤ m ≤ 2x` and `t ≤ x^{401}`. -/
theorem Adm.shift_le (hA : Dg.Adm) (J : Fin Dg.R.m) :
    ((Dg.R.k : ℝ) + (2 * (J : ℝ) + 1) * ((Dg.R.t : ℝ) + 1)) / 2 ≤ x ^ 403 := by
  have hx := hA.big.x_ge
  obtain ⟨-, hk⟩ := hA.big.designK_le
  rw [← hA.k_eq] at hk
  have ht : (Dg.R.t : ℝ) ≤ x ^ 401 := by rw [hA.t_eq]; exact designT_le S hA.big hA.card_le
  have hm : (Dg.R.m : ℝ) ≤ 2 * x := by rw [hA.m_eq]; exact hA.big.designM_le
  have hJ : (J : ℝ) + 1 ≤ Dg.R.m := by exact_mod_cast J.isLt
  have h1 : (1 : ℝ) ≤ x ^ 401 := one_le_pow₀ (by linarith)
  have h5 : x ^ 5 ≤ x ^ 402 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h402 : 0 ≤ x ^ 402 := by positivity
  have e2 : x ^ 403 = x * x ^ 402 := by ring
  have hJ0 : (0 : ℝ) ≤ 2 * (J : ℝ) + 1 := by positivity
  have ht0 : (0 : ℝ) ≤ (Dg.R.t : ℝ) + 1 := by positivity
  calc ((Dg.R.k : ℝ) + (2 * (J : ℝ) + 1) * ((Dg.R.t : ℝ) + 1)) / 2 ≤
      (2 * x ^ 5 + (4 * x) * (2 * x ^ 401)) / 2 := by
        gcongr
        · linarith
        · linarith
    _ = x ^ 5 + 4 * x ^ 402 := by ring
    _ ≤ x ^ 403 := by rw [e2]; nlinarith

/-- **The ask as a finite sum** at an admissible design: `Σ_t Σ_j ASK(a_t, t, w_{u,j}) =
Σ_t Σ_j (Σ_{p ∈ askSupp} 2 log p·askU + log d·askAtD)`, exact in the frontier's (untwisted) coordinates for every
`κ` (`Setting.ASK_eq_sum`, with `a_t ≤ 2a`, `w ≥ w″ ≥ 1` and `2X″·w″ = 2a`). -/
theorem ask_eq_sum (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (u : S.A) :
    ∑ t ∈ Dg.TT, ∑ j, S.ASK (Dg.a t) t (Dg.w u j) =
      ∑ t ∈ Dg.TT, ∑ J, ((∑ p ∈ S.askSupp x ε, 2 * Real.log p * Dg.askU u J p t) +
        Real.log S.d * Dg.askAtD u J t) := by
  have hx := hA.big.x_ge
  have hw := hA.toDesignAdm.w''_ge
  have hw1 : (1 : ℝ) ≤ scW'' S x ε := le_trans (one_le_pow₀ (by linarith)) hw
  have hX : S.cutX x ε * scW'' S x ε = scA x ε := by
    have h := scA_div_scW'' S ε hA.big.pos
    rw [div_eq_iff (scW''_pos S ε hA.big.pos).ne'] at h
    rw [h]
    rfl
  refine sum_congr rfl fun t ht => ?_
  rw [← (finCongr Dg.hm).sum_comp]
  refine sum_congr rfl fun j _ => ?_
  have hwj : Dg.w u j = Dg.wt u (Fin.cast Dg.hm j) := funext fun ρ => Dg.hw u j ρ
  have hX0 : 0 ≤ S.cutX x ε := by unfold Setting.cutX; have := hA.big.pos; positivity
  rw [hwj, S.ASK_eq_sum (W := Dg.wt u (Fin.cast Dg.hm j)) t (hA.a_le_two hF ht)
    (fun ρ => hw1.trans (hA.e_mem u ρ _).1) fun ρ => ?_]
  · simp only [askU, askAtD, mul_sum, finCongr_apply]
  · have h1 := (hA.e_mem u ρ (Fin.cast Dg.hm j)).1
    have h2 := hA.a_le_two hF ht
    have : 2 * S.cutX x ε * scW'' S x ε ≤ 2 * S.cutX x ε * Dg.wt u (Fin.cast Dg.hm j) ρ :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    linarith

/-- **The two coordinates agree at an even `κ`**: with `twA κ = 1`, `askU = askE` at every non-split `p ∤ N`, as
`ρ_t(p^e) = pos_p(1, t; e)` at the odd `e` of `gainExps` (`Setting.partner_pow_eq_pos`). -/
theorem askU_eq_askE (hχ : S.twA κ = 1) (u : S.A) (J : Fin Dg.R.m) {p : ℕ} (hp : p.Prime) (hN : ¬ p ∣ S.N)
    (hcls : S.cls p ≠ .split) (t : S.A) : Dg.askU u J p t = Dg.askE u J p t := by
  unfold askU askE
  refine sum_congr rfl fun e he => ?_
  rw [hχ, S.partner_pow_eq_pos hp hN hcls t (odd_of_mem_gainExps he)]

open scoped Classical in
/-- **The size of the gain at an admissible design**: `0 ≤ G_j(p) ≤ 4|TT|·a/p` (`gain_le`): the caps
`w̃_j + c₀ ≥ w″ − κ_j` and the served penalties are nonnegative (`κ_j ≤ x^{403}`, `Adm.shift_le`; a non-V top has
`w̃_j(1, s) − b_s ≥ b′/x − κ_j` by the top window, `b′/x ≥ x^{440}`), and `0 ≤ a_t ≤ 2a`. -/
theorem gain_le_of_adm (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (u : S.A) (J : Fin Dg.R.m) (p : ℕ) :
    0 ≤ Dg.gainG pr u J p ∧ Dg.gainG pr u J p ≤ 4 * Dg.TT.card * scA x ε / p := by
  have hx := hA.big.x_ge
  have hκ := hA.shift_le J
  have h437 : x ^ 403 ≤ x ^ 437 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hw := hA.toDesignAdm.w''_ge
  have hc0 := Dg.c0_nonneg
  refine Dg.gain_le hA.one_le_x pr u J p (fun z => ?_) (fun t₀ _ => ?_) fun s hs =>
    ⟨by linarith [hA.two_c0_le_a hF hs], hA.a_le_two hF hs⟩
  · have : scW'' S x ε ≤ Dg.wt u J z := (hA.e_mem u z J).1
    unfold wsh
    linarith
  · have hb' := hA.big.b'_ge
    have hb'x : x ^ 440 ≤ scB' x ε / x := by
      rw [le_div_iff₀ (by linarith)]
      calc x ^ 440 * x = x ^ 441 := by ring
        _ ≤ _ := hb'
    have h440 : x ^ 403 ≤ x ^ 440 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hW : 0 ≤ scW'' S x ε + Dg.eta + Dg.c0 + Dg.R.N Dg.R.m := by
      have := scW''_pos S ε hA.big.pos
      have := Dg.eta_nonneg
      positivity
    have hB : 0 ≤ 2 * scB' x ε + Dg.c0 := by have := scB'_pos ε hA.big.pos; positivity
    unfold pen
    split_ifs
    · refine add_nonneg (sum_nonneg fun s hs => ?_) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (Nat.cast_nonneg _)) hW)
      have hsT : s ∈ Dg.TT := (mem_filter.1 (mem_filter.1 hs).1).1
      have := (hA.top_window hF u J hsT).1
      unfold wsh
      linarith
    · exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hB)
        (mul_nonneg (Nat.cast_nonneg _) hW))

/-- **The fallback**: `Σ_{p ∈ P} 2 log p·Σ_j G_j(p) ≤ 8m|TT|·a·Σ_{p ∈ P} log p/p` for any set `P` of primes
(`gain_le_of_adm`, `log p ≥ 0`): the half of the colength bound at the candidates with large `Σ_j κ_j` that M-G7
supplies. -/
theorem fallback_le (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (u : S.A) (P : Finset ℕ) :
    ∑ p ∈ P, 2 * Real.log p * ∑ J, Dg.gainG pr u J p ≤
      8 * Dg.R.m * Dg.TT.card * scA x ε * ∑ p ∈ P, Real.log p / p := by
  rw [mul_sum]
  refine sum_le_sum fun p _ => ?_
  have hl := Real.log_natCast_nonneg p
  have h : ∑ J, Dg.gainG pr u J p ≤ Dg.R.m * (4 * Dg.TT.card * scA x ε / p) := by
    calc _ ≤ ∑ _J : Fin Dg.R.m, 4 * Dg.TT.card * scA x ε / p :=
          sum_le_sum fun J _ => (gain_le_of_adm hA hF u J p).2
      _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc 2 * Real.log p * ∑ J, Dg.gainG pr u J p ≤ 2 * Real.log p * (Dg.R.m * (4 * Dg.TT.card * scA x ε / p)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

end SharpDesign

end

end ZetaBalance
