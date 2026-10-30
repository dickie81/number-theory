/-
# Linnik's theorem by the sieve route, under the refined certificate

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. The route and the grid are as in `SieveQ` (`RouteOK`, `GridOK` and `Fits`), and the decomposition's
rule (`SieveCert.Rule`) splits and decomposes a box only when `limOK` passes, or the bilinear Type I test with no
boundary term does (`RuleIB`), with the test's exponent the route's (`IBFits`); `total2` is the refined certificate's
total under the rule (`SieveCert.total2R`).

* `route_of_large`: for `L ≥ 0`, if for large `q` every unit `a` mod `q` has a prime `p ≡ a (mod q)` with
  `q^L < p ≤ 2q^L`, there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime
  `p ≡ a (mod q)` with `p ≤ K·q^L`.
* `linnik_large2`: given the route's Type II estimate (`hII`) and the refined certificate's total `total2/K ≤ c` in the
  reals for some `c < 1` (`htot`), there is `q₀` such that for `q ≥ 1` with `q ≥ q₀` and `a` a unit mod `q` there is
  a prime `p ≡ a (mod q)` with `q^L < p ≤ 2q^L`.
* `linnik_route2`: given `hII` and `htot`, there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there
  is a prime `p ≡ a (mod q)` with `p ≤ K·q^L`; `linnik_route_lt2`: the same for `total2 < K`.

The proof is `SieveMain.linnik_large_of`'s, with `SieveBuch.Par.decompk` (the decomposition with the kept parts) for
`SieveBuch.Par.decomp`, `SieveKeptLeaf.leaves_ev2` (with the kept leaves) for `SieveQ.leaves_ev`,
`SieveDrop2.drop_ev2` (the dropped terms less the kept parts) for `SieveDrop.drop_ev_of`, and the decomposition's
constant `Ck = 1 + n(1 + n(ec2 + 2 + 3n))` for `Cdec`; `route_of_large` is `SieveMain.linnik_route_of`'s step
for the small moduli (Mathlib's `Nat.forall_exists_prime_gt_and_modEq`, Dirichlet's theorem).

The file imports `SieveDrop2.lean`.
-/
import SieveMain

open Real Finset Filter SieveFamily SieveChain SieveDecomp SieveBuch SieveLeaves SieveQ SieveRough SieveDrop SieveRoute

namespace SieveMain2

open Classical

variable [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [SieveCert.GridOKC] [Fits]

omit [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [SieveCert.GridOKC] [Fits] in
/-- **The small moduli.** For `L ≥ 0` (`hL0`): if for large `q` every unit `a` mod `q` has a prime `p ≡ a (mod q)`
with `q^L < p ≤ 2q^L` (`hlarge`), there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a
prime `p ≡ a (mod q)` with `p ≤ K·q^L`: Dirichlet's theorem gives a prime for each of the finitely many smaller `q`
and residues, and `K` is the larger of `2` and their maximum. -/
theorem route_of_large (hL0 : 0 ≤ L) (hlarge : ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∃ p : ℕ, p.Prime ∧ (p : ZMod q) = a ∧ (q : ℝ) ^ L < p ∧ (p : ℝ) ≤ 2 * (q : ℝ) ^ L) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ L := by
  obtain ⟨q₀, hq₀⟩ := hlarge
  -- small moduli: one prime per residue, by Dirichlet's theorem
  let f : ℕ × ℕ → ℕ := fun x =>
    if h : x.1 ≠ 0 ∧ x.2.Coprime x.1 then Classical.choose (Nat.forall_exists_prime_gt_and_modEq 0 h.1 h.2)
    else 0
  have hf : ∀ x : ℕ × ℕ, ∀ h : x.1 ≠ 0 ∧ x.2.Coprime x.1, (f x).Prime ∧ f x ≡ x.2 [MOD x.1] := by
    intro x h
    have hs := Classical.choose_spec (Nat.forall_exists_prime_gt_and_modEq 0 h.1 h.2)
    simp only [f, dite_eq_left h]
    exact ⟨hs.2.1, hs.2.2⟩
  set M : ℕ := (Finset.range q₀ ×ˢ Finset.range q₀).sup f with hM
  refine ⟨max 2 (M : ℝ), fun q _ a ha => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqL : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow hq1 hL0
  by_cases hq : q₀ ≤ q
  · have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha
    obtain ⟨p, hp, hpa, -, hpx⟩ := hq₀ q hq (a : ZMod q) hu
    refine ⟨p, hp, (ZMod.natCast_eq_natCast_iff p a q).1 hpa, hpx.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · push Not at hq
    set r := a % q with hr
    have hq0 : q ≠ 0 := NeZero.ne q
    have hrc : r.Coprime q := by
      rw [hr]
      unfold Nat.Coprime
      rw [← Nat.gcd_rec, Nat.gcd_comm]
      exact ha
    have hrq : r < q := Nat.mod_lt a (Nat.pos_of_ne_zero hq0)
    obtain ⟨hp, hpr⟩ := hf (q, r) ⟨hq0, hrc⟩
    refine ⟨f (q, r), hp, hpr.trans (Nat.mod_modEq a q), ?_⟩
    have hmem : (q, r) ∈ Finset.range q₀ ×ˢ Finset.range q₀ :=
      Finset.mem_product.2 ⟨Finset.mem_range.2 hq, Finset.mem_range.2 (by omega)⟩
    have hle : f (q, r) ≤ M := Finset.le_sup (f := f) hmem
    have hle' : (f (q, r) : ℝ) ≤ max 2 (M : ℝ) := by
      have : (f (q, r) : ℝ) ≤ M := by exact_mod_cast hle
      exact this.trans (le_max_right _ _)
    calc (f (q, r) : ℝ) ≤ max 2 (M : ℝ) := hle'
      _ = max 2 (M : ℝ) * 1 := (mul_one _).symm
      _ ≤ max 2 (M : ℝ) * (q : ℝ) ^ L :=
          mul_le_mul_of_nonneg_left hqL (le_trans (by norm_num) (le_max_left _ _))

end SieveMain2

#print axioms SieveMain2.route_of_large
