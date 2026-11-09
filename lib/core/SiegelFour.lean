/-
# Siegel's formula for four squares: the points on the sphere are the volume times the local densities

Plain statement. Count the solutions of `x₁² + x₂² + x₃² + x₄² ≡ n` modulo `q` (`localCount`, by representatives in
`[0, q)⁴`; in `(ℤ/q)⁴`, `localCount_eq_card`). Modulo the powers of a prime `p` the counts stabilise: from the level
`k = v_p(n) + 1` for odd `p`, `k = v₂(n) + 3` at `2`, each step multiplies the count by `p³` (`localCount_succ`), so
`#{x mod p^k}/p^{3k}` tends to the local density `δ_p(n)` (`delta`, `tendsto_delta`), with
* `δ_p(n) = (1 − p⁻²)(1 + p⁻¹ + ⋯ + p^{−v_p(n)})` for odd `p` (`delta_odd`), so `1 − p⁻²` when `p ∤ n`;
* `δ₂(n) = 1` for odd `n` and `3·2^{−v₂(n)}` for even `n` (`delta_two`).
**Siegel's formula** for four squares (`siegel`): `∏_p δ_p(n) = r₄(n)/(π²n)`, so the number `r₄(n)` of points of `ℤ⁴`
on the sphere `x₁² + ⋯ + x₄² = n` is the factor `π²n` of the sphere times the product of the local densities. This is
the global statement that `LocalTeeth` leaves open, in dimension `4`; `GlobalTeeth` and `FourSquareTeeth` give the
prime-by-prime form without densities.
* Hensel, counted (`countN_succ`): over an odd prime a solution with some `xᵢ` prime to `p` has `p³` lifts, by the
  count of an affine hyperplane over `𝔽_p` (`card_hyperplane`). The solutions with every `xᵢ` divisible by `p` need
  `p² ∣ n` and are `p⁴` times the solutions for `n/p²` two levels down (`countS_eq`). At `2` a lift needs two levels
  (`countN_two_succ`), and the counts modulo `8` come from those of two squares (`countN_two_eight`).
* Modulo an odd prime the counts are `p³ − p` for `p ∤ n` (`LocalTeeth.teeth_mod_prime`) and `p³ + p² − p` for
  `p ∣ n` (`localCount_prime`). The product over the primes uses Euler's product `∏_p (1 − p⁻²) = 6/π²` (Mathlib's
  `EulerProduct.eulerProduct_completely_multiplicative_hasProd` and `hasSum_zeta_two`), and is compared with Jacobi's
  theorem through `FourSquareTeeth.r4_two_pow_mul`.
-/
import Mathlib
import JacobiFourSquares
import FourSquareTeeth
import LocalTeeth

open Finset

noncomputable section

namespace SiegelFour

/-! ## Counting in the box `[0, q)⁴` -/

/-- The box `[0, q)⁴` of representatives of `(ℤ/q)⁴`. -/
abbrev box (q : ℕ) : Finset (Fin 4 → ℕ) := Fintype.piFinset fun _ => range q

lemma mem_box {q : ℕ} {a : Fin 4 → ℕ} : a ∈ box q ↔ ∀ i, a i < q := by simp [box]

/-- **The local count**: the solutions of `x₁² + x₂² + x₃² + x₄² ≡ n` modulo `q`, by their representatives in
`[0, q)⁴`. -/
def localCount (q n : ℕ) : ℕ := ((box q).filter fun a => ∑ i, a i ^ 2 ≡ n [MOD q]).card

/-- Splitting `[0, mr)⁴` as `[0, m)⁴ + m·[0, r)⁴`. -/
lemma card_filter_box_mul {m r : ℕ} (hm : 0 < m) (P : (Fin 4 → ℕ) → Prop) [DecidablePred P] :
    ((box (m * r)).filter P).card = ∑ a ∈ box m, ((box r).filter fun b => P (a + m • b)).card := by
  have hprod : ∑ a ∈ box m, ((box r).filter fun b => P (a + m • b)).card =
      ((box m ×ˢ box r).filter fun x => P (x.1 + m • x.2)).card := by
    rw [card_filter, sum_product]
    refine sum_congr rfl fun a _ => ?_
    rw [card_filter]
  rw [hprod]
  refine card_nbij' (fun a => ((fun i => a i % m), (fun i => a i / m))) (fun x => x.1 + m • x.2)
    ?_ ?_ ?_ ?_
  · intro a ha
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_box] at ha ⊢
    refine ⟨⟨fun i => Nat.mod_lt _ hm, fun i => (Nat.div_lt_iff_lt_mul hm).2 (by rw [mul_comm]; exact ha.1 i)⟩,
      ?_⟩
    convert ha.2 using 1
    funext i
    simp [Nat.mod_add_div]
  · intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_box] at hx ⊢
    refine ⟨fun i => ?_, hx.2⟩
    have h1 := hx.1.1 i
    have h2 := hx.1.2 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc x.1 i + m * x.2 i < m + m * x.2 i := by omega
      _ = m * (x.2 i + 1) := by ring
      _ ≤ m * r := Nat.mul_le_mul_left _ h2
  · intro a _
    funext i
    simp [Nat.mod_add_div]
  · intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_box] at hx
    ext i
    · simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hx.1.1 i)]
    · simp [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt (hx.1.1 i)]

/-- The box `[0, q)⁴` is a set of representatives of `(ℤ/q)⁴`. -/
lemma card_box_filter_zmod {q : ℕ} [NeZero q] (P : (Fin 4 → ZMod q) → Prop) [DecidablePred P] :
    ((box q).filter fun a => P fun i => (a i : ZMod q)).card = (univ.filter P).card := by
  refine card_nbij' (fun a i => (a i : ZMod q)) (fun x i => (x i).val) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [coe_filter, Set.mem_ofPred_eq] at ha
    simpa using ha.2
  · intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hx
    simp only [coe_filter, Set.mem_ofPred_eq, mem_box, ZMod.natCast_val, ZMod.cast_id', id_eq]
    exact ⟨fun i => ZMod.val_lt _, hx⟩
  · intro a ha
    simp only [coe_filter, Set.mem_ofPred_eq, mem_box] at ha
    funext i
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt (ha.1 i)]
  · intro x _
    funext i
    simp

/-- **The local count in `(ℤ/q)⁴`**. -/
theorem localCount_eq_card {q : ℕ} [NeZero q] (n : ℕ) :
    localCount q n = (univ.filter fun x : Fin 4 → ZMod q => ∑ i, x i ^ 2 = (n : ZMod q)).card := by
  rw [← card_box_filter_zmod]
  unfold localCount
  congr 1
  refine filter_congr fun a _ => ?_
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rfl

/-- **An affine hyperplane over `𝔽_p` has `p³` points**. -/
lemma card_hyperplane {p : ℕ} (hp : p.Prime) (α : Fin 4 → ℤ) {i₀ : Fin 4} (hα : ¬ (p : ℤ) ∣ α i₀) (c : ℤ) :
    ((box p).filter fun b => (p : ℤ) ∣ c + ∑ i, α i * b i).card = p ^ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have e : ((box p).filter fun b => (p : ℤ) ∣ c + ∑ i, α i * b i) =
      (box p).filter fun b => (fun x : Fin 4 → ZMod p => (c : ZMod p) + ∑ i, (α i : ZMod p) * x i = 0)
        fun i => (b i : ZMod p) := by
    refine filter_congr fun b _ => ?_
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rfl
  rw [e, card_box_filter_zmod (q := p) (fun x : Fin 4 → ZMod p => (c : ZMod p) + ∑ i, (α i : ZMod p) * x i = 0)]
  -- the linear form is surjective, so its fibres have `p⁴/p` points each
  let f : (Fin 4 → ZMod p) →+ ZMod p :=
    { toFun := fun x => ∑ i, (α i : ZMod p) * x i
      map_zero' := by simp
      map_add' := fun x y => by simp [mul_add, sum_add_distrib] }
  have hα' : (α i₀ : ZMod p) ≠ 0 := fun h => hα ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h)
  have hsurj : Function.Surjective f := fun y => ⟨Pi.single i₀ ((α i₀ : ZMod p)⁻¹ * y), by
    simp [f, Pi.single_apply, mul_inv_cancel_left₀ hα']⟩
  have hfib : ∀ y : ZMod p, (univ.filter fun x => f x = y).card = (univ.filter fun x => f x = 0).card :=
    fun y => AddMonoidHom.card_fiber_eq_of_mem_range f (hsurj y) (hsurj 0)
  have htot : ∑ y : ZMod p, (univ.filter fun x => f x = y).card = p ^ 4 := by
    rw [← card_eq_sum_card_fiberwise (fun x _ => mem_univ (f x)), card_univ, Fintype.card_fun,
      ZMod.card, Fintype.card_fin]
  simp only [hfib, sum_const, card_univ, ZMod.card, smul_eq_mul] at htot
  have hcount : (univ.filter fun x => f x = 0).card = p ^ 3 := by
    have hp0 : 0 < p := hp.pos
    have : p * (univ.filter fun x => f x = 0).card = p * p ^ 3 := by rw [htot]; ring
    exact Nat.eq_of_mul_eq_mul_left hp0 this
  rw [← hcount, ← hfib (-(c : ZMod p))]
  congr 1
  refine filter_congr fun x _ => ?_
  simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [add_comm, add_eq_zero_iff_eq_neg]
  exact Iff.rfl


lemma card_box (q : ℕ) : (box q).card = q ^ 4 := by simp [box, Fintype.card_piFinset]

lemma localCount_mod (q n : ℕ) : localCount q (n % q) = localCount q n := by
  unfold localCount
  congr 1
  exact filter_congr fun a _ =>
    ⟨fun h => h.trans (Nat.mod_modEq n q), fun h => h.trans (Nat.mod_modEq n q).symm⟩

/-- `Σ (aᵢ + m bᵢ)² = Σ aᵢ² + 2m Σ aᵢbᵢ + m² Σ bᵢ²`. -/
lemma sum_sq_add (a b : Fin 4 → ℕ) (m : ℕ) :
    ((∑ i, (a + m • b) i ^ 2 : ℕ) : ℤ) =
      ((∑ i, a i ^ 2 : ℕ) : ℤ) + 2 * m * ∑ i, (a i : ℤ) * b i + (m : ℤ) ^ 2 * ∑ i, (b i : ℤ) ^ 2 := by
  push_cast
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_add, Nat.cast_mul, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  ring

/-- The congruence mod `m` sees `a + m b` as `a`. -/
lemma sum_sq_add_modEq (a b : Fin 4 → ℕ) (m : ℕ) : ∑ i, (a + m • b) i ^ 2 ≡ ∑ i, a i ^ 2 [MOD m] := by
  rw [Nat.modEq_iff_dvd, sum_sq_add]
  exact ⟨-(2 * ∑ i, (a i : ℤ) * b i + m * ∑ i, (b i : ℤ) ^ 2), by ring⟩

/-- **Periodicity**: a condition mod `m` counted in `[0, mr)⁴` is `r⁴` times the count in `[0, m)⁴`. -/
lemma card_box_mul_modEq {m r : ℕ} (hm : 0 < m) (n : ℕ) :
    ((box (m * r)).filter fun b => ∑ i, b i ^ 2 ≡ n [MOD m]).card = r ^ 4 * localCount m n := by
  rw [card_filter_box_mul hm, localCount, card_filter, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  have e : ((box r).filter fun b => ∑ i, (a + m • b) i ^ 2 ≡ n [MOD m]) =
      (box r).filter fun _ => ∑ i, a i ^ 2 ≡ n [MOD m] :=
    filter_congr fun b _ => ⟨fun h => (sum_sq_add_modEq a b m).symm.trans h,
      fun h => (sum_sq_add_modEq a b m).trans h⟩
  rw [e]
  split_ifs with h
  · rw [filter_true_of_mem fun _ _ => h, card_box, mul_one]
  · rw [filter_false_of_mem fun _ _ => h, card_empty, mul_zero]

/-! ## Nonsingular and singular solutions -/

/-- The nonsingular solutions: some coordinate is prime to `p`. -/
def countN (p q n : ℕ) : ℕ := ((box q).filter fun a => ∑ i, a i ^ 2 ≡ n [MOD q] ∧ ∃ i, ¬ p ∣ a i).card

/-- The singular solutions: every coordinate is divisible by `p`. -/
def countS (p q n : ℕ) : ℕ := ((box q).filter fun a => ∑ i, a i ^ 2 ≡ n [MOD q] ∧ ∀ i, p ∣ a i).card

lemma localCount_eq_add (p q n : ℕ) : localCount q n = countN p q n + countS p q n := by
  unfold localCount countN countS
  rw [← card_filter_add_card_filter_not (s := (box q).filter fun a => ∑ i, a i ^ 2 ≡ n [MOD q])
    (fun a => ∃ i, ¬ p ∣ a i), filter_filter, filter_filter]
  congr 2
  exact filter_congr fun a _ => by rw [not_exists_not]

/-- **Hensel's lemma, counted**: for an odd prime `p` and `k ≥ 1`, each nonsingular solution mod `p^k` has `p³`
lifts mod `p^{k+1}`. -/
lemma countN_succ {p k n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k) :
    countN p (p ^ (k + 1)) n = p ^ 3 * countN p (p ^ k) n := by
  have hpk : 0 < p ^ k := pow_pos hp.pos k
  unfold countN
  rw [pow_succ, card_filter_box_mul hpk, card_filter, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  have hdiv : ∀ (b : Fin 4 → ℕ) i, p ∣ (a + p ^ k • b) i ↔ p ∣ a i := fun b i => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact Nat.dvd_add_left (dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _)
  by_cases hQ1 : ∑ i, a i ^ 2 ≡ n [MOD p ^ k]
  · by_cases hQ2 : ∃ i, ¬ p ∣ a i
    · obtain ⟨i₀, hi₀⟩ := hQ2
      obtain ⟨d, hd⟩ := (Nat.modEq_iff_dvd.1 hQ1)
      have h2T : ∀ b : Fin 4 → ℕ, ∑ i, (2 * (a i : ℤ)) * b i = 2 * ∑ i, (a i : ℤ) * b i := fun b => by
        rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
      have e : ((box p).filter fun b => ∑ i, (a + p ^ k • b) i ^ 2 ≡ n [MOD p ^ k * p] ∧
          ∃ i, ¬ p ∣ (a + p ^ k • b) i) =
          (box p).filter fun b => (p : ℤ) ∣ -d + ∑ i, (2 * (a i : ℤ)) * b i := by
        refine filter_congr fun b _ => ?_
        have hex : ∃ i, ¬ p ∣ (a + p ^ k • b) i := ⟨i₀, by rwa [hdiv]⟩
        simp only [hex, and_true]
        rw [Nat.modEq_iff_dvd]
        have hX : (n : ℤ) - ((∑ i, (a + p ^ k • b) i ^ 2 : ℕ) : ℤ) = (p : ℤ) ^ k *
            (-(-d + ∑ i, (2 * (a i : ℤ)) * b i) - (p : ℤ) ^ k * ∑ i, (b i : ℤ) ^ 2) := by
          rw [sum_sq_add, h2T b]
          push_cast at hd ⊢
          linear_combination hd
        rw [hX]
        push_cast
        rw [mul_dvd_mul_iff_left (pow_ne_zero _ (by exact_mod_cast hp.ne_zero)), dvd_sub_left
          (dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _), dvd_neg]
      rw [e, card_hyperplane hp _ (i₀ := i₀), ite_eq_left ⟨hQ1, i₀, hi₀⟩, mul_one]
      intro h
      have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
      rcases hp'.dvd_or_dvd h with h2 | h2
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (by exact_mod_cast h2))
      · exact hi₀ (by exact_mod_cast h2)
    · rw [ite_eq_right fun h => hQ2 h.2, mul_zero]
      refine card_eq_zero.2 (filter_eq_empty_iff.2 fun b _ h => hQ2 ?_)
      obtain ⟨i, hi⟩ := h.2
      exact ⟨i, by rwa [hdiv] at hi⟩
  · rw [ite_eq_right fun h => hQ1 h.1, mul_zero]
    refine card_eq_zero.2 (filter_eq_empty_iff.2 fun b _ h => hQ1 ?_)
    exact (sum_sq_add_modEq a b (p ^ k)).symm.trans (Nat.ModEq.of_mul_right p h.1)

/-- **The singular solutions** mod `p^k`, `k ≥ 2`: `x = p y`, so `p² ∣ n` and `y` solves the equation for `n/p²`
mod `p^{k−2}`, with `p⁴` choices of `y` mod `p^{k−1}` for each. -/
lemma countS_eq {p k n : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    countS p (p ^ k) n = if p ^ 2 ∣ n then p ^ 4 * localCount (p ^ (k - 2)) (n / p ^ 2) else 0 := by
  have hp0 : 0 < p := hp.pos
  have hpk : p ^ k = p * p ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  have hbij : countS p (p ^ k) n =
      ((box (p ^ (k - 1))).filter fun b => ∑ i, (p * b i) ^ 2 ≡ n [MOD p ^ k]).card := by
    unfold countS
    refine card_nbij' (fun a i => a i / p) (fun b i => p * b i) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [coe_filter, Set.mem_ofPred_eq, mem_box] at ha ⊢
      refine ⟨fun i => (Nat.div_lt_iff_lt_mul hp0).2 ?_, ?_⟩
      · rw [← pow_succ]; convert ha.1 i using 2; omega
      · have e : ∑ i, (p * (a i / p)) ^ 2 = ∑ i, a i ^ 2 :=
          sum_congr rfl fun i _ => by rw [Nat.mul_div_cancel' (ha.2.2 i)]
        rw [e]
        exact ha.2.1
    · intro b hb
      simp only [coe_filter, Set.mem_ofPred_eq, mem_box] at hb ⊢
      refine ⟨fun i => ?_, hb.2, fun i => dvd_mul_right _ _⟩
      rw [hpk]
      exact Nat.mul_lt_mul_of_pos_left (hb.1 i) hp0
    · intro a ha
      simp only [coe_filter, Set.mem_ofPred_eq] at ha
      funext i
      exact Nat.mul_div_cancel' (ha.2.2 i)
    · intro b _
      funext i
      exact Nat.mul_div_cancel_left _ hp0
  rw [hbij]
  have hsq : ∀ b : Fin 4 → ℕ, ∑ i, (p * b i) ^ 2 = p ^ 2 * ∑ i, b i ^ 2 := fun b => by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  split_ifs with hn
  · obtain ⟨n', rfl⟩ := hn
    have hpk2 : p ^ k = p ^ 2 * p ^ (k - 2) := by rw [← pow_add]; congr 1; omega
    have e : ((box (p ^ (k - 1))).filter fun b => ∑ i, (p * b i) ^ 2 ≡ p ^ 2 * n' [MOD p ^ k]) =
        (box (p ^ (k - 2) * p)).filter fun b => ∑ i, b i ^ 2 ≡ n' [MOD p ^ (k - 2)] := by
      rw [show p ^ (k - 2) * p = p ^ (k - 1) by rw [← pow_succ]; congr 1; omega]
      refine filter_congr fun b _ => ?_
      rw [hsq, hpk2]
      exact Nat.ModEq.mul_left_cancel_iff' (pow_ne_zero 2 hp.ne_zero)
    rw [e, card_box_mul_modEq (pow_pos hp0 _), Nat.mul_div_cancel_left _ (pow_pos hp0 2)]
  · refine card_eq_zero.2 (filter_eq_empty_iff.2 fun b _ h => hn ?_)
    have h2 : p ^ 2 ∣ p ^ k := pow_dvd_pow p hk
    rw [hsq] at h
    exact ((Nat.ModEq.of_dvd h2 h).dvd_iff dvd_rfl).1 (dvd_mul_right _ _)

lemma countS_one {p n : ℕ} (hp : p.Prime) : countS p p n = if p ∣ n then 1 else 0 := by
  unfold countS
  have e : ((box p).filter fun a => ∑ i, a i ^ 2 ≡ n [MOD p] ∧ ∀ i, p ∣ a i) =
      if p ∣ n then {fun _ => 0} else ∅ := by
    ext a
    simp only [mem_filter, mem_box]
    constructor
    · rintro ⟨hb, hs, hd⟩
      have ha : a = fun _ => 0 := funext fun i => Nat.eq_zero_of_dvd_of_lt (hd i) (hb i)
      subst ha
      have : p ∣ n := (Nat.modEq_zero_iff_dvd.1 (by simpa using hs.symm))
      simp [this]
    · intro h
      split_ifs at h with hn
      · rw [mem_singleton] at h
        subst h
        refine ⟨fun _ => hp.pos, ?_, fun _ => dvd_zero p⟩
        simpa using (Nat.modEq_zero_iff_dvd.2 hn).symm
      · simp at h
  rw [e]
  split_ifs <;> simp


/-- The parity condition of a hyperplane mod `2` is periodic: `[0, 4)⁴` holds `16` copies of `[0, 2)⁴`. -/
lemma card_parity_box_four (α : Fin 4 → ℤ) (c : ℤ) :
    ((box 4).filter fun b => (2 : ℤ) ∣ c + ∑ i, α i * b i).card =
      16 * ((box 2).filter fun b => (2 : ℤ) ∣ c + ∑ i, α i * b i).card := by
  have h4 : box 4 = box (2 * 2) := rfl
  rw [h4, card_filter_box_mul two_pos, card_filter, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  have e : ((box 2).filter fun b => (2 : ℤ) ∣ c + ∑ i, α i * ((a + 2 • b) i : ℕ)) =
      (box 2).filter fun _ => (2 : ℤ) ∣ c + ∑ i, α i * a i := by
    refine filter_congr fun b _ => ?_
    have : c + ∑ i, α i * ((a + 2 • b) i : ℕ) = (c + ∑ i, α i * a i) + 2 * ∑ i, α i * b i := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_add, Nat.cast_mul, mul_sum,
        ← sum_add_distrib, add_assoc]
      congr 1
      exact sum_congr rfl fun i _ => by push_cast; ring
    rw [this]
    exact (dvd_add_left (dvd_mul_right 2 _))
  rw [e]
  split_ifs with h
  · rw [filter_true_of_mem fun _ _ => h, card_box]; norm_num
  · rw [filter_false_of_mem fun _ _ => h, card_empty, mul_zero]

/-- **Hensel at `2`, counted**: for `k ≥ 3` the nonsingular solutions mod `2^{k+1}` are `8` times those mod `2^k`. -/
lemma countN_two_succ {k n : ℕ} (hk : 3 ≤ k) : countN 2 (2 ^ (k + 1)) n = 8 * countN 2 (2 ^ k) n := by
  set m := 2 ^ (k - 1) with hm
  have hm0 : 0 < m := by positivity
  have h1 : 2 ^ (k + 1) = m * 4 := by
    rw [hm, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have h2 : 2 ^ k = m * 2 := by rw [hm, ← pow_succ]; congr 1; omega
  have h4m : 4 ∣ m := by rw [hm, show (4 : ℕ) = 2 ^ 2 by norm_num]; exact pow_dvd_pow 2 (by omega)
  obtain ⟨m', hm'⟩ := h4m
  unfold countN
  rw [h1, h2, card_filter_box_mul hm0, card_filter_box_mul hm0, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  have hdiv : ∀ (b : Fin 4 → ℕ) i, 2 ∣ (a + m • b) i ↔ 2 ∣ a i := fun b i => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact Nat.dvd_add_left (dvd_mul_of_dvd_left (by rw [hm']; exact ⟨2 * m', by ring⟩) _)
  -- mod `2m` the lift `a + m b` looks like `a`
  have hmod2 : ∀ b : Fin 4 → ℕ, ∑ i, (a + m • b) i ^ 2 ≡ ∑ i, a i ^ 2 [MOD m * 2] := fun b => by
    rw [Nat.modEq_iff_dvd, sum_sq_add]
    refine ⟨-(∑ i, (a i : ℤ) * b i + 2 * m' * ∑ i, (b i : ℤ) ^ 2), ?_⟩
    rw [hm']; push_cast; ring
  have hlow : ((box 2).filter fun b => ∑ i, (a + m • b) i ^ 2 ≡ n [MOD m * 2] ∧ ∃ i, ¬ 2 ∣ (a + m • b) i) =
      (box 2).filter fun _ => ∑ i, a i ^ 2 ≡ n [MOD m * 2] ∧ ∃ i, ¬ 2 ∣ a i := by
    refine filter_congr fun b _ => ?_
    simp only [hdiv]
    exact and_congr_left' ⟨fun h => (hmod2 b).symm.trans h, fun h => (hmod2 b).trans h⟩
  rw [hlow]
  by_cases hQ : ∑ i, a i ^ 2 ≡ n [MOD m * 2] ∧ ∃ i, ¬ 2 ∣ a i
  · rw [filter_true_of_mem fun _ _ => hQ, card_box]
    obtain ⟨⟨d, hd⟩, i₀, hi₀⟩ := And.intro (Nat.modEq_iff_dvd.1 hQ.1) hQ.2
    have e : ((box 4).filter fun b => ∑ i, (a + m • b) i ^ 2 ≡ n [MOD m * 4] ∧ ∃ i, ¬ 2 ∣ (a + m • b) i) =
        (box 4).filter fun b => (2 : ℤ) ∣ -d + ∑ i, (a i : ℤ) * b i := by
      refine filter_congr fun b _ => ?_
      have hex : ∃ i, ¬ 2 ∣ (a + m • b) i := ⟨i₀, by rwa [hdiv]⟩
      simp only [hex, and_true]
      rw [Nat.modEq_iff_dvd, sum_sq_add]
      have hX : (n : ℤ) - (((∑ i, a i ^ 2 : ℕ) : ℤ) + 2 * (m : ℕ) * ∑ i, (a i : ℤ) * b i +
          ((m : ℕ) : ℤ) ^ 2 * ∑ i, (b i : ℤ) ^ 2) =
          ((m * 4 : ℕ) : ℤ) * (-(m' * ∑ i, (b i : ℤ) ^ 2)) + (2 * m : ℤ) * -(-d + ∑ i, (a i : ℤ) * b i) := by
        push_cast at hd ⊢
        rw [hm'] at hd ⊢
        push_cast at hd ⊢
        linear_combination hd
      rw [hX, dvd_add_right (dvd_mul_right _ _), show ((m * 4 : ℕ) : ℤ) = (2 * m : ℤ) * 2 by
        push_cast; ring, mul_dvd_mul_iff_left (by positivity), dvd_neg]
    have hh := card_hyperplane Nat.prime_two (fun i => (a i : ℤ)) (i₀ := i₀)
      (fun h => hi₀ (by exact_mod_cast h)) (-d)
    push_cast at hh
    rw [e, card_parity_box_four, hh]
    norm_num
  · rw [filter_false_of_mem fun _ _ => hQ, card_empty, mul_zero]
    refine card_eq_zero.2 (filter_eq_empty_iff.2 fun b _ h => hQ ⟨?_, ?_⟩)
    · have h4 : m * 2 ∣ m * 4 := Nat.mul_dvd_mul_left m (by norm_num)
      exact (hmod2 b).symm.trans (Nat.ModEq.of_dvd h4 h.1)
    · obtain ⟨i, hi⟩ := h.2
      exact ⟨i, by rwa [hdiv] at hi⟩

/-! ## The counts modulo a prime and modulo `8` -/

/-- `(Fin 4 → R) ≃ (R × R) × (R × R)`. -/
def splitEquiv (R : Type*) : (Fin 4 → R) ≃ (R × R) × (R × R) where
  toFun x := ((x 0, x 1), (x 2, x 3))
  invFun y := ![y.1.1, y.1.2, y.2.1, y.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv y := rfl

lemma card_split {R : Type*} [CommRing R] [Fintype R] [DecidableEq R] (a : R) :
    (univ.filter fun x : Fin 4 → R => ∑ i, x i ^ 2 = a).card =
      (univ.filter fun y : (R × R) × (R × R) => (y.1.1 ^ 2 + y.1.2 ^ 2) + (y.2.1 ^ 2 + y.2.2 ^ 2) = a).card := by
  have hkey : ∀ x : Fin 4 → R, ((splitEquiv R x).1.1 ^ 2 + (splitEquiv R x).1.2 ^ 2) +
      ((splitEquiv R x).2.1 ^ 2 + (splitEquiv R x).2.2 ^ 2) = ∑ i, x i ^ 2 := fun x => by
    rw [Fin.sum_univ_four]
    change x 0 ^ 2 + x 1 ^ 2 + (x 2 ^ 2 + x 3 ^ 2) = _
    ring
  refine card_nbij' (splitEquiv R) (splitEquiv R).symm ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    rw [hkey, hx]
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
    rw [← hkey, Equiv.apply_symm_apply, hy]
  · intro x _; exact (splitEquiv R).symm_apply_apply x
  · intro y _; exact (splitEquiv R).apply_symm_apply y

/-- Counting the solutions of `f x + g y = a` fibre by fibre. -/
lemma card_add_eq {R : Type*} [AddCommGroup R] [Fintype R] [DecidableEq R] {α β : Type*} [Fintype α] [Fintype β]
    (f : α → R) (g : β → R) (a : R) :
    (univ.filter fun p : α × β => f p.1 + g p.2 = a).card =
      ∑ b : R, (univ.filter fun x => f x = b).card * (univ.filter fun y => g y = a - b).card := by
  have h1 : (univ.filter fun p : α × β => f p.1 + g p.2 = a).card =
      ∑ x : α, (univ.filter fun y => g y = a - f x).card := by
    rw [card_filter, ← univ_product_univ, sum_product]
    refine sum_congr rfl fun x _ => ?_
    rw [card_filter]
    refine sum_congr rfl fun y _ => ?_
    congr 1
    exact propext ⟨fun h => by rw [← h]; abel, fun h => by rw [h]; abel⟩
  rw [h1, ← sum_fiberwise univ f (fun x => (univ.filter fun y => g y = a - f x).card)]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_congr rfl (fun x hx => by rw [(mem_filter.mp hx).2]), sum_const, smul_eq_mul]

/-- **Modulo an odd prime**: `p³ − p` solutions for `p ∤ n` (`LocalTeeth`), and `p³ + p² − p` for `p ∣ n`. -/
lemma localCount_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) :
    (localCount p n : ℤ) = if p ∣ n then (p : ℤ) ^ 3 + p ^ 2 - p else (p : ℤ) ^ 3 - p := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hq : ∀ a : ZMod p, a ≠ 0 →
      ((univ.filter fun x : Fin 4 → ZMod p => ∑ i, x i ^ 2 = a).card : ℤ) = (p : ℤ) ^ 3 - p := fun a ha => by
    rw [card_split]; exact (LocalTeeth.teeth_mod_prime p hp2 ha).2
  rw [localCount_eq_card]
  split_ifs with hn
  · have h0 : ((n : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).2 hn
    rw [h0]
    have htot : ∑ a : ZMod p, ((univ.filter fun x : Fin 4 → ZMod p => ∑ i, x i ^ 2 = a).card : ℤ) = p ^ 4 := by
      rw [← Nat.cast_sum, ← card_eq_sum_card_fiberwise (fun x _ => mem_univ _), card_univ, Fintype.card_fun,
        ZMod.card, Fintype.card_fin]
      push_cast; ring
    rw [← add_sum_erase _ _ (mem_univ (0 : ZMod p)), sum_congr rfl fun a ha => hq a (ne_of_mem_erase ha),
      sum_const, card_erase_of_mem (mem_univ _), card_univ, ZMod.card, nsmul_eq_mul] at htot
    push_cast [Nat.cast_sub hp.one_le] at htot
    linear_combination htot
  · exact hq _ fun h => hn ((ZMod.natCast_eq_zero_iff n p).1 h)

/-- The `2`-dimensional counts modulo `8`. -/
def two8 (b : ZMod 8) : ℕ := (univ.filter fun x : ZMod 8 × ZMod 8 => x.1 ^ 2 + x.2 ^ 2 = b).card

lemma conv_eight (r : ℕ) (hr : r < 8) : ∑ b : ZMod 8, two8 b * two8 ((r : ZMod 8) - b) =
    if r = 0 then 128 else if r = 4 then 384 else if r = 2 ∨ r = 6 then 768 else 512 := by
  interval_cases r <;> decide

lemma localCount_two (n : ℕ) : localCount 2 n = 8 := by
  rw [← localCount_mod]
  have h : n % 2 < 2 := Nat.mod_lt _ two_pos
  interval_cases (n % 2) <;> decide

/-- **Modulo `8`**: the nonsingular solutions number `512`, `768`, `256` or `0` as `n` is odd, `2 mod 4`,
`4 mod 8` or `0 mod 8`. -/
lemma countN_two_eight (n : ℕ) :
    countN 2 8 n = if n % 2 = 1 then 512 else if n % 4 = 2 then 768 else if n % 8 = 4 then 256 else 0 := by
  have htot := localCount_eq_add 2 8 n
  have hS : countS 2 8 n = if 4 ∣ n then 128 else 0 := by
    have := countS_eq (p := 2) (k := 3) (n := n) Nat.prime_two (by norm_num)
    norm_num [localCount_two] at this
    exact this
  have hlt : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have h8 : localCount 8 n = ∑ b : ZMod 8, two8 b * two8 (((n % 8 : ℕ) : ZMod 8) - b) := by
    rw [localCount_eq_card, card_split, ZMod.natCast_mod]
    exact card_add_eq (fun x : ZMod 8 × ZMod 8 => x.1 ^ 2 + x.2 ^ 2) (fun x : ZMod 8 × ZMod 8 => x.1 ^ 2 + x.2 ^ 2)
      (n : ZMod 8)
  rw [h8, conv_eight _ hlt, hS] at htot
  split_ifs at htot ⊢ <;> omega


/-! ## The stable counts -/

lemma countN_pow {p k n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k) :
    countN p (p ^ k) n = p ^ (3 * (k - 1)) * countN p p n := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [countN_succ hp hp2 hk, ih, ← mul_assoc, ← pow_add]
    congr 2
    omega

lemma countN_two_pow {k n : ℕ} (hk : 3 ≤ k) : countN 2 (2 ^ k) n = 8 ^ (k - 3) * countN 2 8 n := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [countN_two_succ hk, ih, ← mul_assoc, ← pow_succ']
    congr 2
    omega

/-- The nonsingular solutions modulo an odd prime. -/
lemma countN_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) :
    (countN p p n : ℝ) = if p ∣ n then (p : ℝ) ^ 3 + p ^ 2 - p - 1 else (p : ℝ) ^ 3 - p := by
  have h := localCount_eq_add p p n
  have hl := localCount_prime hp hp2 n
  rw [countS_one hp] at h
  have hl' : (localCount p n : ℝ) = if p ∣ n then (p : ℝ) ^ 3 + p ^ 2 - p else (p : ℝ) ^ 3 - p := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hl
    push_cast at this
    rw [this]
  have hc : (localCount p n : ℝ) = countN p p n + if p ∣ n then 1 else 0 := by
    rw [h]; push_cast; split_ifs <;> simp
  split_ifs at hl' hc ⊢ <;> linarith

/-- The density at an odd prime, `(1 − p⁻²)(1 + p⁻¹ + ⋯ + p^{−v})`. -/
def dOdd (p : ℝ) (v : ℕ) : ℝ := (1 - p⁻¹ ^ 2) * ∑ i ∈ range (v + 1), p⁻¹ ^ i

lemma dOdd_add_two (p : ℝ) (v : ℕ) : dOdd p (v + 2) = (1 - p⁻¹ ^ 2) * (1 + p⁻¹) + p⁻¹ ^ 2 * dOdd p v := by
  have h : ∑ i ∈ range (v + 2 + 1), p⁻¹ ^ i = 1 + p⁻¹ + p⁻¹ ^ 2 * ∑ i ∈ range (v + 1), p⁻¹ ^ i := by
    rw [show v + 2 + 1 = v + 1 + 1 + 1 by ring, sum_range_succ', sum_range_succ', mul_sum]
    have e : ∀ i, p⁻¹ ^ (i + 1 + 1) = p⁻¹ ^ 2 * p⁻¹ ^ i := fun i => by ring
    rw [sum_congr rfl fun i _ => e i]
    ring
  unfold dOdd
  rw [h]
  ring

/-- **The stable counts at an odd prime**: for `k ≥ v_p(n) + 1`, `#{x mod p^k} = p^{3k}·δ`. -/
lemma localCount_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ v n k : ℕ, n ≠ 0 → padicValNat p n = v → v + 1 ≤ k →
      (localCount (p ^ k) n : ℝ) = (p : ℝ) ^ (3 * k) * dOdd p v := by
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hdvd : ∀ {n j : ℕ}, n ≠ 0 → (p ^ j ∣ n ↔ j ≤ padicValNat p n) := fun hn => padicValNat_dvd_iff_le hn
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  intro n k hn hv hk
  have hk1 : 1 ≤ k := by omega
  have hsplit := localCount_eq_add p (p ^ k) n
  have hN := countN_pow (n := n) hp hp2 hk1
  have hNr : (countN p (p ^ k) n : ℝ) = (p : ℝ) ^ (3 * (k - 1)) * countN p p n := by
    rw [hN]; push_cast; ring
  rw [countN_prime hp hp2] at hNr
  have hpow : (p : ℝ) ^ (3 * k) = (p : ℝ) ^ (3 * (k - 1)) * p ^ 3 := by
    rw [← pow_add]; congr 1; omega
  rcases Nat.lt_or_ge v 2 with hv2 | hv2
  · -- `v ≤ 1`: no singular solutions
    have hS : countS p (p ^ k) n = 0 := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · obtain rfl : k = 1 := by omega
        rw [pow_one, countS_one hp, ite_eq_right]
        intro h
        have : 1 ≤ padicValNat p n := (hdvd (j := 1) hn).1 (by simpa using h)
        omega
      · rw [countS_eq hp hk2, ite_eq_right]
        intro h
        have := (hdvd hn).1 h
        omega
    rw [hsplit, hS, Nat.cast_add, Nat.cast_zero, add_zero, hNr, hpow]
    interval_cases v
    · rw [ite_eq_right]
      · unfold dOdd; simp only [zero_add, range_one, sum_singleton, pow_zero, mul_one]
        field_simp
      · intro h; have := (hdvd (j := 1) hn).1 (by simpa using h); omega
    · rw [ite_eq_left]
      · unfold dOdd; simp only [show 1 + 1 = 2 by rfl, sum_range_succ, range_one, sum_singleton, pow_zero,
          pow_one]
        field_simp; ring
      · exact (pow_one p) ▸ (hdvd hn).2 (by omega)
  · -- `v ≥ 2`: the singular solutions come from `n/p²`
    obtain ⟨w, rfl⟩ : ∃ w, v = w + 2 := ⟨v - 2, by omega⟩
    have hk2 : 2 ≤ k := by omega
    have hp2n : p ^ 2 ∣ n := (hdvd hn).2 (by omega)
    have hn' : n / p ^ 2 ≠ 0 := by
      intro h
      have := Nat.div_eq_zero_iff.1 h
      rcases this with h0 | hlt
      · exact absurd h0 (pow_ne_zero 2 hp.ne_zero)
      · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hp2n) (not_le.2 hlt)
    have hv' : padicValNat p (n / p ^ 2) = w := by rw [padicValNat.div_pow hp2n, hv]; omega
    have hrec := ih w (by omega) (n / p ^ 2) (k - 2) hn' hv' (by omega)
    rw [hsplit, countS_eq hp hk2, ite_eq_left hp2n, Nat.cast_add, Nat.cast_mul, hrec, hNr, ite_eq_left
      (dvd_trans (dvd_pow_self p two_ne_zero) hp2n), dOdd_add_two]
    have hpow2 : (p : ℝ) ^ (3 * k) = (p : ℝ) ^ 4 * p ^ (3 * (k - 2)) * p ^ 2 := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [hpow, show (p : ℝ) ^ (3 * (k - 1)) = (p : ℝ) ^ (3 * (k - 2)) * p ^ 3 by rw [← pow_add]; congr 1; omega] at *
    push_cast
    field_simp
    ring

/-- The density at `2`: `1` for odd `n`, `3·2^{−v}` for `v = v₂(n) ≥ 1`. -/
def dTwo (v : ℕ) : ℝ := if v = 0 then 1 else 3 / 2 ^ v

/-- **The stable counts at `2`**: for `k ≥ v₂(n) + 3`, `#{x mod 2^k} = 2^{3k}·δ`. -/
lemma localCount_two_pow : ∀ v n k : ℕ, n ≠ 0 → padicValNat 2 n = v → v + 3 ≤ k →
    (localCount (2 ^ k) n : ℝ) = (2 : ℝ) ^ (3 * k) * dTwo v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : ∀ {n j : ℕ}, n ≠ 0 → (2 ^ j ∣ n ↔ j ≤ padicValNat 2 n) := fun hn => padicValNat_dvd_iff_le hn
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  intro n k hn hv hk
  have hsplit := localCount_eq_add 2 (2 ^ k) n
  have hN := countN_two_pow (n := n) (show 3 ≤ k by omega)
  have h8 := countN_two_eight n
  have hpow : (2 : ℝ) ^ (3 * k) = (8 : ℝ) ^ (k - 3) * 2 ^ 9 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_add]; congr 1; omega
  have hk2 : 2 ≤ k := by omega
  rw [hsplit, hN, countS_eq Nat.prime_two hk2]
  -- the residue of `n` mod `8` from `v`
  have hmod : (v = 0 → n % 2 = 1) ∧ (v = 1 → n % 4 = 2) ∧ (v = 2 → n % 8 = 4) ∧ (3 ≤ v → n % 8 = 0) := by
    refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
    · have : ¬ 2 ∣ n := fun h => by have := (hdvd (j := 1) hn).1 (by simpa using h); omega
      omega
    · have h2d : 2 ∣ n := by simpa using (hdvd hn).2 (by omega : 1 ≤ padicValNat 2 n)
      have h4d : ¬ 4 ∣ n := fun h => by
        have := (hdvd (j := 2) hn).1 (by simpa using h); omega
      omega
    · have h4d : 4 ∣ n := by simpa using (hdvd (j := 2) hn).2 (by omega)
      have h8d : ¬ 8 ∣ n := fun h => by
        have := (hdvd (j := 3) hn).1 (by simpa using h); omega
      omega
    · have h8d : 8 ∣ n := by simpa using (hdvd (j := 3) hn).2 (by omega)
      omega
  rcases Nat.lt_or_ge v 2 with hv2 | hv2
  · have h4 : ¬ 2 ^ 2 ∣ n := fun h => by have := (hdvd hn).1 h; omega
    rw [ite_eq_right h4, add_zero]
    push_cast
    interval_cases v
    · rw [h8, ite_eq_left (hmod.1 rfl), hpow]; unfold dTwo; norm_num
    · rw [h8, ite_eq_right (by have := hmod.2.1 rfl; omega), ite_eq_left (hmod.2.1 rfl), hpow]; unfold dTwo
      norm_num
      ring
  · obtain ⟨w, rfl⟩ : ∃ w, v = w + 2 := ⟨v - 2, by omega⟩
    have hp2n : 2 ^ 2 ∣ n := (hdvd hn).2 (by omega)
    have hn' : n / 2 ^ 2 ≠ 0 := by
      intro h
      rcases Nat.div_eq_zero_iff.1 h with h0 | hlt
      · norm_num at h0
      · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hp2n) (not_le.2 hlt)
    have hv' : padicValNat 2 (n / 2 ^ 2) = w := by rw [padicValNat.div_pow hp2n, hv]; omega
    have hrec := ih w (by omega) (n / 2 ^ 2) (k - 2) hn' hv' (by omega)
    rw [ite_eq_left hp2n, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hrec, h8]
    have hpow2 : (2 : ℝ) ^ (3 * k) = (2 : ℝ) ^ 4 * 2 ^ (3 * (k - 2)) * 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_add]; congr 1; omega
    rcases Nat.lt_or_ge w 1 with hw | hw
    · obtain rfl : w = 0 := by omega
      rw [ite_eq_right (by have := hmod.2.2.1 rfl; omega), ite_eq_right (by have := hmod.2.2.1 rfl; omega),
        ite_eq_left (hmod.2.2.1 rfl)]
      unfold dTwo
      rw [hpow2]
      have : (8 : ℝ) ^ (k - 3) * 2 ^ 8 = 2 ^ (3 * (k - 2)) * 2 ^ 5 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_add, ← pow_add]; congr 1; omega
      push_cast
      norm_num
      linear_combination this
    · have h0 := hmod.2.2.2 (by omega)
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      unfold dTwo
      rw [ite_eq_right (by omega), ite_eq_right (by omega), hpow2]
      push_cast
      field_simp
      ring


/-! ## The local densities -/

/-- The level from which the counts modulo `p^k` are stable: `v_p(n) + 1` for odd `p`, `v₂(n) + 3` at `2`. -/
def level (p n : ℕ) : ℕ := if p = 2 then padicValNat 2 n + 3 else padicValNat p n + 1

/-- **The local density** `δ_p(n)`: the solutions modulo `p^k` over `p^{3k}`, at the stable level `k`. -/
def delta (p n : ℕ) : ℝ := localCount (p ^ level p n) n / (p : ℝ) ^ (3 * level p n)

lemma delta_eq {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    delta p n = if p = 2 then dTwo (padicValNat 2 n) else dOdd p (padicValNat p n) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold delta level
  split_ifs with h2
  · subst h2
    rw [localCount_two_pow _ n _ hn rfl le_rfl]
    push_cast
    field_simp
  · rw [localCount_odd hp h2 _ n _ hn rfl le_rfl]
    field_simp

/-- From the stable level on, the count modulo `p^k` is `p^{3k}·δ_p(n)`. -/
lemma localCount_stable {p n k : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hk : level p n ≤ k) :
    (localCount (p ^ k) n : ℝ) = (p : ℝ) ^ (3 * k) * delta p n := by
  rw [delta_eq hp hn]
  unfold level at hk
  split_ifs at hk ⊢ with h2
  · subst h2; exact localCount_two_pow _ n k hn rfl hk
  · exact localCount_odd hp h2 _ n k hn rfl hk

/-- **The counts stabilise (Hensel)**: from the stable level on, each step multiplies the count by `p³`. -/
theorem localCount_succ {p n k : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hk : level p n ≤ k) :
    localCount (p ^ (k + 1)) n = p ^ 3 * localCount (p ^ k) n := by
  have h : (localCount (p ^ (k + 1)) n : ℝ) = (p : ℝ) ^ 3 * localCount (p ^ k) n := by
    rw [localCount_stable hp hn hk, localCount_stable hp hn (by omega : level p n ≤ k + 1)]
    ring
  exact_mod_cast h

/-- **`δ_p(n)` is the limit** of `#{x mod p^k}/p^{3k}`. -/
theorem tendsto_delta {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    Filter.Tendsto (fun k => (localCount (p ^ k) n : ℝ) / (p : ℝ) ^ (3 * k)) Filter.atTop
      (nhds (delta p n)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (level p n)] with k hk
  rw [localCount_stable hp hn hk]
  field_simp

/-- **The density at an odd prime**: `δ_p(n) = (1 − p⁻²)(1 + p⁻¹ + ⋯ + p^{−v_p(n)})`. -/
theorem delta_odd {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : n ≠ 0) :
    delta p n = (1 - (p : ℝ)⁻¹ ^ 2) * ∑ i ∈ range (padicValNat p n + 1), (p : ℝ)⁻¹ ^ i := by
  rw [delta_eq hp hn, ite_eq_right hp2]
  rfl

/-- **The density at `2`**: `δ₂(n) = 1` for odd `n`, and `3·2^{−v}` for `v = v₂(n) ≥ 1`. -/
theorem delta_two {n : ℕ} (hn : n ≠ 0) :
    delta 2 n = if padicValNat 2 n = 0 then 1 else 3 / 2 ^ padicValNat 2 n := by
  rw [delta_eq Nat.prime_two hn, ite_eq_left rfl]
  rfl

/-! ## Siegel's formula -/

/-- Euler's product for `1/ζ(2) = 6/π²`. -/
lemma hasProd_one_sub_inv_sq : HasProd (fun p : Nat.Primes => 1 - ((p : ℕ) : ℝ)⁻¹ ^ 2) (6 / Real.pi ^ 2) := by
  let f : ℕ →*₀ ℝ :=
    { toFun := fun n => ((n : ℝ) ^ 2)⁻¹
      map_zero' := by simp
      map_one' := by simp
      map_mul' := fun a b => by push_cast; rw [mul_pow, mul_inv] }
  have hsum : Summable fun n => ‖f n‖ := by
    simp only [f, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_inv, norm_pow, Real.norm_natCast]
    exact Real.summable_nat_pow_inv.2 one_lt_two
  have h := EulerProduct.eulerProduct_completely_multiplicative_hasProd hsum
  have hz : ∑' n, f n = Real.pi ^ 2 / 6 := by
    simp only [f, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
    simpa [one_div] using hasSum_zeta_two.tsum_eq
  rw [hz] at h
  have h' := h.inv₀ (by positivity)
  convert h' using 1
  · funext p
    simp [f, inv_pow]
  · field_simp

/-- **Siegel's formula for four squares**: `r₄(n) = π² n ∏_p δ_p(n)`, the volume of the sphere times the product of
the local densities. -/
theorem siegel {n : ℕ} (hn : n ≠ 0) :
    HasProd (fun p : Nat.Primes => delta p n) ((JacobiFourSquares.r4 n : ℝ) / (Real.pi ^ 2 * n)) := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hm0 : m ≠ 0 := fun h => by simp [h] at hm
  have hm2 : ¬ 2 ∣ m := fun h => (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h)
  set N := 2 ^ k * m with hN
  -- the finitely many primes where `δ_p(n) ≠ 1 − p⁻²`
  set T : Finset ℕ := insert 2 m.primeFactors with hT
  have hTN : ∀ q : ℕ, q.Prime → q ∉ T → delta q N = 1 - (q : ℝ)⁻¹ ^ 2 := by
    intro q hq hqT
    have hq2 : q ≠ 2 := fun h => hqT (h ▸ mem_insert_self 2 _)
    have hqm : ¬ q ∣ m := fun h => hqT (mem_insert_of_mem (Nat.mem_primeFactors.2 ⟨hq, h, hm0⟩))
    have : Fact q.Prime := ⟨hq⟩
    have hv : padicValNat q N = 0 := by
      rw [hN, padicValNat.mul (pow_ne_zero _ two_ne_zero) hm0,
        padicValNat.eq_zero_of_not_dvd (fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1
          (hq.dvd_of_dvd_pow h))), padicValNat.eq_zero_of_not_dvd hqm]
    rw [delta_odd hq hq2 hn, hv]
    simp
  set f : Nat.Primes → ℝ := fun p => 1 - ((p : ℕ) : ℝ)⁻¹ ^ 2 with hf
  set g : Nat.Primes → ℝ := fun p => delta p N / f p with hg
  have hf0 : ∀ p : Nat.Primes, f p ≠ 0 := fun p => by
    have h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
    have : ((p : ℕ) : ℝ)⁻¹ ^ 2 < 1 := by
      rw [inv_pow]; exact inv_lt_one_of_one_lt₀ (by nlinarith)
    simp only [hf]; linarith
  have hinj : Set.InjOn (fun p : Nat.Primes => (p : ℕ)) ((fun p : Nat.Primes => (p : ℕ)) ⁻¹' ↑T) :=
    fun a _ b _ h => Subtype.ext h
  set S : Finset Nat.Primes := T.preimage (fun p : Nat.Primes => (p : ℕ)) hinj with hS
  have hg1 : ∀ p ∉ S, g p = 1 := fun p hp => by
    have hpT : (p : ℕ) ∉ T := fun h => hp (Finset.mem_preimage.2 h)
    simp only [hg, hTN p p.2 hpT]
    exact div_self (hf0 p)
  have hprod : HasProd (fun p : Nat.Primes => f p * g p) (6 / Real.pi ^ 2 * ∏ p ∈ S, g p) :=
    hasProd_one_sub_inv_sq.mul (hasProd_prod_of_ne_finset_one hg1)
  have hfg : (fun p : Nat.Primes => f p * g p) = fun p : Nat.Primes => delta p N := funext fun p => by
    simp only [hg]; field_simp [hf0 p]
  rw [hfg] at hprod
  convert hprod using 1
  -- the finite product
  have hTp : ∀ q ∈ T, q.Prime := fun q hq => by
    rcases mem_insert.1 hq with rfl | hq
    · exact Nat.prime_two
    · exact Nat.prime_of_mem_primeFactors hq
  have hSprod : ∏ p ∈ S, g p = ∏ q ∈ T, delta q N / (1 - (q : ℝ)⁻¹ ^ 2) :=
    prod_preimage (fun p : Nat.Primes => (p : ℕ)) T hinj (fun q => delta q N / (1 - (q : ℝ)⁻¹ ^ 2))
      fun q hq hnr => absurd ⟨⟨q, hTp q hq⟩, rfl⟩ hnr
  have h2T : (2 : ℕ) ∉ m.primeFactors := fun h => hm2 (Nat.dvd_of_mem_primeFactors h)
  rw [hSprod, hT, prod_insert h2T]
  -- the density at `2`
  have hv2 : padicValNat 2 N = k := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [hN, padicValNat.mul (pow_ne_zero _ two_ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm2, add_zero]
  rw [delta_two hn, hv2]
  -- the odd primes: `∏ (1 + q⁻¹ + ⋯ + q^{−v}) = σ(m)/m`
  have hodd : ∏ q ∈ m.primeFactors, delta q N / (1 - (q : ℝ)⁻¹ ^ 2) =
      (ArithmeticFunction.sigma 1 m : ℝ) / m := by
    have hσ : (ArithmeticFunction.sigma 1 m : ℝ) =
        ∏ q ∈ m.primeFactors, ∑ i ∈ range (m.factorization q + 1), (q : ℝ) ^ i := by
      rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization _
        ArithmeticFunction.isMultiplicative_sigma hm0, Nat.prod_factorization_eq_prod_primeFactors]
      push_cast
      refine prod_congr rfl fun q hq => ?_
      rw [ArithmeticFunction.sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hq)]
      push_cast; rfl
    have hmprod : (m : ℝ) = ∏ q ∈ m.primeFactors, (q : ℝ) ^ m.factorization q := by
      conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hm0]
      push_cast; rfl
    rw [hσ, hmprod, ← prod_div_distrib]
    refine prod_congr rfl fun q hqm => ?_
    have hq := Nat.prime_of_mem_primeFactors hqm
    have hq2 : q ≠ 2 := fun h => h2T (h ▸ hqm)
    have : Fact q.Prime := ⟨hq⟩
    have hvq : padicValNat q N = m.factorization q := by
      rw [hN, padicValNat.mul (pow_ne_zero _ two_ne_zero) hm0,
        padicValNat.eq_zero_of_not_dvd (fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1
          (hq.dvd_of_dvd_pow h))), zero_add, Nat.factorization_def m hq]
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hf0' : 1 - (q : ℝ)⁻¹ ^ 2 ≠ 0 := by
      have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.two_le
      have : (q : ℝ)⁻¹ ^ 2 < 1 := by rw [inv_pow]; exact inv_lt_one_of_one_lt₀ (by nlinarith)
      linarith
    rw [delta_odd hq hq2 hn, hvq, mul_div_cancel_left₀ _ hf0']
    -- `Σ_{i ≤ v} q^{−i} = (Σ_{i ≤ v} q^i)/q^v`
    set v := m.factorization q
    rw [eq_div_iff (pow_ne_zero _ hq0), sum_mul, ← sum_range_reflect]
    refine sum_congr rfl fun i hi => ?_
    have hiv : i ≤ v := Nat.lt_succ_iff.1 (mem_range.1 hi)
    rw [inv_pow, ← div_eq_inv_mul, div_eq_iff (pow_ne_zero _ hq0), ← pow_add]
    congr 1
    omega
  rw [hodd]
  -- assemble with `r₄(2^k m) = (8 or 24)σ(m)`
  rw [FourSquareTeeth.r4_two_pow_mul hm]
  have hm0' : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
  have hpi : Real.pi ^ 2 ≠ 0 := by positivity
  rw [hN]
  split_ifs with hk
  · subst hk; push_cast; field_simp; ring
  · push_cast; field_simp; ring

end SiegelFour

#print axioms SiegelFour.localCount_eq_card
#print axioms SiegelFour.localCount_succ
#print axioms SiegelFour.tendsto_delta
#print axioms SiegelFour.delta_odd
#print axioms SiegelFour.delta_two
#print axioms SiegelFour.siegel
