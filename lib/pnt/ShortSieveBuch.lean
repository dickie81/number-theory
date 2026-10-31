import ShortSieveNode

/-!
# Buchstab's identity and role reversals for the terms of the certificate

Li's decomposition takes a term apart in two ways.

* **Buchstab's identity** on a rough item `ρ_{i₀}` (free of primes below `P = p_{s(i₀)}`): with a lower level `z ≤ P`,
  `ρ` is free of primes below `z` exactly when it is free of primes below `P`, or its least prime factor `p'` lies in
  `[z, P)`, and then `ρ = p' ρ'` with `ρ'` free of primes below `p'`.
* **A role reversal** on a prime `p₀`: a number `v ≥ z ≥ 2` free of primes below `z` is a prime, or `v = p β` with
  `p` its least prime factor, `p ≥ z` and `β ≥ p` free of primes below `p`.

On nodes (`ShortSieveNode.Node`) they are exact identities between counts, in `ℕ`: the term with the lower level
(`JNode`, a Type I term) is the node plus its child.

* `count_buchstab`: `(N.toJ i₀ a b).count = N.count + (N.buch i₀ a b).count`, with the level `x^a ∏ p_j^{−b_j}`;
* `count_rev`: `(revJ ...).count = (revParent ...).count + (revChild ...).count`, the prime `p₀` becoming a rough item
  free of primes below the level.
-/

open Finset Real

namespace ShortSieveBuch

open ShortSieveNode ShortSieveExpand

open Classical

/-! ### The identities at one number -/

/-- A number is free of primes below `p` exactly when its quotient by the prime `p` is. -/
theorem rough_div_iff {p n : ℕ} (hp : p.Prime) (hd : p ∣ n) :
    SieveTree.rough p (n / p) ↔ SieveTree.rough p n := by
  obtain ⟨c, rfl⟩ := hd
  rw [Nat.mul_div_cancel_left c hp.pos]
  constructor
  · intro h r hr hrp hdiv
    rcases (Nat.Prime.dvd_mul hrp).1 hdiv with h1 | h1
    · rw [(Nat.prime_dvd_prime_iff_eq hrp hp).1 h1] at hr
      exact Nat.lt_irrefl _ hr
    · exact h r hr hrp h1
  · intro h r hr hrp hdiv
    exact h r hr hrp (dvd_mul_of_dvd_right hdiv p)

/-- For `n ≥ 2`, a prime `p` divides `n` with `n/p` free of primes below `p` exactly when `p` is `n`'s least prime
factor. -/
theorem dvd_rough_div_iff {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n) :
    p ∣ n ∧ SieveTree.rough p (n / p) ↔ p = Nat.minFac n := by
  constructor
  · rintro ⟨hd, hr⟩
    rw [rough_div_iff hp hd] at hr
    have h1 := Nat.minFac_le_of_dvd hp.two_le hd
    have h2 := (SieveStops2.rough_iff_le_minFac hn).1 hr
    omega
  · rintro rfl
    refine ⟨Nat.minFac_dvd n, (rough_div_iff hp (Nat.minFac_dvd n)).2 ?_⟩
    exact (SieveStops2.rough_iff_le_minFac hn).2 le_rfl

/-- `1` is free of primes below any level. -/
theorem rough_one (z : ℕ) : SieveTree.rough z 1 := fun _ _ hp hd => hp.one_lt.ne' (Nat.dvd_one.1 hd)


/-! ### Type I terms, and the level conditions -/

/-- A Type I term: `k` primes and `m` rough items with log-linear conditions, as in a `Node`, except that an item `i`
with `s i = none` is free of primes below the level `x^a ∏ p_j^{−b_j}` instead of below a prime. -/
structure JNode where
  k : ℕ
  m : ℕ
  s : Fin m → Option (Fin k)
  a : ℝ
  b : Fin k → ℝ
  conds : List (Cond k m)

/-- The level `⌈x^a ∏ p_j^{−b_j}⌉`. -/
noncomputable def lvlOf {k : ℕ} (a : ℝ) (b : Fin k → ℝ) (x : ℝ) (p : Fin k → ℕ) : ℕ :=
  ⌈x ^ a * ∏ j, (p j : ℝ) ^ (-b j)⌉₊

/-- The sifting conditions of a Type I term: each item free of primes below its prime, or below the level. -/
def JNode.Sifted (J : JNode) (x : ℝ) (v : (Fin J.k → ℕ) × (Fin J.m → ℕ)) : Prop :=
  ∀ i, SieveTree.rough ((J.s i).elim (lvlOf J.a J.b x v.1) v.1) (v.2 i)

/-- The Type I term's count in `(x − y, x]`. -/
noncomputable def JNode.count (J : JNode) (x y : ℝ) : ℕ :=
  #{v ∈ pairs J.k J.m ⌊x⌋₊ | J.Sifted x v ∧ (∀ C ∈ J.conds, C.Holds x v.1 v.2) ∧
    x - y < (prodP v : ℝ) ∧ (prodP v : ℝ) ≤ x}

/-- The level condition on a new last prime: `p_{last} ≥ x^a ∏_{j<k} p_j^{−b_j}`, as
`−Σ_j b_j log p_j − log p_{last} ≤ −a log x`. -/
noncomputable def lvlCond {k m : ℕ} (a : ℝ) (b : Fin k → ℝ) : Cond (k + 1) m :=
  ⟨Fin.snoc (fun j => -b j) (-1), fun _ => 0, fun x => -(a * Real.log x), false⟩

/-- The order condition `p_{last} < p_t`: `log p_{last} − log p_t < 0`. -/
def ltCond {k m : ℕ} (t : Fin k) : Cond (k + 1) m :=
  ⟨fun j => (if j = Fin.last k then 1 else 0) - (if j = t.castSucc then 1 else 0), fun _ => 0, fun _ => 0, true⟩

/-- `log` of the level's argument: `log(x^a ∏ p_j^{−b_j}) = a log x − Σ_j b_j log p_j`. -/
theorem log_lvl {k : ℕ} (a : ℝ) (b : Fin k → ℝ) {x : ℝ} (hx : 0 < x) {p : Fin k → ℕ} (hp : ∀ j, 0 < p j) :
    Real.log (x ^ a * ∏ j, (p j : ℝ) ^ (-b j)) = a * Real.log x - ∑ j, b j * Real.log (p j) := by
  have hp' : ∀ j, (0 : ℝ) < p j := fun j => by exact_mod_cast hp j
  rw [Real.log_mul (Real.rpow_pos_of_pos hx a).ne' (prod_pos fun j _ => Real.rpow_pos_of_pos (hp' j) _).ne',
    Real.log_rpow hx, Real.log_prod (fun j _ => (Real.rpow_pos_of_pos (hp' j) _).ne')]
  simp only [Real.log_rpow (hp' _), neg_mul, sum_neg_distrib]
  ring

/-- A number is at least the level exactly when its `log` is at least `a log x − Σ_j b_j log p_j`. -/
theorem lvlOf_le_iff {k : ℕ} (a : ℝ) (b : Fin k → ℝ) {x : ℝ} (hx : 0 < x) {p : Fin k → ℕ} (hp : ∀ j, 0 < p j)
    {q : ℕ} (hq : 0 < q) :
    lvlOf a b x p ≤ q ↔ a * Real.log x - ∑ j, b j * Real.log (p j) ≤ Real.log q := by
  have hp' : ∀ j, (0 : ℝ) < p j := fun j => by exact_mod_cast hp j
  have hpos : 0 < x ^ a * ∏ j, (p j : ℝ) ^ (-b j) :=
    mul_pos (Real.rpow_pos_of_pos hx a) (prod_pos fun j _ => Real.rpow_pos_of_pos (hp' j) _)
  rw [lvlOf, Nat.ceil_le, ← log_lvl a b hx hp, Real.log_le_log_iff hpos (by exact_mod_cast hq)]

/-- The level condition holds exactly when the new prime is at least the level. -/
theorem holds_lvlCond {k m : ℕ} (a : ℝ) (b : Fin k → ℝ) {x : ℝ} (hx : 0 < x) {p : Fin k → ℕ} (hp : ∀ j, 0 < p j)
    {q : ℕ} (hq : 0 < q) (ρ : Fin m → ℕ) :
    (lvlCond a b : Cond (k + 1) m).Holds x (Fin.snoc p q) ρ ↔ lvlOf a b x p ≤ q := by
  rw [lvlOf_le_iff a b hx hp hq]
  unfold Cond.Holds Cond.val lvlCond
  simp only [Bool.false_eq_true, ite_false, zero_mul, sum_const_zero, add_zero, Fin.sum_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last, neg_mul, one_mul, sum_neg_distrib]
  constructor <;> intro h <;> linarith

/-- The order condition holds exactly when the new prime is below `p_t`. -/
theorem holds_ltCond {k m : ℕ} (t : Fin k) (x : ℝ) {p : Fin k → ℕ} (hp : ∀ j, 0 < p j) {q : ℕ} (hq : 0 < q)
    (ρ : Fin m → ℕ) : (ltCond t : Cond (k + 1) m).Holds x (Fin.snoc p q) ρ ↔ q < p t := by
  unfold Cond.Holds Cond.val ltCond
  simp only [ite_true, zero_mul, sum_const_zero, add_zero]
  rw [val_diff, sub_neg, Fin.snoc_last, Fin.snoc_castSucc, Real.log_lt_log_iff (by exact_mod_cast hq)
    (by exact_mod_cast hp t), Nat.cast_lt]

/-! ### Splitting an item -/

/-- A condition after the item `i₀` is written `p_{last} ρ'_{i₀}`: `f_{i₀} log ρ_{i₀}` becomes
`f_{i₀} log p_{last} + f_{i₀} log ρ'_{i₀}`. -/
def _root_.ShortSieveNode.Cond.split {k m : ℕ} (C : Cond k m) (i₀ : Fin m) : Cond (k + 1) m :=
  ⟨Fin.snoc C.e (C.f i₀), C.f, C.b, C.strict⟩

/-- `Σ_i f_i log ρ'_i` with one entry changed. -/
theorem sum_log_update {m : ℕ} (f : Fin m → ℝ) (ρ : Fin m → ℕ) (i₀ : Fin m) (r : ℕ) :
    ∑ i, f i * Real.log (Function.update ρ i₀ r i) =
      f i₀ * Real.log r + ∑ i ∈ univ \ {i₀}, f i * Real.log (ρ i) := by
  rw [sum_eq_add_sum_sdiff_singleton i₀ _ (fun h => absurd (mem_univ _) h), Function.update_self]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (by simpa using hi)]

/-- The split condition's value at the split pair is the condition's value. -/
theorem val_split {k m : ℕ} (C : Cond k m) (i₀ : Fin m) (p : Fin k → ℕ) (ρ : Fin m → ℕ) {q r : ℕ} (hq : 0 < q)
    (hr : 0 < r) (h : ρ i₀ = q * r) :
    (C.split i₀).val (Fin.snoc p q) (Function.update ρ i₀ r) = C.val p ρ := by
  unfold Cond.val Cond.split
  simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  rw [sum_log_update, sum_eq_add_sum_sdiff_singleton i₀ (fun i => C.f i * Real.log (ρ i))
    (fun h => absurd (mem_univ _) h), h,
    Nat.cast_mul, Real.log_mul (by exact_mod_cast hq.ne') (by exact_mod_cast hr.ne')]
  ring

theorem holds_split {k m : ℕ} (C : Cond k m) (i₀ : Fin m) (x : ℝ) (p : Fin k → ℕ) (ρ : Fin m → ℕ) {q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) (h : ρ i₀ = q * r) :
    (C.split i₀).Holds x (Fin.snoc p q) (Function.update ρ i₀ r) ↔ C.Holds x p ρ := by
  unfold Cond.Holds
  rw [val_split C i₀ p ρ hq hr h]
  rfl

/-- The product of a split pair. -/
theorem prodP_split {k m : ℕ} (p : Fin k → ℕ) (ρ : Fin m → ℕ) (i₀ : Fin m) {q r : ℕ} (h : ρ i₀ = q * r) :
    prodP ((Fin.snoc p q : Fin (k + 1) → ℕ), Function.update ρ i₀ r) = prodP (p, ρ) := by
  unfold prodP
  simp only
  rw [Fin.prod_univ_castSucc, prod_update_of_mem (mem_univ i₀),
    prod_eq_mul_prod_sdiff_singleton i₀ ρ (fun h => absurd (mem_univ _) h), h]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- A pair of `pairs k m Y`. -/
theorem mem_pairs {k m Y : ℕ} {v : (Fin k → ℕ) × (Fin m → ℕ)} :
    v ∈ pairs k m Y ↔ (∀ a, v.1 a ≤ Y ∧ (v.1 a).Prime) ∧ ∀ i, 1 ≤ v.2 i ∧ v.2 i ≤ Y := by
  simp only [pairs, mem_product, Fintype.mem_piFinset, SieveTypeIIU.mem_primesLe, mem_Icc]

/-- `Finset.mem_filter` with the decidability instance found by unification, not synthesis. -/
theorem mem_filter_inst {α : Type*} {s : Finset α} {p : α → Prop} {ip : DecidablePred p} {a : α} :
    a ∈ @Finset.filter α p ip s ↔ a ∈ s ∧ p a := @Finset.mem_filter α p ip s a

/-- Free of primes below `P` implies free of primes below `z ≤ P`. -/
theorem rough_mono {z P n : ℕ} (h : SieveTree.rough P n) (hzP : z ≤ P) : SieveTree.rough z n :=
  fun p hp => h p (lt_of_lt_of_le hp hzP)

/-! ### Buchstab's identity on a node -/

/-- **The Buchstab child** of a node at the item `i₀`, with the level `x^a ∏ p_j^{−b_j}`: one more prime
`p_{last} ∈ [x^a ∏ p_j^{−b_j}, p_{s(i₀)})`, the item `i₀` free of primes below it, and the node's conditions with
`ρ_{i₀} = p_{last} ρ'_{i₀}`. -/
@[reducible] noncomputable def _root_.ShortSieveNode.Node.buch (N : Node) (i₀ : Fin N.m) (a : ℝ) (b : Fin N.k → ℝ) :
    Node where
  k := N.k + 1
  m := N.m
  s := Function.update (fun i => (N.s i).castSucc) i₀ (Fin.last N.k)
  conds := N.conds.map (Cond.split · i₀) ++ [lvlCond a b, ltCond (N.s i₀)]

/-- **The Type I term** of a Buchstab step: the node with the item `i₀` free of primes below the level. -/
@[reducible] def _root_.ShortSieveNode.Node.toJ (N : Node) (i₀ : Fin N.m) (a : ℝ) (b : Fin N.k → ℝ) : JNode :=
  ⟨N.k, N.m, Function.update (fun i => some (N.s i)) i₀ none, a, b, N.conds⟩


/-- The sifting conditions of a Buchstab step's Type I term: the node's, except the item `i₀` below the level. -/
theorem sifted_toJ_iff (N : Node) (i₀ : Fin N.m) (a : ℝ) (b : Fin N.k → ℝ) (x : ℝ)
    (v : (Fin N.k → ℕ) × (Fin N.m → ℕ)) :
    (N.toJ i₀ a b).Sifted x v ↔
      (∀ i, i ≠ i₀ → SieveTree.rough (v.1 (N.s i)) (v.2 i)) ∧ SieveTree.rough (lvlOf a b x v.1) (v.2 i₀) := by
  show (∀ i, SieveTree.rough ((Function.update (fun i => some (N.s i)) i₀ none i).elim (lvlOf a b x v.1) v.1)
    (v.2 i)) ↔ _
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · have := h i
      rwa [Function.update_of_ne hi] at this
    · have := h i₀
      rwa [Function.update_self] at this
  · rintro ⟨h1, h2⟩ i
    by_cases hi : i = i₀
    · subst hi
      rw [Function.update_self]
      exact h2
    · rw [Function.update_of_ne hi]
      exact h1 i hi

/-- The product of two entries of a pair of positive numbers, one prime and one item, is at most its product. -/
theorem mul_le_prodP {k m : ℕ} {v : (Fin k → ℕ) × (Fin m → ℕ)} (h1 : ∀ a, 0 < v.1 a) (h2 : ∀ i, 0 < v.2 i)
    (a : Fin k) (i : Fin m) : v.1 a * v.2 i ≤ prodP v :=
  Nat.mul_le_mul (le_prod_of_pos h1 a) (le_prod_of_pos h2 i)

/-- The Buchstab child's count, over pairs typed as `k + 1` primes. -/
theorem count_buch_eq (N : Node) (i₀ : Fin N.m) (a : ℝ) (b : Fin N.k → ℝ) (x y : ℝ) :
    (N.buch i₀ a b).count x y = #((pairs (N.k + 1) N.m ⌊x⌋₊).filter fun w : (Fin (N.k + 1) → ℕ) × (Fin N.m → ℕ) =>
      (∀ i, SieveTree.rough (w.1 ((N.buch i₀ a b).s i)) (w.2 i)) ∧ (N.buch i₀ a b).InI x y w.1 w.2) := by
  unfold Node.count
  refine card_nbij' (fun w => w) (fun w => w) ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) <;>
  · intro w hw
    exact mem_coe.2 (mem_filter_inst.2 (mem_filter_inst.1 (mem_coe.1 hw)))

/-- The Type I term's count, over pairs typed as the node's. -/
theorem count_toJ_eq (N : Node) (i₀ : Fin N.m) (a : ℝ) (b : Fin N.k → ℝ) (x y : ℝ) :
    (N.toJ i₀ a b).count x y = #((pairs N.k N.m ⌊x⌋₊).filter fun v : (Fin N.k → ℕ) × (Fin N.m → ℕ) =>
      (N.toJ i₀ a b).Sifted x v ∧ (∀ C ∈ N.conds, C.Holds x v.1 v.2) ∧
        x - y < (prodP v : ℝ) ∧ (prodP v : ℝ) ≤ x) := by
  unfold JNode.count
  refine card_nbij' (fun v => v) (fun v => v) ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) <;>
  · intro v hv
    exact mem_coe.2 (mem_filter_inst.2 (mem_filter_inst.1 (mem_coe.1 hv)))

/-- **Buchstab's identity on a node.** When the level is at most `p_{s(i₀)}` at the node's pairs, the Type I term (the
item `i₀` free of primes below the level) is the node plus its Buchstab child: a pair whose item `i₀` has a prime
factor in `[level, p_{s(i₀)})` is the child's pair with `p_{last}` its least prime factor. -/
theorem count_buchstab (N : Node) (i₀ : Fin N.m) (a : ℝ) (b : Fin N.k → ℝ) {x : ℝ} (hx : 0 < x) (y : ℝ)
    (hlvl : ∀ v ∈ pairs N.k N.m ⌊x⌋₊, (∀ C ∈ N.conds, C.Holds x v.1 v.2) → lvlOf a b x v.1 ≤ v.1 (N.s i₀)) :
    (N.toJ i₀ a b).count x y = N.count x y + (N.buch i₀ a b).count x y := by
  rw [count_toJ_eq, count_buch_eq, Node.count,
    ← card_filter_add_card_filter_not (fun v : (Fin N.k → ℕ) × (Fin N.m → ℕ) =>
      SieveTree.rough (v.1 (N.s i₀)) (v.2 i₀))]
  congr 1
  · -- the pairs with the item free of primes below `p_{s(i₀)}` are the node's
    congr 1
    ext v
    rw [mem_filter_inst, mem_filter_inst, mem_filter_inst]
    constructor
    · rintro ⟨⟨hv, hsf, hc, h1, h2⟩, hr⟩
      obtain ⟨hs, -⟩ := (sifted_toJ_iff N i₀ a b x v).1 hsf
      refine ⟨hv, fun i => ?_, hc, h1, h2⟩
      by_cases hi : i = i₀
      · subst hi; exact hr
      · exact hs i hi
    · rintro ⟨hv, hs, hc, h1, h2⟩
      exact ⟨⟨hv, (sifted_toJ_iff N i₀ a b x v).2 ⟨fun i _ => hs i, rough_mono (hs i₀) (hlvl v hv hc)⟩, hc, h1,
        h2⟩, hs i₀⟩
  · -- the others are the child's pairs
    refine card_nbij' (fun v => ((Fin.snoc v.1 (Nat.minFac (v.2 i₀)) : Fin (N.k + 1) → ℕ),
        Function.update v.2 i₀ (v.2 i₀ / Nat.minFac (v.2 i₀))))
      (fun w => (Fin.init w.1, Function.update w.2 i₀ (w.1 (Fin.last N.k) * w.2 i₀))) ?_ ?_ ?_ ?_
    · -- into the child's pairs
      intro v hv
      rw [mem_coe, mem_filter_inst, mem_filter_inst] at hv
      obtain ⟨⟨hvp, hsf, hc, h1, h2⟩, hr⟩ := hv
      obtain ⟨hs, hz⟩ := (sifted_toJ_iff N i₀ a b x v).1 hsf
      obtain ⟨hp, hρ⟩ := mem_pairs.1 hvp
      have hP := hlvl v hvp hc
      have hρ1 : v.2 i₀ ≠ 1 := fun h => hr (h ▸ rough_one _)
      have hρ2 : 2 ≤ v.2 i₀ := by have := (hρ i₀).1; omega
      have hq : (Nat.minFac (v.2 i₀)).Prime := Nat.minFac_prime hρ1
      have hzq : lvlOf a b x v.1 ≤ Nat.minFac (v.2 i₀) := (SieveStops2.rough_iff_le_minFac hρ2).1 hz
      have hqP : Nat.minFac (v.2 i₀) < v.1 (N.s i₀) :=
        not_le.1 fun h => hr ((SieveStops2.rough_iff_le_minFac hρ2).2 h)
      have hqd : Nat.minFac (v.2 i₀) ∣ v.2 i₀ := Nat.minFac_dvd _
      have hqr := (dvd_rough_div_iff hq hρ2).2 rfl
      have hsplit : v.2 i₀ = Nat.minFac (v.2 i₀) * (v.2 i₀ / Nat.minFac (v.2 i₀)) :=
        (Nat.mul_div_cancel' hqd).symm
      have hdiv1 : 1 ≤ v.2 i₀ / Nat.minFac (v.2 i₀) := Nat.div_pos (Nat.minFac_le (by omega)) hq.pos
      have hp0 : ∀ j, 0 < v.1 j := fun j => (hp j).2.pos
      rw [mem_coe, mem_filter_inst]
      dsimp only
      refine ⟨mem_pairs.2 ⟨fun j => ?_, fun i => ?_⟩, fun i => ?_, fun C hC => ?_, ?_⟩
      · induction j using Fin.lastCases with
        | last => simp only [Fin.snoc_last]; exact ⟨(Nat.minFac_le (by omega)).trans (hρ i₀).2, hq⟩
        | cast j => simp only [Fin.snoc_castSucc]; exact hp j
      · dsimp only
        by_cases hi : i = i₀
        · subst hi
          rw [Function.update_self]
          exact ⟨hdiv1, (Nat.div_le_self _ _).trans (hρ i).2⟩
        · rw [Function.update_of_ne hi]; exact hρ i
      · show SieveTree.rough ((Fin.snoc v.1 (Nat.minFac (v.2 i₀)) : Fin (N.k + 1) → ℕ)
          (Function.update (fun i => (N.s i).castSucc) i₀ (Fin.last N.k) i))
          (Function.update v.2 i₀ (v.2 i₀ / Nat.minFac (v.2 i₀)) i)
        by_cases hi : i = i₀
        · subst hi
          simp only [Function.update_self, Fin.snoc_last]
          exact hqr.2
        · simp only [Function.update_of_ne hi, Fin.snoc_castSucc]
          exact hs i hi
      · simp only [Node.buch, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hC
        rcases hC with ⟨C', hC', rfl⟩ | rfl | rfl
        · exact (holds_split C' i₀ x v.1 v.2 hq.pos hdiv1 hsplit).2 (hc C' hC')
        · exact (holds_lvlCond a b hx hp0 hq.pos _).2 hzq
        · exact (holds_ltCond (N.s i₀) x hp0 hq.pos _).2 hqP
      · rw [prodP_split v.1 v.2 i₀ hsplit]
        exact ⟨h1, h2⟩
    · -- into the pairs not free of primes below `p_{s(i₀)}`
      intro w hw
      rw [mem_coe, mem_filter_inst] at hw
      obtain ⟨hwp, hs', hc', h1, h2⟩ := hw
      have hs : ∀ i, SieveTree.rough (w.1 (Function.update (fun i => (N.s i).castSucc) i₀ (Fin.last N.k) i))
          (w.2 i) := hs'
      have hc : ∀ C ∈ N.conds.map (Cond.split · i₀) ++ [lvlCond a b, ltCond (N.s i₀)], C.Holds x w.1 w.2 := hc'
      obtain ⟨hp, hρ⟩ := mem_pairs.1 hwp
      have hq : (w.1 (Fin.last N.k)).Prime := (hp _).2
      have hs₀ : SieveTree.rough (w.1 (Fin.last N.k)) (w.2 i₀) := by
        have := hs i₀
        rwa [Function.update_self] at this
      have hsi : ∀ i, i ≠ i₀ → SieveTree.rough (w.1 (N.s i).castSucc) (w.2 i) := fun i hi => by
        have := hs i
        rwa [Function.update_of_ne hi] at this
      have hp0 : ∀ j, 0 < Fin.init w.1 j := fun j => (hp _).2.pos
      have hw1 : 1 ≤ w.2 i₀ := (hρ i₀).1
      have hwq : (Fin.snoc (Fin.init w.1) (w.1 (Fin.last N.k)) : Fin (N.k + 1) → ℕ) = w.1 := Fin.snoc_init_self w.1
      have hwu : Function.update (Function.update w.2 i₀ (w.1 (Fin.last N.k) * w.2 i₀)) i₀ (w.2 i₀) = w.2 := by
        rw [Function.update_idem, Function.update_eq_self]
      have hsplit : Function.update w.2 i₀ (w.1 (Fin.last N.k) * w.2 i₀) i₀ = w.1 (Fin.last N.k) * w.2 i₀ :=
        Function.update_self _ _ _
      -- the conditions, at the pair written as a split pair
      have hcond : ∀ C ∈ N.conds.map (Cond.split · i₀) ++ [lvlCond a b, ltCond (N.s i₀)],
          C.Holds x (Fin.snoc (Fin.init w.1) (w.1 (Fin.last N.k)))
            (Function.update (Function.update w.2 i₀ (w.1 (Fin.last N.k) * w.2 i₀)) i₀ (w.2 i₀)) := by
        rw [hwq, hwu]; exact hc
      have hzq : lvlOf a b x (Fin.init w.1) ≤ w.1 (Fin.last N.k) :=
        (holds_lvlCond a b hx hp0 hq.pos _).1 (hcond _ (by simp))
      have hqP : w.1 (Fin.last N.k) < Fin.init w.1 (N.s i₀) :=
        (holds_ltCond (N.s i₀) x hp0 hq.pos _).1 (hcond _ (by simp))
      have hrq : SieveTree.rough (w.1 (Fin.last N.k)) (w.1 (Fin.last N.k) * w.2 i₀) := by
        rw [← rough_div_iff hq (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hq.pos]
        exact hs₀
      have hprod : prodP (Fin.init w.1, Function.update w.2 i₀ (w.1 (Fin.last N.k) * w.2 i₀)) = prodP w := by
        rw [← prodP_split (Fin.init w.1) (Function.update w.2 i₀ (w.1 (Fin.last N.k) * w.2 i₀)) i₀ hsplit, hwq,
          hwu]
      have hpos : ∀ i, 0 < w.2 i := fun i => (hρ i).1
      have hle : w.1 (Fin.last N.k) * w.2 i₀ ≤ ⌊x⌋₊ := by
        have := mul_le_prodP (v := w) (fun j => (hp j).2.pos) hpos (Fin.last N.k) i₀
        refine Nat.le_floor ?_
        calc ((w.1 (Fin.last N.k) * w.2 i₀ : ℕ) : ℝ) ≤ (prodP w : ℝ) := by exact_mod_cast this
          _ ≤ x := h2
      rw [mem_coe, mem_filter_inst, mem_filter_inst, sifted_toJ_iff]
      dsimp only
      refine ⟨⟨mem_pairs.2 ⟨fun j => hp _, fun i => ?_⟩, ⟨fun i hi => ?_, ?_⟩, fun C hC => ?_, ?_, ?_⟩, ?_⟩
      · dsimp only
        by_cases hi : i = i₀
        · subst hi; rw [Function.update_self]
          exact ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hq.ne_zero (by omega)), hle⟩
        · rw [Function.update_of_ne hi]; exact hρ i
      · rw [Function.update_of_ne hi]; exact hsi i hi
      · rw [Function.update_self]; exact rough_mono hrq hzq
      · exact (holds_split C i₀ x _ _ hq.pos hw1 hsplit).1
          (hcond _ (List.mem_append_left _ (List.mem_map.2 ⟨C, hC, rfl⟩)))
      · rw [hprod]; exact h1
      · rw [hprod]; exact h2
      · rw [Function.update_self]
        exact fun h => h _ hqP hq (dvd_mul_right _ _)
    · -- left inverse
      intro v hv
      simp only [Fin.init_snoc, Fin.snoc_last, Function.update_self, Function.update_idem]
      rw [Nat.mul_div_cancel' (Nat.minFac_dvd _), Function.update_eq_self]
    · -- right inverse
      intro w hw
      rw [mem_coe, mem_filter_inst] at hw
      obtain ⟨hwp, hs', -⟩ := hw
      have hs : ∀ i, SieveTree.rough (w.1 (Function.update (fun i => (N.s i).castSucc) i₀ (Fin.last N.k) i))
          (w.2 i) := hs'
      obtain ⟨hp, hρ⟩ := mem_pairs.1 hwp
      have hq : (w.1 (Fin.last N.k)).Prime := (hp _).2
      have hs₀ : SieveTree.rough (w.1 (Fin.last N.k)) (w.2 i₀) := by
        have := hs i₀
        rwa [Function.update_self] at this
      have h2 : 2 ≤ w.1 (Fin.last N.k) * w.2 i₀ :=
        le_trans hq.two_le (Nat.le_mul_of_pos_right _ (hρ i₀).1)
      have hmin : Nat.minFac (w.1 (Fin.last N.k) * w.2 i₀) = w.1 (Fin.last N.k) := by
        refine ((dvd_rough_div_iff hq h2).1 ⟨dvd_mul_right _ _, ?_⟩).symm
        rw [Nat.mul_div_cancel_left _ hq.pos]
        exact hs₀
      simp only [Function.update_self, hmin, Nat.mul_div_cancel_left _ hq.pos, Function.update_idem,
        Function.update_eq_self, Fin.snoc_init_self]


/-! ### Role reversals -/

/-- A condition after the prime `p₀` becomes the last item `v` (the role reversal's Type I term): `e_0 log p₀`
becomes `e_0 log v`. -/
def _root_.ShortSieveNode.Cond.rev {k m : ℕ} (C : Cond (k + 1) m) : Cond k (m + 1) :=
  ⟨Fin.tail C.e, Fin.snoc C.f (C.e 0), C.b, C.strict⟩

/-- A condition after the prime `p₀` is written `p β` (`p` in `p₀`'s place, `β` the last item): `e_0 log p₀` becomes
`e_0 log p + e_0 log β`. -/
def _root_.ShortSieveNode.Cond.revSplit {k m : ℕ} (C : Cond (k + 1) m) : Cond (k + 1) (m + 1) :=
  ⟨C.e, Fin.snoc C.f (C.e 0), C.b, C.strict⟩

theorem val_rev {k m : ℕ} (C : Cond (k + 1) m) (p : Fin k → ℕ) (ρ : Fin m → ℕ) (v : ℕ) :
    C.rev.val p (Fin.snoc ρ v) = C.val (Fin.cons v p) ρ := by
  unfold Cond.val Cond.rev
  rw [Fin.sum_univ_castSucc (n := m), Fin.sum_univ_succ (n := k)]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.cons_zero, Fin.cons_succ, Fin.tail]
  ring

theorem holds_rev {k m : ℕ} (C : Cond (k + 1) m) (x : ℝ) (p : Fin k → ℕ) (ρ : Fin m → ℕ) (v : ℕ) :
    C.rev.Holds x p (Fin.snoc ρ v) ↔ C.Holds x (Fin.cons v p) ρ := by
  unfold Cond.Holds
  rw [val_rev]
  rfl

theorem val_revSplit {k m : ℕ} (C : Cond (k + 1) m) (p : Fin k → ℕ) (ρ : Fin m → ℕ) {q r : ℕ} (hq : 0 < q)
    (hr : 0 < r) : C.revSplit.val (Fin.cons q p) (Fin.snoc ρ r) = C.rev.val p (Fin.snoc ρ (q * r)) := by
  unfold Cond.val Cond.rev Cond.revSplit
  rw [Fin.sum_univ_succ (n := k), Fin.sum_univ_castSucc (n := m), Fin.sum_univ_castSucc (n := m)]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.cons_zero, Fin.cons_succ, Fin.tail]
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hq.ne') (by exact_mod_cast hr.ne')]
  ring

theorem holds_revSplit {k m : ℕ} (C : Cond (k + 1) m) (x : ℝ) (p : Fin k → ℕ) (ρ : Fin m → ℕ) {q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) :
    C.revSplit.Holds x (Fin.cons q p) (Fin.snoc ρ r) ↔ C.rev.Holds x p (Fin.snoc ρ (q * r)) := by
  unfold Cond.Holds
  rw [val_revSplit C p ρ hq hr]
  rfl

/-- The level condition on `p₀`: `p₀ ≥ x^a ∏_j p_{j+1}^{−b_j}`, as `−log p₀ − Σ_j b_j log p_{j+1} ≤ −a log x`. -/
noncomputable def lvlCond0 {k m : ℕ} (a : ℝ) (b : Fin k → ℝ) : Cond (k + 1) m :=
  ⟨Fin.cons (-1) (fun j => -b j), fun _ => 0, fun x => -(a * Real.log x), false⟩

theorem holds_lvlCond0 {k m : ℕ} (a : ℝ) (b : Fin k → ℝ) {x : ℝ} (hx : 0 < x) {p : Fin k → ℕ}
    (hp : ∀ j, 0 < p j) {q : ℕ} (hq : 0 < q) (ρ : Fin m → ℕ) :
    (lvlCond0 a b : Cond (k + 1) m).Holds x (Fin.cons q p) ρ ↔ lvlOf a b x p ≤ q := by
  rw [lvlOf_le_iff a b hx hp hq]
  unfold Cond.Holds Cond.val lvlCond0
  simp only [Bool.false_eq_true, ite_false, zero_mul, sum_const_zero, add_zero, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, neg_mul, one_mul, sum_neg_distrib]
  constructor <;> intro h <;> linarith

/-- The order condition `p₀ ≤ β` of `p₀` and the last item. -/
def geCond0 {k m : ℕ} : Cond (k + 1) (m + 1) :=
  ⟨fun j => if j = 0 then 1 else 0, fun i => if i = Fin.last m then -1 else 0, fun _ => 0, false⟩

theorem holds_geCond0 {k m : ℕ} (x : ℝ) (p : Fin k → ℕ) (ρ : Fin m → ℕ) {q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    (geCond0 : Cond (k + 1) (m + 1)).Holds x (Fin.cons q p) (Fin.snoc ρ r) ↔ q ≤ r := by
  unfold Cond.Holds Cond.val geCond0
  simp only [Bool.false_eq_true, ite_false, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true,
    neg_mul, Fin.cons_zero, Fin.snoc_last]
  rw [← sub_eq_add_neg, sub_nonpos, Real.log_le_log_iff (by exact_mod_cast hq) (by exact_mod_cast hr), Nat.cast_le]

/-- The product after the prime `p₀` becomes the last item. -/
theorem prodP_rev {k m : ℕ} (p : Fin k → ℕ) (ρ : Fin m → ℕ) (v : ℕ) :
    prodP ((Fin.cons v p : Fin (k + 1) → ℕ), ρ) = prodP (p, (Fin.snoc ρ v : Fin (m + 1) → ℕ)) := by
  unfold prodP
  rw [Fin.prod_univ_succ (n := k), Fin.prod_univ_castSucc (n := m)]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- The product after `p₀ = qr`. -/
theorem prodP_revSplit {k m : ℕ} (p : Fin k → ℕ) (ρ : Fin m → ℕ) (q r : ℕ) :
    prodP ((Fin.cons q p : Fin (k + 1) → ℕ), (Fin.snoc ρ r : Fin (m + 1) → ℕ)) =
      prodP (p, (Fin.snoc ρ (q * r) : Fin (m + 1) → ℕ)) := by
  unfold prodP
  rw [Fin.prod_univ_succ (n := k), Fin.prod_univ_castSucc (n := m), Fin.prod_univ_castSucc (n := m)]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- **The role reversal's Type I term** for the node `⟨k + 1, m, s, conds⟩` (no item free of primes below `p₀`):
its prime `p₀` becomes the last item, free of primes below the level `x^a ∏_j p_{j+1}^{−b_j}`. -/
@[reducible] def revJ (k m : ℕ) (s : Fin m → Fin (k + 1)) (hs : ∀ i, s i ≠ 0) (a : ℝ) (b : Fin k → ℝ)
    (conds : List (Cond (k + 1) m)) : JNode :=
  ⟨k, m + 1, Fin.snoc (fun i => some ((s i).pred (hs i))) none, a, b, conds.map Cond.rev⟩

/-- **The role reversal's child**: `p₀ = p β` with `p` at least the level in `p₀`'s place and `β ≥ p` the last
item, free of primes below `p`. -/
@[reducible] noncomputable def revChild (k m : ℕ) (s : Fin m → Fin (k + 1)) (a : ℝ) (b : Fin k → ℝ)
    (conds : List (Cond (k + 1) m)) : Node :=
  ⟨k + 1, m + 1, Fin.snoc s 0, conds.map Cond.revSplit ++ [lvlCond0 a b, geCond0]⟩

theorem sifted_revJ_iff (k m : ℕ) (s : Fin m → Fin (k + 1)) (hs : ∀ i, s i ≠ 0) (a : ℝ) (b : Fin k → ℝ)
    (conds : List (Cond (k + 1) m)) (x : ℝ) (w : (Fin k → ℕ) × (Fin (m + 1) → ℕ)) :
    (revJ k m s hs a b conds).Sifted x w ↔
      (∀ i : Fin m, SieveTree.rough (w.1 ((s i).pred (hs i))) (w.2 i.castSucc)) ∧
        SieveTree.rough (lvlOf a b x w.1) (w.2 (Fin.last m)) := by
  show (∀ i, SieveTree.rough (((Fin.snoc (fun i => some ((s i).pred (hs i))) none : Fin (m + 1) → Option (Fin k))
    i).elim (lvlOf a b x w.1) w.1) (w.2 i)) ↔ _
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · have := h i.castSucc
      rwa [Fin.snoc_castSucc] at this
    · have := h (Fin.last m)
      rwa [Fin.snoc_last] at this
  · rintro ⟨h1, h2⟩ i
    induction i using Fin.lastCases with
    | last => rw [Fin.snoc_last]; exact h2
    | cast i => rw [Fin.snoc_castSucc]; exact h1 i

theorem count_revJ_eq (k m : ℕ) (s : Fin m → Fin (k + 1)) (hs : ∀ i, s i ≠ 0) (a : ℝ) (b : Fin k → ℝ)
    (conds : List (Cond (k + 1) m)) (x y : ℝ) :
    (revJ k m s hs a b conds).count x y = #((pairs k (m + 1) ⌊x⌋₊).filter
      fun w : (Fin k → ℕ) × (Fin (m + 1) → ℕ) => (revJ k m s hs a b conds).Sifted x w ∧
        (∀ C ∈ conds.map Cond.rev, C.Holds x w.1 w.2) ∧ x - y < (prodP w : ℝ) ∧ (prodP w : ℝ) ≤ x) := by
  unfold JNode.count
  refine card_nbij' (fun w => w) (fun w => w) ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) <;>
  · intro w hw
    exact mem_coe.2 (mem_filter_inst.2 (mem_filter_inst.1 (mem_coe.1 hw)))

theorem count_revChild_eq (k m : ℕ) (s : Fin m → Fin (k + 1)) (a : ℝ) (b : Fin k → ℝ)
    (conds : List (Cond (k + 1) m)) (x y : ℝ) :
    (revChild k m s a b conds).count x y = #((pairs (k + 1) (m + 1) ⌊x⌋₊).filter
      fun u : (Fin (k + 1) → ℕ) × (Fin (m + 1) → ℕ) =>
        (∀ i, SieveTree.rough (u.1 ((Fin.snoc s 0 : Fin (m + 1) → Fin (k + 1)) i)) (u.2 i)) ∧
        (revChild k m s a b conds).InI x y u.1 u.2) := by
  unfold Node.count
  refine card_nbij' (fun u => u) (fun u => u) ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) <;>
  · intro u hu
    exact mem_coe.2 (mem_filter_inst.2 (mem_filter_inst.1 (mem_coe.1 hu)))


/-- **The role reversal on a node.** For the node `⟨k + 1, m, s, conds⟩` with no item free of primes below `p₀`,
when the level is at least `2` and at most the last item at the Type I term's pairs that satisfy its conditions, the
Type I term (`p₀` turned into the last item, free of primes below the level) is the node (that item a prime) plus the
role reversal's child (that item composite, `p β` with `p` its least prime factor). -/
theorem count_rev (k m : ℕ) (s : Fin m → Fin (k + 1)) (hs : ∀ i, s i ≠ 0) (a : ℝ) (b : Fin k → ℝ)
    (conds : List (Cond (k + 1) m)) {x : ℝ} (hx : 0 < x) (y : ℝ)
    (hlvl : ∀ w ∈ pairs k (m + 1) ⌊x⌋₊, (∀ C ∈ conds, C.rev.Holds x w.1 w.2) →
      2 ≤ lvlOf a b x w.1 ∧ lvlOf a b x w.1 ≤ w.2 (Fin.last m)) :
    (revJ k m s hs a b conds).count x y =
      (⟨k + 1, m, s, conds⟩ : Node).count x y + (revChild k m s a b conds).count x y := by
  rw [count_revJ_eq, count_revChild_eq, Node.count,
    ← card_filter_add_card_filter_not (fun w : (Fin k → ℕ) × (Fin (m + 1) → ℕ) => (w.2 (Fin.last m)).Prime)]
  congr 1
  · -- the last item prime: the node's pairs
    refine card_nbij' (fun w => ((Fin.cons (w.2 (Fin.last m)) w.1 : Fin (k + 1) → ℕ), Fin.init w.2))
      (fun v => (Fin.tail v.1, (Fin.snoc v.2 (v.1 0) : Fin (m + 1) → ℕ))) ?_ ?_ ?_ ?_
    · intro w hw
      rw [mem_coe, mem_filter_inst, mem_filter_inst] at hw
      obtain ⟨⟨hwp, hsf, hc, h1, h2⟩, hpr⟩ := hw
      obtain ⟨hs1, -⟩ := (sifted_revJ_iff k m s hs a b conds x w).1 hsf
      obtain ⟨hp, hρ⟩ := mem_pairs.1 hwp
      have hw2 : (Fin.snoc (Fin.init w.2) (w.2 (Fin.last m)) : Fin (m + 1) → ℕ) = w.2 := Fin.snoc_init_self _
      have hprod : prodP ((Fin.cons (w.2 (Fin.last m)) w.1 : Fin (k + 1) → ℕ), Fin.init w.2) = prodP w := by
        rw [prodP_rev, hw2]
      rw [mem_coe, mem_filter_inst]
      refine ⟨mem_pairs.2 ⟨fun j => ?_, fun i => ?_⟩, fun i => ?_, ⟨fun C hC => ?_, ?_, ?_⟩⟩
      · dsimp only
        induction j using Fin.cases with
        | zero => rw [Fin.cons_zero]; exact ⟨(hρ _).2, hpr⟩
        | succ j => rw [Fin.cons_succ]; exact hp j
      · exact hρ i.castSucc
      · dsimp only
        rw [← Fin.succ_pred (s i) (hs i), Fin.cons_succ]
        exact hs1 i
      · have := hc C.rev (List.mem_map.2 ⟨C, hC, rfl⟩)
        rw [← hw2, holds_rev] at this
        exact this
      · dsimp only; rw [hprod]; exact h1
      · dsimp only; rw [hprod]; exact h2
    · intro v hv
      rw [mem_coe, mem_filter_inst] at hv
      obtain ⟨hvp, hs', hc, h1, h2⟩ := hv
      obtain ⟨hp, hρ⟩ := mem_pairs.1 hvp
      dsimp only at hs' hc hp hρ
      have hv1 : (Fin.cons (v.1 0) (Fin.tail v.1) : Fin (k + 1) → ℕ) = v.1 := Fin.cons_self_tail _
      have hcr : ∀ C ∈ conds.map Cond.rev, C.Holds x (Fin.tail v.1) (Fin.snoc v.2 (v.1 0)) := by
        intro C hC
        obtain ⟨C', hC', rfl⟩ := List.mem_map.1 hC
        rw [holds_rev, hv1]
        exact hc C' hC'
      have hprod : prodP (Fin.tail v.1, (Fin.snoc v.2 (v.1 0) : Fin (m + 1) → ℕ)) = prodP v := by
        rw [← prodP_rev, hv1]
      have hwp : (Fin.tail v.1, (Fin.snoc v.2 (v.1 0) : Fin (m + 1) → ℕ)) ∈ pairs k (m + 1) ⌊x⌋₊ := by
        refine mem_pairs.2 ⟨fun j => hp _, fun i => ?_⟩
        dsimp only
        induction i using Fin.lastCases with
        | last => rw [Fin.snoc_last]; exact ⟨(hp 0).2.one_lt.le, (hp 0).1⟩
        | cast i => rw [Fin.snoc_castSucc]; exact hρ i
      obtain ⟨-, hzv⟩ := hlvl _ hwp (fun C hC => hcr C.rev (List.mem_map.2 ⟨C, hC, rfl⟩))
      simp only [Fin.snoc_last] at hzv
      rw [mem_coe, mem_filter_inst, mem_filter_inst, sifted_revJ_iff]
      refine ⟨⟨hwp, ⟨fun i => ?_, ?_⟩, hcr, ?_, ?_⟩, ?_⟩
      · dsimp only
        rw [Fin.snoc_castSucc]
        have := hs' i
        rw [← Fin.succ_pred (s i) (hs i)] at this
        exact this
      · dsimp only
        rw [Fin.snoc_last]
        intro r hr hrp hrd
        rw [(Nat.prime_dvd_prime_iff_eq hrp (hp 0).2).1 hrd] at hr
        omega
      · dsimp only; rw [hprod]; exact h1
      · dsimp only; rw [hprod]; exact h2
      · dsimp only; rw [Fin.snoc_last]; exact (hp 0).2
    · intro w _
      simp only [Fin.tail_cons, Fin.cons_zero, Fin.snoc_init_self]
    · intro v _
      simp only [Fin.snoc_last, Fin.cons_self_tail, Fin.init_snoc]
  · -- the last item composite: the child's pairs
    refine card_nbij' (fun w => ((Fin.cons (Nat.minFac (w.2 (Fin.last m))) w.1 : Fin (k + 1) → ℕ),
        (Fin.snoc (Fin.init w.2) (w.2 (Fin.last m) / Nat.minFac (w.2 (Fin.last m))) : Fin (m + 1) → ℕ)))
      (fun u => (Fin.tail u.1, (Fin.snoc (Fin.init u.2) (u.1 0 * u.2 (Fin.last m)) : Fin (m + 1) → ℕ)))
      ?_ ?_ ?_ ?_
    · intro w hw
      rw [mem_coe, mem_filter_inst, mem_filter_inst] at hw
      obtain ⟨⟨hwp, hsf, hc, h1, h2⟩, hpr⟩ := hw
      obtain ⟨hs1, hz⟩ := (sifted_revJ_iff k m s hs a b conds x w).1 hsf
      obtain ⟨hp, hρ⟩ := mem_pairs.1 hwp
      obtain ⟨hz2, hzv⟩ := hlvl w hwp (fun C hC => hc C.rev (List.mem_map.2 ⟨C, hC, rfl⟩))
      have hV2 : 2 ≤ w.2 (Fin.last m) := le_trans hz2 hzv
      have hq : (Nat.minFac (w.2 (Fin.last m))).Prime := Nat.minFac_prime (by omega)
      have hzq : lvlOf a b x w.1 ≤ Nat.minFac (w.2 (Fin.last m)) := (SieveStops2.rough_iff_le_minFac hV2).1 hz
      have hqr := (dvd_rough_div_iff hq hV2).2 rfl
      have hsq : Nat.minFac (w.2 (Fin.last m)) * Nat.minFac (w.2 (Fin.last m)) ≤ w.2 (Fin.last m) := by
        have := Nat.minFac_sq_le_self (by omega) hpr; rwa [sq] at this
      have hqle : Nat.minFac (w.2 (Fin.last m)) ≤ w.2 (Fin.last m) / Nat.minFac (w.2 (Fin.last m)) :=
        (Nat.le_div_iff_mul_le hq.pos).2 hsq
      have hdiv1 : 1 ≤ w.2 (Fin.last m) / Nat.minFac (w.2 (Fin.last m)) := le_trans hq.one_lt.le hqle
      have hqV : Nat.minFac (w.2 (Fin.last m)) * (w.2 (Fin.last m) / Nat.minFac (w.2 (Fin.last m))) =
          w.2 (Fin.last m) := Nat.mul_div_cancel' (Nat.minFac_dvd _)
      have hw2 : (Fin.snoc (Fin.init w.2) (w.2 (Fin.last m)) : Fin (m + 1) → ℕ) = w.2 := Fin.snoc_init_self _
      have hp0 : ∀ j, 0 < w.1 j := fun j => (hp j).2.pos
      rw [mem_coe, mem_filter_inst]
      refine ⟨mem_pairs.2 ⟨fun j => ?_, fun i => ?_⟩, fun i => ?_, ⟨fun C hC => ?_, ?_, ?_⟩⟩
      · dsimp only
        induction j using Fin.cases with
        | zero => rw [Fin.cons_zero]; exact ⟨(Nat.minFac_le (by omega)).trans (hρ _).2, hq⟩
        | succ j => rw [Fin.cons_succ]; exact hp j
      · dsimp only
        induction i using Fin.lastCases with
        | last => rw [Fin.snoc_last]; exact ⟨hdiv1, (Nat.div_le_self _ _).trans (hρ _).2⟩
        | cast i => rw [Fin.snoc_castSucc]; exact hρ i.castSucc
      · dsimp only
        induction i using Fin.lastCases with
        | last => rw [Fin.snoc_last, Fin.snoc_last, Fin.cons_zero]; exact hqr.2
        | cast i =>
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc, ← Fin.succ_pred (s i) (hs i), Fin.cons_succ]
          exact hs1 i
      · simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hC
        rcases hC with ⟨C', hC', rfl⟩ | rfl | rfl
        · rw [holds_revSplit C' x w.1 _ hq.pos hdiv1, hqV, hw2]
          exact hc C'.rev (List.mem_map.2 ⟨C', hC', rfl⟩)
        · exact (holds_lvlCond0 a b hx hp0 hq.pos _).2 hzq
        · exact (holds_geCond0 x w.1 _ hq.pos hdiv1).2 hqle
      · dsimp only; rw [prodP_revSplit, hqV, hw2]; exact h1
      · dsimp only; rw [prodP_revSplit, hqV, hw2]; exact h2
    · intro u hu
      rw [mem_coe, mem_filter_inst] at hu
      obtain ⟨hup, hs', hc, h1, h2⟩ := hu
      obtain ⟨hp, hρ⟩ := mem_pairs.1 hup
      have hq : (u.1 0).Prime := (hp 0).2
      have hp0 : ∀ j, 0 < Fin.tail u.1 j := fun j => (hp _).2.pos
      have hβ1 : 1 ≤ u.2 (Fin.last m) := (hρ _).1
      have hu1 : (Fin.cons (u.1 0) (Fin.tail u.1) : Fin (k + 1) → ℕ) = u.1 := Fin.cons_self_tail _
      have hu2 : (Fin.snoc (Fin.init u.2) (u.2 (Fin.last m)) : Fin (m + 1) → ℕ) = u.2 := Fin.snoc_init_self _
      have hcond : ∀ C ∈ conds.map Cond.revSplit ++ [lvlCond0 a b, geCond0],
          C.Holds x (Fin.cons (u.1 0) (Fin.tail u.1)) (Fin.snoc (Fin.init u.2) (u.2 (Fin.last m))) := by
        rw [hu1, hu2]; exact hc
      have hzq : lvlOf a b x (Fin.tail u.1) ≤ u.1 0 :=
        (holds_lvlCond0 a b hx hp0 hq.pos _).1 (hcond _ (by simp))
      have hqβ : u.1 0 ≤ u.2 (Fin.last m) := (holds_geCond0 x _ _ hq.pos hβ1).1 (hcond _ (by simp))
      have hsβ : SieveTree.rough (u.1 0) (u.2 (Fin.last m)) := by
        have := hs' (Fin.last m)
        rwa [Fin.snoc_last] at this
      have hrq : SieveTree.rough (u.1 0) (u.1 0 * u.2 (Fin.last m)) := by
        rw [← rough_div_iff hq (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hq.pos]
        exact hsβ
      have hprod : prodP (Fin.tail u.1, (Fin.snoc (Fin.init u.2) (u.1 0 * u.2 (Fin.last m)) : Fin (m + 1) → ℕ)) =
          prodP u := by
        rw [← prodP_revSplit, hu1, hu2]
      have hle : u.1 0 * u.2 (Fin.last m) ≤ ⌊x⌋₊ := by
        have := mul_le_prodP (v := u) (fun j => (hp j).2.pos) (fun i => (hρ i).1) 0 (Fin.last m)
        refine Nat.le_floor ?_
        calc ((u.1 0 * u.2 (Fin.last m) : ℕ) : ℝ) ≤ (prodP u : ℝ) := by exact_mod_cast this
          _ ≤ x := h2
      rw [mem_coe, mem_filter_inst, mem_filter_inst, sifted_revJ_iff]
      refine ⟨⟨mem_pairs.2 ⟨fun j => hp _, fun i => ?_⟩, ⟨fun i => ?_, ?_⟩, fun C hC => ?_, ?_, ?_⟩, ?_⟩
      · dsimp only
        induction i using Fin.lastCases with
        | last => rw [Fin.snoc_last]; exact ⟨le_trans hq.one_lt.le (Nat.le_mul_of_pos_right _ hβ1), hle⟩
        | cast i => rw [Fin.snoc_castSucc]; exact hρ i.castSucc
      · dsimp only
        rw [Fin.snoc_castSucc]
        have := hs' i.castSucc
        rw [Fin.snoc_castSucc, ← Fin.succ_pred (s i) (hs i)] at this
        exact this
      · dsimp only
        rw [Fin.snoc_last]
        exact rough_mono hrq hzq
      · obtain ⟨C', hC', rfl⟩ := List.mem_map.1 hC
        rw [← holds_revSplit C' x _ _ hq.pos hβ1]
        exact hcond _ (List.mem_append_left _ (List.mem_map.2 ⟨C', hC', rfl⟩))
      · dsimp only; rw [hprod]; exact h1
      · dsimp only; rw [hprod]; exact h2
      · dsimp only
        rw [Fin.snoc_last]
        exact Nat.not_prime_mul hq.one_lt.ne' (by have := hq.two_le; omega)
    · intro w _
      simp only [Fin.tail_cons, Fin.init_snoc, Fin.cons_zero, Fin.snoc_last,
        Nat.mul_div_cancel' (Nat.minFac_dvd _), Fin.snoc_init_self]
    · intro u hu
      rw [mem_coe, mem_filter_inst] at hu
      obtain ⟨hup, hs', -⟩ := hu
      obtain ⟨hp, hρ⟩ := mem_pairs.1 hup
      have hq : (u.1 0).Prime := (hp 0).2
      have hsβ : SieveTree.rough (u.1 0) (u.2 (Fin.last m)) := by
        have := hs' (Fin.last m)
        rwa [Fin.snoc_last] at this
      have h2 : 2 ≤ u.1 0 * u.2 (Fin.last m) := le_trans hq.two_le (Nat.le_mul_of_pos_right _ (hρ _).1)
      have hmin : Nat.minFac (u.1 0 * u.2 (Fin.last m)) = u.1 0 := by
        refine ((dvd_rough_div_iff hq h2).1 ⟨dvd_mul_right _ _, ?_⟩).symm
        rw [Nat.mul_div_cancel_left _ hq.pos]
        exact hsβ
      simp only [Fin.snoc_last, Fin.init_snoc, hmin, Nat.mul_div_cancel_left _ hq.pos, Fin.cons_self_tail,
        Fin.snoc_init_self]

end ShortSieveBuch

#print axioms ShortSieveBuch.count_buchstab
#print axioms ShortSieveBuch.count_rev
