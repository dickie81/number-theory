import ShortSieveTerm
import ShortSieveExpand
import ShortSieveWit

/-!
# Sieve terms of the certificate and their asymptotic formula

A node of Li's decomposition sums over `k` primes `p` and `m` rough integers `ρ` (`ρ_i` free of primes below
`p_{s(i)}`), with conditions that are log-linear in them: `Σ_a e_a log p_a + Σ_i f_i log ρ_i ≤ b(x)` (`Cond`), such
as the bounds of a box of exponents, the order of the primes, or a rough item larger than a prime. `Node.count` counts
its terms with product in `(x − y, x]`.

* `count_eq_sum`: for large `x`, when the conditions force every prime above `x^c` and every rough item above `1`,
  the count is the sum, over the patterns `len ≥ 1` of numbers of prime factors, of the counts of the expanded tuples
  (`ShortSieveExpand.card_expand`) in the cut of the expanded conditions (`ShortSieveTerm.cut`): the conditions on
  the blocks' primes, the blocks' monotonicity, and every prime of a block at least its sifting prime.
-/

open Finset Real Filter

namespace ShortSieveNode

open ShortSieveBoxes ShortSieveTerm ShortSieveExpand

open Classical

/-! ### Conditions and nodes -/

/-- A log-linear condition on `k` primes and `m` rough items: `Σ_a e_a log p_a + Σ_i f_i log ρ_i ≤ b(x)`, or `< b(x)`
when `strict`. -/
structure Cond (k m : ℕ) where
  e : Fin k → ℝ
  f : Fin m → ℝ
  b : ℝ → ℝ
  strict : Bool

/-- The value `Σ_a e_a log p_a + Σ_i f_i log ρ_i`. -/
noncomputable def Cond.val {k m : ℕ} (C : Cond k m) (p : Fin k → ℕ) (ρ : Fin m → ℕ) : ℝ :=
  ∑ a, C.e a * Real.log (p a) + ∑ i, C.f i * Real.log (ρ i)

/-- The condition holds at `(p, ρ)`. -/
def Cond.Holds {k m : ℕ} (C : Cond k m) (x : ℝ) (p : Fin k → ℕ) (ρ : Fin m → ℕ) : Prop :=
  if C.strict then C.val p ρ < C.b x else C.val p ρ ≤ C.b x

/-- A sieve term: `k` primes, `m` rough items (`ρ_i` free of primes below `p_{s(i)}`), and log-linear conditions. -/
structure Node where
  k : ℕ
  m : ℕ
  s : Fin m → Fin k
  conds : List (Cond k m)

/-- The product of a pair `(p, ρ)`. -/
def prodP {k m : ℕ} (v : (Fin k → ℕ) × (Fin m → ℕ)) : ℕ := (∏ a, v.1 a) * ∏ i, v.2 i

/-- The node's terms: pairs `(p, ρ)` in `[1, x]` with `ρ_i` free of primes below `p_{s(i)}` and the conditions. -/
noncomputable def Node.terms (N : Node) (x : ℝ) : Finset ((Fin N.k → ℕ) × (Fin N.m → ℕ)) :=
  (pairs N.k N.m ⌊x⌋₊).filter fun v => (∀ i, SieveTree.rough (v.1 (N.s i)) (v.2 i)) ∧ ∀ C ∈ N.conds, C.Holds x v.1 v.2

/-- The conditions of a term `(p, ρ)` of the node in `(x − y, x]`. -/
def Node.InI (N : Node) (x y : ℝ) (p : Fin N.k → ℕ) (ρ : Fin N.m → ℕ) : Prop :=
  (∀ C ∈ N.conds, C.Holds x p ρ) ∧ x - y < (prodP (p, ρ) : ℝ) ∧ (prodP (p, ρ) : ℝ) ≤ x

/-- The node's count in `(x − y, x]`. -/
noncomputable def Node.count (N : Node) (x y : ℝ) : ℕ :=
  #{v ∈ pairs N.k N.m ⌊x⌋₊ | (∀ i, SieveTree.rough (v.1 (N.s i)) (v.2 i)) ∧ N.InI x y v.1 v.2}

/-! ### The expanded conditions -/

/-- A condition on the expanded tuple: `e` on the primes, `f_i` on every prime of block `i`. -/
def Cond.lift {k m : ℕ} (C : Cond k m) (len : Fin m → ℕ) : LAtom (Idx k m len) :=
  ⟨Sum.elim C.e fun ij => C.f ij.1, C.b, C.strict⟩

/-- The order `q_j ≤ q_{j'}` of two primes of a block: `log q_j − log q_{j'} ≤ 0`. -/
def monoAtom {k m : ℕ} (len : Fin m → ℕ) (i : Fin m) (j j' : Fin (len i)) : LAtom (Idx k m len) :=
  ⟨fun t => (if t = Sum.inr ⟨i, j⟩ then 1 else 0) - (if t = Sum.inr ⟨i, j'⟩ then 1 else 0), fun _ => 0, false⟩

/-- The sifting `p_{s(i)} ≤ q_j` of a prime of block `i`: `log p_{s(i)} − log q_j ≤ 0`. -/
def siftAtom {k m : ℕ} (s : Fin m → Fin k) (len : Fin m → ℕ) (i : Fin m) (j : Fin (len i)) :
    LAtom (Idx k m len) :=
  ⟨fun t => (if t = Sum.inl (s i) then 1 else 0) - (if t = Sum.inr ⟨i, j⟩ then 1 else 0), fun _ => 0, false⟩

/-- The expanded conditions of a node for the pattern `len`. -/
noncomputable def Node.atoms (N : Node) (len : Fin N.m → ℕ) : List (LAtom (Idx N.k N.m len)) :=
  N.conds.map (fun C => C.lift len) ++
    (((univ : Finset (Σ i : Fin N.m, Fin (len i) × Fin (len i))).filter fun t => t.2.1 < t.2.2).toList.map
      fun t => monoAtom len t.1 t.2.1 t.2.2) ++
    ((univ : Finset (Σ i : Fin N.m, Fin (len i))).toList.map fun t => siftAtom N.s len t.1 t.2)

/-- The value of a lifted condition is the condition's value at the contracted pair, for positive entries. -/
theorem Cond.lift_val {k m : ℕ} (C : Cond k m) {len : Fin m → ℕ} {g : Idx k m len → ℕ} (hg : ∀ t, g t ≠ 0) :
    (C.lift len).val g = C.val (contract g).1 (contract g).2 := by
  simp only [LAtom.val, Cond.lift, Cond.val, contract, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  congr 1
  rw [Fintype.sum_sigma]
  refine sum_congr rfl fun i _ => ?_
  rw [Nat.cast_prod, Real.log_prod fun j _ => by exact_mod_cast hg _, mul_sum]
  rfl

/-- The value of a difference of two indicators: `Σ_t ([t = a] − [t = b]) log g_t = log g_a − log g_b`. -/
theorem val_diff {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) (g : ι → ℕ) :
    ∑ t, ((if t = a then (1 : ℝ) else 0) - (if t = b then 1 else 0)) * Real.log (g t) =
      Real.log (g a) - Real.log (g b) := by
  simp only [sub_mul, sum_sub_distrib, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]

/-- A pair's product is the product of its expanded tuple. -/
theorem prodP_contract {k m : ℕ} {len : Fin m → ℕ} (g : Idx k m len → ℕ) :
    prodP (contract g) = ∏ t, g t := by
  simp only [prodP, contract, block, Fintype.prod_sum_type, Fintype.prod_sigma]

/-- A coordinate of a tuple of positive numbers is at most its product. -/
theorem le_prod_of_pos {ι : Type*} [Fintype ι] {g : ι → ℕ} (hg : ∀ t, 0 < g t) (t : ι) : g t ≤ ∏ t, g t :=
  Nat.le_of_dvd (prod_pos fun t _ => hg t) (dvd_prod_of_mem _ (mem_univ t))

/-- A lifted condition holds at an expanded tuple of positive numbers exactly when the condition holds at its
contracted pair. -/
theorem holds_lift {k m : ℕ} (C : Cond k m) {len : Fin m → ℕ} {g : Idx k m len → ℕ} (hg : ∀ t, g t ≠ 0) (x : ℝ) :
    (C.lift len).Holds x g ↔ C.Holds x (contract g).1 (contract g).2 := by
  unfold LAtom.Holds Cond.Holds
  rw [C.lift_val hg]
  rfl

/-- The order atom holds exactly when the two primes are in order. -/
theorem holds_mono {k m : ℕ} {len : Fin m → ℕ} (i : Fin m) (j j' : Fin (len i)) {g : Idx k m len → ℕ}
    (hg : ∀ t, 0 < g t) (x : ℝ) :
    (monoAtom len i j j').Holds x g ↔ g (Sum.inr ⟨i, j⟩) ≤ g (Sum.inr ⟨i, j'⟩) := by
  unfold LAtom.Holds LAtom.val monoAtom
  simp only [Bool.false_eq_true, ite_false]
  rw [val_diff, sub_nonpos, Real.log_le_log_iff (by exact_mod_cast hg _) (by exact_mod_cast hg _), Nat.cast_le]

/-- The sifting atom holds exactly when the prime of the block is at least the sifting prime. -/
theorem holds_sift {k m : ℕ} (s : Fin m → Fin k) {len : Fin m → ℕ} (i : Fin m) (j : Fin (len i))
    {g : Idx k m len → ℕ} (hg : ∀ t, 0 < g t) (x : ℝ) :
    (siftAtom s len i j).Holds x g ↔ g (Sum.inl (s i)) ≤ g (Sum.inr ⟨i, j⟩) := by
  unfold LAtom.Holds LAtom.val siftAtom
  simp only [Bool.false_eq_true, ite_false]
  rw [val_diff, sub_nonpos, Real.log_le_log_iff (by exact_mod_cast hg _) (by exact_mod_cast hg _), Nat.cast_le]

/-- **The expanded conditions.** At an expanded tuple of positive numbers they hold exactly when the node's conditions
hold at the contracted pair, the blocks are monotone, and every prime of a block is at least its sifting prime. -/
theorem forall_atoms (N : Node) {len : Fin N.m → ℕ} {g : Idx N.k N.m len → ℕ} (hg : ∀ t, 0 < g t) (x : ℝ) :
    (∀ A ∈ N.atoms len, A.Holds x g) ↔ (∀ C ∈ N.conds, C.Holds x (contract g).1 (contract g).2) ∧
      (∀ i, Monotone (block g i)) ∧ ∀ i j, g (Sum.inl (N.s i)) ≤ block g i j := by
  have hg0 : ∀ t, g t ≠ 0 := fun t => (hg t).ne'
  simp only [Node.atoms, List.forall_mem_append, List.forall_mem_map, mem_toList, mem_filter, mem_univ, true_and,
    Sigma.forall, Prod.forall, and_assoc, true_implies]
  refine and_congr (forall₂_congr fun C _ => holds_lift C hg0 x) (and_congr ?_ ?_)
  · constructor
    · intro h i j j' hjj'
      rcases lt_or_eq_of_le hjj' with hlt | rfl
      · exact (holds_mono i j j' hg x).1 (h i j j' hlt)
      · exact le_rfl
    · intro h i j j' hlt
      exact (holds_mono i j j' hg x).2 (h i hlt.le)
  · exact forall₂_congr fun i j => holds_sift N.s i j hg x

/-- **The count as a sum over the patterns.** Let `0 < c` and suppose that, for large `x`, the conditions force
every prime above `x^c` and every rough item above `1`. Then for large `x` and `0 ≤ y ≤ x`, the count is the sum over
the patterns `len` with `1 ≤ len_i ≤ ⌊1/c⌋₊` of the counts of the cut of the expanded conditions. -/
theorem count_eq_sum (N : Node) {c : ℝ} (hc : 0 < c)
    (hbig : ∀ᶠ x in atTop, ∀ v ∈ N.terms x, (∀ a, x ^ c < v.1 a) ∧ ∀ i, 1 < v.2 i) :
    ∀ᶠ x in atTop, ∀ y : ℝ, (N.count x y : ℝ) = ∑ len ∈ (Fintype.piFinset fun _ : Fin N.m => Icc 1 ⌊1 / c⌋₊),
      (#{g ∈ cut c (N.atoms len) x | x - y < ((∏ t, g t : ℕ) : ℝ) ∧ ((∏ t, g t : ℕ) : ℝ) ≤ x} : ℝ) := by
  filter_upwards [hbig, eventually_ge_atTop (2 : ℝ)] with x hbx hx2 y
  have hx0 : 0 < x := by linarith
  set R := ⌊1 / c⌋₊ with hR
  -- the rough items have at most `R` prime factors
  have hRb : ∀ v ∈ pairs N.k N.m ⌊x⌋₊, (∀ i, SieveTree.rough (v.1 (N.s i)) (v.2 i)) → N.InI x y v.1 v.2 →
      ∀ i, (v.2 i).primeFactorsList.length ≤ R := by
    intro v hv hr hP i
    have hvt : v ∈ N.terms x := mem_filter.2 ⟨hv, hr, hP.1⟩
    obtain ⟨hpbig, hρ1⟩ := hbx v hvt
    have hρ0 : v.2 i ≠ 0 := by have := hρ1 i; omega
    -- every prime factor of `ρ_i` exceeds `x^c`, and `ρ_i ≤ x`
    set l := (v.2 i).primeFactorsList with hl
    have hfac : ∀ q ∈ l, x ^ c < (q : ℝ) := fun q hq => by
      have hqp := Nat.prime_of_mem_primeFactorsList hq
      have hqd := Nat.dvd_of_mem_primeFactorsList hq
      have hge : v.1 (N.s i) ≤ q := by
        by_contra hlt
        exact hr i q (not_le.1 hlt) hqp hqd
      exact lt_of_lt_of_le (hpbig _) (by exact_mod_cast hge)
    have hρx : (v.2 i : ℝ) ≤ x := by
      have h1 : v.2 i ≤ prodP v := by
        unfold prodP
        have hp : 0 < ∏ a, v.1 a := prod_pos fun a _ => by
          have := hpbig a; have : (0 : ℝ) < v.1 a := lt_trans (Real.rpow_pos_of_pos hx0 c) this
          exact_mod_cast this
        have hr' : v.2 i ≤ ∏ i, v.2 i := Nat.le_of_dvd (prod_pos fun i _ => by have := hρ1 i; omega)
          (dvd_prod_of_mem _ (mem_univ i))
        calc v.2 i ≤ ∏ i, v.2 i := hr'
          _ ≤ (∏ a, v.1 a) * ∏ i, v.2 i := Nat.le_mul_of_pos_left _ hp
      exact le_trans (by exact_mod_cast h1) hP.2.2
    -- `x^{c·#l} < ρ_i ≤ x`
    have hprod : (x ^ c) ^ l.length ≤ (v.2 i : ℝ) := by
      have hlp : (l.prod : ℝ) = v.2 i := by rw [hl]; exact_mod_cast Nat.prod_primeFactorsList hρ0
      rw [← hlp]
      have key : ∀ l' : List ℕ, (∀ q ∈ l', x ^ c < (q : ℝ)) → (x ^ c) ^ l'.length ≤ (l'.prod : ℝ) := by
        intro l' hl'
        induction l' with
        | nil => simp
        | cons q l' ih =>
          rw [List.length_cons, pow_succ, List.prod_cons, Nat.cast_mul]
          have h1 := hl' q List.mem_cons_self
          have h2 := ih fun q' hq' => hl' q' (List.mem_cons_of_mem _ hq')
          calc (x ^ c) ^ l'.length * x ^ c ≤ (l'.prod : ℝ) * q :=
                mul_le_mul h2 h1.le (by positivity) (by positivity)
            _ = q * l'.prod := by ring
      exact key l hfac
    have hlen : c * l.length ≤ 1 := by
      have h1 : (x ^ c) ^ l.length ≤ x := hprod.trans hρx
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le] at h1
      have h2 := (Real.rpow_le_rpow_left_iff (by linarith : (1 : ℝ) < x)).1 (h1.trans (Real.rpow_one x).symm.le)
      linarith
    rw [hR]
    exact Nat.le_floor (by rw [le_div_iff₀ hc]; linarith)
  -- the count, expanded
  rw [Node.count, card_expand N.s ⌊x⌋₊ R (N.InI x y) hRb, Nat.cast_sum]
  -- the patterns with an empty block contribute nothing; the others are cuts
  have hsub : (Fintype.piFinset fun _ : Fin N.m => Icc 1 R) ⊆ Fintype.piFinset fun _ : Fin N.m => range (R + 1) :=
    fun len hlen => Fintype.mem_piFinset.2 fun i => by
      have := mem_Icc.1 (Fintype.mem_piFinset.1 hlen i)
      exact mem_range.2 (by omega)
  -- a tuple of the expanded set: its contracted pair is a term, with positive entries
  have hterm : ∀ (len : Fin N.m → ℕ) (g : Idx N.k N.m len → ℕ), g ∈ tuplesOf N.k N.m ⌊x⌋₊ len →
      (∀ i, Monotone (block g i)) → (∀ i, ∏ j, block g i j ≤ ⌊x⌋₊) → (∀ i j, g (Sum.inl (N.s i)) ≤ block g i j) →
      N.InI x y (contract g).1 (contract g).2 → contract g ∈ N.terms x := by
    intro len g hgT hmono hY hsift hP
    have hgp : ∀ t, (g t).Prime ∧ g t ≤ ⌊x⌋₊ := fun t => by
      have := SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 hgT t)
      exact ⟨this.2, this.1⟩
    have hpos : ∀ i, 1 ≤ (contract g).2 i := fun i => by
      show 0 < ∏ j, block g i j
      exact prod_pos fun j _ => (hgp _).1.pos
    refine mem_filter.2 ⟨mem_product.2 ⟨Fintype.mem_piFinset.2 fun a =>
      SieveTypeIIU.mem_primesLe.2 ⟨(hgp _).2, (hgp _).1⟩, Fintype.mem_piFinset.2 fun i =>
        mem_Icc.2 ⟨hpos i, hY i⟩⟩, fun i => ?_, hP.1⟩
    intro q hq hqp hqd
    simp only [contract] at hq hqd
    obtain ⟨j, -, hj⟩ := (Prime.dvd_finsetProd_iff hqp.prime _).1 hqd
    have := (Nat.prime_dvd_prime_iff_eq hqp (hgp _).1).1 hj
    have := hsift i j
    simp only [block] at this
    omega
  symm
  calc ∑ len ∈ Fintype.piFinset (fun _ : Fin N.m => Icc 1 R),
        (#{g ∈ cut c (N.atoms len) x | x - y < ((∏ t, g t : ℕ) : ℝ) ∧ ((∏ t, g t : ℕ) : ℝ) ≤ x} : ℝ)
      = ∑ len ∈ Fintype.piFinset (fun _ : Fin N.m => Icc 1 R),
        (#{g ∈ tuplesOf N.k N.m ⌊x⌋₊ len | (∀ i, Monotone (block g i)) ∧ (∀ i, ∏ j, block g i j ≤ ⌊x⌋₊) ∧
          (∀ i j, g (Sum.inl (N.s i)) ≤ block g i j) ∧ N.InI x y (contract g).1 (contract g).2} : ℝ) := by
        refine sum_congr rfl fun len hlen => ?_
        congr 2
        ext g
        simp only [cut, mem_filter]
        constructor
        · rintro ⟨⟨hgQ, hat⟩, hp1, hp2⟩
          have hgq : ∀ t, (g t).Prime ∧ ⌊x ^ c⌋₊ < g t ∧ g t < ⌈x ^ (2 : ℝ)⌉₊ := fun t => by
            obtain ⟨h1, h2⟩ := mem_filter.1 (Fintype.mem_piFinset.1 hgQ t)
            exact ⟨h2, (mem_Ioo.1 h1).1, (mem_Ioo.1 h1).2⟩
          have hgpos : ∀ t, 0 < g t := fun t => (hgq t).1.pos
          obtain ⟨hC, hmono, hsift⟩ := (forall_atoms N hgpos x).1 hat
          have hle : ∀ t, (g t : ℝ) ≤ x := fun t =>
            le_trans (by exact_mod_cast le_prod_of_pos hgpos t) hp2
          refine ⟨Fintype.mem_piFinset.2 fun t => SieveTypeIIU.mem_primesLe.2 ⟨Nat.le_floor (hle t), (hgq t).1⟩,
            hmono, fun i => Nat.le_floor ?_, hsift, hC, ?_, ?_⟩
          · have h1 : ∏ j, block g i j ≤ ∏ t, g t := by
              rw [← prodP_contract g]
              refine Nat.le_of_dvd ?_ ?_
              · rw [prodP_contract]; exact prod_pos fun t _ => hgpos t
              · exact dvd_trans (dvd_prod_of_mem (fun i' => ∏ j, block g i' j) (mem_univ i)) (Dvd.intro_left _ rfl)
            exact le_trans (by exact_mod_cast h1) hp2
          · rw [prodP_contract]; exact hp1
          · rw [prodP_contract]; exact hp2
        · rintro ⟨hgT, hmono, hY, hsift, hC, hp1, hp2⟩
          have hct := hterm len g hgT hmono hY hsift ⟨hC, hp1, hp2⟩
          have hgp : ∀ t, (g t).Prime ∧ g t ≤ ⌊x⌋₊ := fun t => by
            have := SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 hgT t)
            exact ⟨this.2, this.1⟩
          have hgpos : ∀ t, 0 < g t := fun t => (hgp t).1.pos
          obtain ⟨hpbig, -⟩ := hbx _ hct
          rw [prodP_contract] at hp1 hp2
          refine ⟨⟨Fintype.mem_piFinset.2 fun t => mem_filter.2 ⟨mem_Ioo.2 ⟨?_, ?_⟩, (hgp t).1⟩,
            (forall_atoms N hgpos x).2 ⟨hC, hmono, hsift⟩⟩, hp1, hp2⟩
          · -- every entry exceeds `x^c`: the primes by `hbig`, the blocks' through their sifting primes
            rcases t with a | ⟨i, j⟩
            · exact Nat.floor_lt' (by have := (hgp (Sum.inl a)).1.pos; omega) |>.2 (hpbig a)
            · have h1 := hpbig (N.s i)
              have h2 : (g (Sum.inl (N.s i)) : ℝ) ≤ g (Sum.inr ⟨i, j⟩) := by exact_mod_cast hsift i j
              exact Nat.floor_lt' (by have := (hgp (Sum.inr ⟨i, j⟩)).1.pos; omega) |>.2 (lt_of_lt_of_le h1 h2)
          · -- and is below `x²`
            have h1 : (g t : ℝ) ≤ x := le_trans (by exact_mod_cast (hgp t).2) (Nat.floor_le (by linarith))
            have h2 : x < x ^ (2 : ℝ) := by
              rw [Real.rpow_two, sq]; exact lt_mul_of_one_lt_right hx0 (by linarith)
            exact Nat.lt_ceil.2 (lt_of_le_of_lt h1 h2)
    _ = ∑ len ∈ Fintype.piFinset (fun _ : Fin N.m => range (R + 1)),
        (#{g ∈ tuplesOf N.k N.m ⌊x⌋₊ len | (∀ i, Monotone (block g i)) ∧ (∀ i, ∏ j, block g i j ≤ ⌊x⌋₊) ∧
          (∀ i j, g (Sum.inl (N.s i)) ≤ block g i j) ∧ N.InI x y (contract g).1 (contract g).2} : ℝ) := by
        refine sum_subset hsub fun len hlen hnot => ?_
        -- some block is empty: its product `1` is not a rough item of a term
        have hex : ∃ i, len i = 0 := by
          by_contra hall
          push Not at hall
          refine hnot (Fintype.mem_piFinset.2 fun i => mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 (hall i), ?_⟩)
          have := mem_range.1 (Fintype.mem_piFinset.1 hlen i)
          omega
        obtain ⟨i, hi⟩ := hex
        rw [Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
        rintro g hgT ⟨hmono, hY, hsift, hP⟩
        have hct := hterm len g hgT hmono hY hsift hP
        have h1 := (hbx _ hct).2 i
        have h2 : (contract g).2 i = 1 := by
          simp only [contract]
          have : IsEmpty (Fin (len i)) := by rw [hi]; exact Fin.isEmpty'
          exact Finset.prod_of_isEmpty _
        omega

/-! ### The asymptotic formula -/

/-- The witness on the expanded tuples of a pattern: every prime of block `i` in the group of the rough item `i`. -/
def liftWit {k m G : ℕ} (len : Fin m → ℕ) (grp : Fin k ⊕ Fin m → Fin G) (w : (Fin G → ℝ) × (Fin G → ℝ)) :
    Wit (Idx k m len) :=
  ⟨G, Sum.elim (fun a => grp (Sum.inl a)) fun ij => grp (Sum.inr ij.1), w.1, w.2⟩

/-- A group's product over an expanded tuple is the product of its items: the primes, and the blocks' products. -/
theorem prod_group {k m G : ℕ} {len : Fin m → ℕ} (grp : Fin k ⊕ Fin m → Fin G) (g : Idx k m len → ℕ) (i : Fin G) :
    ∏ t ∈ univ.filter (fun t => Sum.elim (fun a => grp (Sum.inl a)) (fun ij => grp (Sum.inr ij.1)) t = i),
        (g t : ℝ) =
      (∏ a ∈ univ.filter (fun a => grp (Sum.inl a) = i), ((contract g).1 a : ℝ)) *
        ∏ j ∈ univ.filter (fun j => grp (Sum.inr j) = i), ((contract g).2 j : ℝ) := by
  rw [prod_filter, prod_filter, prod_filter, Fintype.prod_sum_type, Fintype.prod_sigma]
  congr 1
  refine prod_congr rfl fun i' _ => ?_
  show (∏ j : Fin (len i'), if grp (Sum.inr i') = i then (g (Sum.inr ⟨i', j⟩) : ℝ) else 1) =
    if grp (Sum.inr i') = i then (((∏ j, block g i' j : ℕ)) : ℝ) else 1
  split_ifs with h
  · push_cast; rfl
  · simp

/-- The coefficients of a lifted condition: `e` on the primes, `f_i` on block `i`. -/
theorem lift_e {k m : ℕ} (C : Cond k m) (len : Fin m → ℕ) (t : Idx k m len) :
    (C.lift len).e t = Sum.elim C.e (fun ij => C.f ij.1) t := rfl

/-- Every expanded condition has a coordinate whose coefficient differs from that of the first prime. -/
theorem atoms_ne (N : Node) (hk : 0 < N.k) {len : Fin N.m → ℕ} (hlen : ∀ i, 0 < len i)
    (hcond : ∀ C ∈ N.conds, ∃ u w : Fin N.k ⊕ Fin N.m, Sum.elim C.e C.f u ≠ Sum.elim C.e C.f w) :
    ∀ A ∈ N.atoms len, ∃ u, u ≠ (Sum.inl ⟨0, hk⟩ : Idx N.k N.m len) ∧ A.e u ≠ A.e (Sum.inl ⟨0, hk⟩) := by
  set v : Idx N.k N.m len := Sum.inl ⟨0, hk⟩ with hv
  -- a coordinate of each item
  set pos : Fin N.k ⊕ Fin N.m → Idx N.k N.m len := Sum.elim Sum.inl fun i => Sum.inr ⟨i, ⟨0, hlen i⟩⟩ with hpos
  have hcoef : ∀ (C : Cond N.k N.m) (it : Fin N.k ⊕ Fin N.m), (C.lift len).e (pos it) = Sum.elim C.e C.f it := by
    intro C it
    rcases it with a | i <;> rfl
  intro A hA
  simp only [Node.atoms, List.mem_append, List.mem_map, mem_toList, mem_filter, mem_univ, true_and] at hA
  rcases hA with (⟨C, hC, rfl⟩ | ⟨⟨i, j, j'⟩, hjj', rfl⟩) | ⟨⟨i, j⟩, rfl⟩
  · -- a lifted condition: two items with different coefficients
    obtain ⟨u, w, huw⟩ := hcond C hC
    by_cases hu : (C.lift len).e (pos u) = (C.lift len).e v
    · have hw : (C.lift len).e (pos w) ≠ (C.lift len).e v := by
        intro h
        apply huw
        rw [← hcoef, ← hcoef, hu, h]
      exact ⟨pos w, fun h => hw (by rw [h]), hw⟩
    · exact ⟨pos u, fun h => hu (by rw [h]), hu⟩
  · -- an order atom: the first prime has coefficient `0`
    refine ⟨Sum.inr ⟨i, j⟩, Sum.inr_ne_inl, ?_⟩
    simp only [monoAtom, hv]
    have hne : (Sum.inr ⟨i, j⟩ : Idx N.k N.m len) ≠ Sum.inr ⟨i, j'⟩ := by
      intro h
      simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
      exact absurd h (ne_of_lt hjj')
    simp [hne]
  · -- a sifting atom
    refine ⟨Sum.inr ⟨i, j⟩, Sum.inr_ne_inl, ?_⟩
    have hu : (siftAtom N.s len i j).e (Sum.inr ⟨i, j⟩) = -1 := by simp [siftAtom]
    have hv' : (siftAtom N.s len i j).e v = if v = Sum.inl (N.s i) then 1 else 0 := by simp [siftAtom, hv]
    rw [hu, hv']
    split_ifs <;> norm_num

/-- Two coordinates of a tuple of positive numbers have product at most the tuple's product. -/
theorem mul_le_prod_of_ne {ι : Type*} [Fintype ι] [DecidableEq ι] {g : ι → ℕ} (hg : ∀ t, 0 < g t) {t t' : ι}
    (htt' : t ≠ t') : g t * g t' ≤ ∏ t, g t := by
  rw [← prod_pair htt']
  exact prod_le_prod_of_subset_of_one_le (subset_univ _) fun t _ _ => hg t

/-- **A tuple of the cut is a term.** For `x ≥ 2`, a tuple of the cut of the expanded conditions with product at most
`2x` contracts to a term of the node: its entries and its blocks' products are at most `x`, since there is always
another entry at least `2`. -/
theorem contract_mem_terms (N : Node) (hk : 0 < N.k) (hm : 0 < N.m) {c x : ℝ} {len : Fin N.m → ℕ}
    (hlen : ∀ i, 0 < len i) {g : Idx N.k N.m len → ℕ} (hg : g ∈ cut c (N.atoms len) x)
    (h2 : ((∏ t, g t : ℕ) : ℝ) ≤ 2 * x) : contract g ∈ N.terms x := by
  obtain ⟨hgQ, hat⟩ := mem_filter.1 hg
  have hgp : ∀ t, (g t).Prime := fun t => (mem_filter.1 (Fintype.mem_piFinset.1 hgQ t)).2
  have hgpos : ∀ t, 0 < g t := fun t => (hgp t).pos
  obtain ⟨hC, hmono, hsift⟩ := (forall_atoms N hgpos x).1 hat
  set v₀ : Idx N.k N.m len := Sum.inl ⟨0, hk⟩ with hv₀
  set v₁ : Idx N.k N.m len := Sum.inr ⟨⟨0, hm⟩, ⟨0, hlen _⟩⟩ with hv₁
  -- `n · 2 ≤ 2x` for a factor `n` with a cofactor `≥ 2`
  have key : ∀ n m' : ℕ, 2 ≤ m' → n * m' ≤ ∏ t, g t → (n : ℝ) ≤ x := fun n m' hm' hle => by
    have : (n : ℝ) * 2 ≤ 2 * x := by
      calc (n : ℝ) * 2 ≤ n * m' := mul_le_mul_of_nonneg_left (by exact_mod_cast hm') (by positivity)
        _ ≤ ((∏ t, g t : ℕ) : ℝ) := by exact_mod_cast hle
        _ ≤ 2 * x := h2
    linarith
  have hle : ∀ t, (g t : ℝ) ≤ x := by
    intro t
    by_cases ht : t = v₀
    · exact key _ _ (hgp v₁).two_le (mul_le_prod_of_ne hgpos (by rw [ht]; exact Sum.inl_ne_inr))
    · exact key _ _ (hgp v₀).two_le (mul_le_prod_of_ne hgpos ht)
  -- a block's product times the first prime is at most the product
  have hblock : ∀ i, (∏ j, block g i j) * g v₀ ≤ ∏ t, g t := by
    intro i
    rw [← prodP_contract g]
    simp only [prodP, contract]
    rw [mul_comm]
    exact Nat.mul_le_mul
      (Nat.le_of_dvd (prod_pos fun a _ => hgpos _) (dvd_prod_of_mem (fun a => g (Sum.inl a)) (mem_univ _)))
      (Nat.le_of_dvd (prod_pos fun i _ => prod_pos fun j _ => hgpos _)
        (dvd_prod_of_mem (fun i => ∏ j, block g i j) (mem_univ i)))
  have hpos : ∀ i, 1 ≤ (contract g).2 i := fun i => by
    show 0 < ∏ j, block g i j
    exact prod_pos fun j _ => hgpos _
  refine mem_filter.2 ⟨mem_product.2 ⟨Fintype.mem_piFinset.2 fun a =>
    SieveTypeIIU.mem_primesLe.2 ⟨Nat.le_floor (hle _), hgp _⟩, Fintype.mem_piFinset.2 fun i =>
      mem_Icc.2 ⟨hpos i, Nat.le_floor (key _ _ (hgp v₀).two_le (hblock i))⟩⟩, fun i => ?_, hC⟩
  intro q hq hqp hqd
  simp only [contract] at hq hqd
  obtain ⟨j, -, hj⟩ := (Prime.dvd_finsetProd_iff hqp.prime _).1 hqd
  have := (Nat.prime_dvd_prime_iff_eq hqp (hgp _)).1 hj
  have := hsift i j
  simp only [block] at this
  omega

/-- **The asymptotic formula for a node.** Let `N` have `k ≥ 1` primes and `m ≥ 1` rough items, conditions whose
coefficients are not all equal, and suppose that for large `x` its terms have their primes above `x^c` and their rough
items above `1`. Let a grouping of the items and a finite list of Hölder data `(a, δ)`, admissible at `θ, κ`, cover
every term with product in `(x/4, 2x]` with margin `μ` (each group's product at least `x^{a_g + μ}`). Then for large
`x` and `x^θ ≤ y ≤ x^{1−ρ}`, the node's terms in `(x − y, x]` number `(y/x^{1−ρ})` times those in
`(x − x^{1−ρ}, x]`, up to `C y/log² x`: for each pattern of numbers of prime factors, the expanded tuples are a cut
(`count_eq_sum`) to which `ShortSieveTerm.abs_card_cut_sub_le` applies, with the witness lifted to the blocks. -/
theorem abs_count_sub_le (N : Node) (hk : 0 < N.k) (hm : 0 < N.m) {c θ κ ρ μ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hθ : 0 < θ) (hκ : 0 < κ) (hρ : 0 < ρ) (hρc : 12 * ρ < c) (hθρ : θ + ρ ≤ 1) (hμ : 0 < μ)
    (hcond : ∀ C ∈ N.conds, ∃ u w : Fin N.k ⊕ Fin N.m, Sum.elim C.e C.f u ≠ Sum.elim C.e C.f w)
    (hbig : ∀ᶠ x in atTop, ∀ v ∈ N.terms x, (∀ a, x ^ c < v.1 a) ∧ ∀ i, 1 < v.2 i)
    {G : ℕ} (grp : Fin N.k ⊕ Fin N.m → Fin G) (W : List ((Fin G → ℝ) × (Fin G → ℝ)))
    (hW : ∀ w ∈ W, (∀ i, κ < w.1 i) ∧ (∀ i, 0 < w.2 i) ∧ ∑ i, 1 / w.2 i = 1 ∧
      ∀ i, ShortSieveTypeII.MomentOK ((1 - θ + κ) / (w.1 i - κ)) (w.2 i))
    (hcov : ∀ᶠ x in atTop, ∀ v ∈ N.terms x, x / 4 < (prodP v : ℝ) → (prodP v : ℝ) ≤ 2 * x →
      ∃ w ∈ W, ∀ i, x ^ (w.1 i + μ) ≤ (∏ a ∈ univ.filter (fun a => grp (Sum.inl a) = i), (v.1 a : ℝ)) *
        ∏ j ∈ univ.filter (fun j => grp (Sum.inr j) = i), (v.2 j : ℝ)) :
    ∃ C : ℝ, ∀ᶠ x in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) →
      |(N.count x y : ℝ) - y / x ^ (1 - ρ) * N.count x (x ^ (1 - ρ))| ≤ C * y / Real.log x ^ 2 := by
  set P := Fintype.piFinset fun _ : Fin N.m => Icc 1 ⌊1 / c⌋₊ with hP
  -- each pattern: the term layer
  have hpat : ∀ len ∈ P, ∃ C : ℝ, ∀ᶠ x in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) →
      |(#{g ∈ cut c (N.atoms len) x | x - y < ((∏ t, g t : ℕ) : ℝ) ∧ ((∏ t, g t : ℕ) : ℝ) ≤ x} : ℝ) -
        y / x ^ (1 - ρ) * #{g ∈ cut c (N.atoms len) x | x - x ^ (1 - ρ) < ((∏ t, g t : ℕ) : ℝ) ∧
          ((∏ t, g t : ℕ) : ℝ) ≤ x}| ≤ C * y / Real.log x ^ 2 := by
    intro len hlen
    have hlen1 : ∀ i, 0 < len i := fun i => (mem_Icc.1 (Fintype.mem_piFinset.1 hlen i)).1
    refine abs_card_cut_sub_le (Sum.inl ⟨0, hk⟩) hc hc1 hθ hκ hρ hρc hθρ hμ (N.atoms len)
      (atoms_ne N hk hlen1 hcond) (W.map (liftWit len grp)) (fun w hw => ?_) ?_
    · obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw
      exact hW w' hw'
    · filter_upwards [hcov] with x hcovx
      intro g hg h1 h2
      have hgp : ∀ t, (g t).Prime := fun t => (mem_filter.1 (Fintype.mem_piFinset.1 (mem_filter.1 hg).1 t)).2
      have hprod : ((∏ t, g t : ℕ) : ℝ) = ∏ t, (g t : ℝ) := by push_cast; rfl
      have hterm := contract_mem_terms N hk hm hlen1 hg (by rw [hprod]; exact h2)
      have hP' : (prodP (contract g) : ℝ) = ∏ t, (g t : ℝ) := by rw [prodP_contract, hprod]
      obtain ⟨w, hwW, hw⟩ := hcovx _ hterm (by rw [hP']; exact h1) (by rw [hP']; exact h2)
      refine ⟨liftWit len grp w, List.mem_map.2 ⟨w, hwW, rfl⟩, fun i => ?_⟩
      have h2 := hw i
      rw [← prod_group grp g i] at h2
      convert h2 using 2
      · rfl
      · ext t
        simp only [mem_filter, mem_univ, true_and]
        rfl
  choose! Cf hCf using hpat
  refine ⟨∑ len ∈ P, Cf len, ?_⟩
  filter_upwards [count_eq_sum N hc hbig, (eventually_all_finset P).2 hCf] with x hsum hall y hy1 hy2
  rw [hsum y, hsum (x ^ (1 - ρ)), mul_sum, ← sum_sub_distrib, sum_mul, sum_div]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun len hlen => hall len hlen y hy1 hy2)

end ShortSieveNode

#print axioms ShortSieveNode.count_eq_sum
#print axioms ShortSieveNode.abs_count_sub_le
