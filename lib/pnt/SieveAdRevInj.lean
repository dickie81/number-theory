/-
# Role reversal: the primes of the atoms' boxes are terms of the box

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. For a box `[c3, c2, c1]` of three primes that passes `SieveAd.revOK`, the other half of the
reversal (`SieveAdRevLemma.lean` has the first): the numbers `n = p·r'` with `p` prime and `r'` the product of a
tuple of an atoms' box, `r'` between `x^{(DEN−h₁+1)/DEN}` and `x^{(DEN−l₁)/DEN}`, are counted by the term of the box,
each once.

* `rev_mem`: for an atoms' box with the cell `c2` at a position `j` before the last and `c3` at the last, a tuple
  `u` of it with `r' = ∏u` in that range and `n = p·r' ∈ (N₁, N₂]`, `p` prime: `(p, u_j, u_last)` is a tuple of
  the box that counts `n`.
* `readOff`, `GoodL`, `readOff_inj`: a tuple of primes as its list, with the position `j`; the triple read off a
  list; two strictly decreasing lists of primes that give the same triple for the same `n` are equal, with the same
  position, by unique factorisation.
* `rev_inject_pt`, `rev_inject`: so for every `n`, the tuples of the five atoms' boxes that count `n` number at
  most the tuples of the box that count it; and with weights `g ≥ 0`, the sum of the numbers `p·r'` over the five
  boxes is at most the term of the box.

The file imports `SieveAdRevLemma.lean`.
-/
import SieveAdRevLemma

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K DEN_pos' K_pos')

/-! ### A triple read off a list of primes -/

/-- The triple `(n/∏l, l_j, l_last)` read off a list `l` with a position `j`. -/
def readOff (n : ℕ) (e : ℕ × List ℕ) : Fin 3 → ℕ :=
  ![n / e.2.prod, e.2.getD e.1 0, e.2.getD (e.2.length - 1) 0]

theorem readOff_ofFn {k : ℕ} (n : ℕ) (j : Fin (k + 1)) (u : Fin (k + 1) → ℕ) :
    readOff n ((j : ℕ), List.ofFn u) = ![n / ∏ i, u i, u j, u (Fin.last k)] := by
  unfold readOff
  simp only [List.prod_ofFn, List.length_ofFn, Nat.add_sub_cancel]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact j.2),
    List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact Nat.lt_succ_self k)]
  simp only [List.getElem_ofFn]
  rfl

/-- A list of primes with a position, for `n`: strictly decreasing, with product a divisor of `n` and a positive
quotient, the position inside the list. -/
def GoodL (n : ℕ) (e : ℕ × List ℕ) : Prop :=
  e.2.SortedGT ∧ (∀ p ∈ e.2, p.Prime) ∧ e.2.prod ∣ n ∧ 0 < n / e.2.prod ∧ e.1 < e.2.length

/-- Two strictly decreasing lists of primes, with positions, that give the same triple for the same `n` are equal,
with the same position: the products are equal, so the lists are, by unique factorisation. -/
theorem readOff_inj {n : ℕ} {e e' : ℕ × List ℕ} (he : GoodL n e) (he' : GoodL n e')
    (h : readOff n e = readOff n e') : e = e' := by
  obtain ⟨j, l⟩ := e
  obtain ⟨j', l'⟩ := e'
  obtain ⟨hs, hp, hd, hK, hlt⟩ := he
  obtain ⟨hs', hp', hd', hK', hlt'⟩ := he'
  simp only at hs hp hd hK hlt hs' hp' hd' hK' hlt'
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [readOff, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hprod : l.prod = l'.prod := by
    have e1 := Nat.div_mul_cancel hd
    have e2 := Nat.div_mul_cancel hd'
    rw [h0] at e1
    exact Nat.eq_of_mul_eq_mul_left hK' (e1.trans e2.symm)
  have hperm : l.Perm l' :=
    (Nat.primeFactorsList_unique rfl hp).trans (Nat.primeFactorsList_unique hprod.symm hp').symm
  have hl : l = l' := hperm.eq_of_sortedGE hs.sortedGE hs'.sortedGE
  subst hl
  rw [List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ hlt'] at h1
  have hj : j = j' := (hs.nodup.getElem_inj_iff).1 h1
  rw [hj]

variable [Route]

/-! ### The numbers `p·r'` are terms of the box -/

/-- **A prime times a tuple of an atoms' box is counted by the box.** For a box `[c3, c2, c1]` that passes `revOK`,
at a large modulus; an atoms' box `bx` with the cell `c2` at a position `j` before the last and `c3` at the last;
a tuple `u` of `bx` with product between `x^{(DEN−h₁+1)/DEN}` and `x^{(DEN−l₁)/DEN}`; and `n ∈ (N₁, N₂]` with
`∏u | n` and `n/∏u` prime: `(n/∏u, u_j, u_last)` is a tuple of the box, its product divides `n`, and `n` has no
prime factor below `u_last`. -/
theorem rev_mem [RouteOK] {q : ℕ} (hq : Big q) {c1 c2 c3 : Cell} (hrev : revOK [c3, c2, c1] = true) {k : ℕ}
    (bx : Fin (k + 1) → Cell) (j : Fin (k + 1)) (hj : j < Fin.last k) (hbj : bx j = c2)
    (hbl : bx (Fin.last k) = c3) {n : ℕ} (hn : n ∈ Ioc (N1 q) (N2 q)) {u : Fin (k + 1) → ℕ}
    (hu : u ∈ famK q (e1 c1 + 1) (e2 c1 - 1) (k + 1) bx) (hd : (∏ i, u i) ∣ n) (hK : (n / ∏ i, u i).Prime) :
    (![n / ∏ i, u i, u j, u (Fin.last k)] : Fin 3 → ℕ) ∈ (famB q (boxFn [c3, c2, c1] 3 rfl)).filter
      (fun rt => (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last 2)) n) := by
  obtain ⟨hx3, hX1, hn'⟩ := big_n hq
  obtain ⟨hn1, hn2⟩ := hn' n hn
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 ≤ xq q := by linarith
  simp only [revOK, Bool.and_eq_true, Nat.ble_eq] at hrev
  obtain ⟨⟨⟨⟨hcells, hb⟩, hsum⟩, hcube⟩, h31⟩ := hrev
  have hcl := (cellsOK_iff _).1 hcells
  have hk1 := hcl c1 (by simp)
  have hk2 := hcl c2 (by simp)
  rw [famK, Finset.mem_filter] at hu
  obtain ⟨hub, hsl⟩ := hu
  obtain ⟨hp, hsa, hc⟩ := mem_famB.1 hub
  unfold slabP at hsl
  rw [aprodR_full (le_refl _)] at hsl
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ, r = ∏ i, u i := ⟨_, rfl⟩
  rw [← hrdef] at hd hK ⊢
  have hrcast : ∏ i, (u i : ℝ) = (r : ℝ) := by rw [hrdef]; push_cast; rfl
  rw [hrcast] at hsl
  obtain ⟨Kp, hKdef⟩ : ∃ Kp : ℕ, Kp = n / r := ⟨_, rfl⟩
  rw [← hKdef] at hK ⊢
  have hnK : n = r * Kp := by rw [hKdef, Nat.mul_div_cancel' hd]
  have hncast : (n : ℝ) = r * Kp := by exact_mod_cast hnK
  have hr0 : (0 : ℝ) < r := lt_trans (Xe_pos hx0 _) hsl.1
  have hK0 : (0 : ℝ) < Kp := by exact_mod_cast hK.pos
  have hn0 : 0 < n := by have := (Finset.mem_Ioc.1 hn).1; omega
  -- the prime lies in the cell `c1`
  have hKlo : Xe q c1.1 < Kp := by
    have e : Xe q c1.1 * Xe q (e2 c1 - 1) = xq q := by
      rw [← Xe_add hx0, ← Xe_DEN q]
      congr 1
      unfold e2
      omega
    have h1 : Xe q c1.1 * r ≤ Xe q c1.1 * Xe q (e2 c1 - 1) := mul_le_mul_of_nonneg_left hsl.2 (Xe_pos hx0 _).le
    have h2 : Xe q c1.1 * r < Kp * r := by rw [mul_comm (Kp : ℝ)]; linarith
    exact lt_of_mul_lt_mul_right h2 hr0.le
  have hKhi : (Kp : ℝ) < Xe q c1.2 := by
    have e : Xe q c1.2 * Xe q (e1 c1 + 1) = Xe q (DEN + 1) := by
      rw [← Xe_add hx0]
      congr 1
      unfold e1
      omega
    have h1 : (Kp : ℝ) * Xe q (e1 c1 + 1) < Kp * r := mul_lt_mul_of_pos_left hsl.1 hK0
    have h2 : (Kp : ℝ) * Xe q (e1 c1 + 1) < Xe q c1.2 * Xe q (e1 c1 + 1) := by
      rw [e]; rw [mul_comm (Kp : ℝ) (r : ℝ)] at h1; linarith
    exact lt_of_mul_lt_mul_right h2 (Xe_pos hx0 _).le
  have hcj := hc j
  rw [hbj] at hcj
  have hcl' := hc (Fin.last k)
  rw [hbl] at hcl'
  have hjK : u j < Kp := by
    have h1 : (u j : ℝ) < Kp := lt_of_lt_of_le hcj.2 ((Xe_mono hx1 hb).trans hKlo.le)
    exact_mod_cast h1
  have hlj : u (Fin.last k) < u j := hsa hj
  have hKn : Kp ∣ n := Dvd.intro_left _ hnK.symm
  rw [Finset.mem_filter]
  refine ⟨mem_famB3 ⟨(Nat.le_of_dvd hn0 hKn).trans (Finset.mem_Ioc.1 hn).2, hK⟩ (hp j) (hp _) hjK hlj
    ⟨hKlo.le, hKhi⟩ hcj hcl', ?_, ?_⟩
  · rw [Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    have h1 : u j * u (Fin.last k) ∣ r := by
      rw [hrdef, ← Finset.prod_pair (ne_of_lt hj)]
      exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
    rw [hnK, mul_assoc, mul_comm r]
    exact Nat.mul_dvd_mul_left _ h1
  · show SieveTree.rough (u (Fin.last k)) n
    intro p hpl hpp hpd
    rw [hnK] at hpd
    rcases (Nat.Prime.dvd_mul hpp).1 hpd with h | h
    · rw [hrdef] at h
      obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).1 h
      have h1 := (Nat.prime_dvd_prime_iff_eq hpp (hp i).2).1 hi
      have h2 := hsa.antitone (Fin.le_last i)
      omega
    · have h1 := (Nat.prime_dvd_prime_iff_eq hpp hK).1 h
      omega

/-- The list of a tuple of an atoms' box that counts `n`, with the position of `c2`: it is good for `n`, the triple
read off it is a tuple of the box that counts `n`, and its position and length are the box's. -/
theorem enc_facts [RouteOK] {q : ℕ} (hq : Big q) {c1 c2 c3 : Cell} (hrev : revOK [c3, c2, c1] = true) {k : ℕ}
    (bx : Fin (k + 1) → Cell) (j : Fin (k + 1)) (hj : j < Fin.last k) (hbj : bx j = c2)
    (hbl : bx (Fin.last k) = c3) {n : ℕ} (hn : n ∈ Ioc (N1 q) (N2 q)) {e : ℕ × List ℕ}
    (he : e ∈ ((famK q (e1 c1 + 1) (e2 c1 - 1) (k + 1) bx).filter
      fun u => (∏ i, u i) ∣ n ∧ (n / ∏ i, u i).Prime).image fun u => ((j : ℕ), List.ofFn u)) :
    GoodL n e ∧ readOff n e ∈ (famB q (boxFn [c3, c2, c1] 3 rfl)).filter
      (fun rt => (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last 2)) n) ∧ (e.1, e.2.length) = ((j : ℕ), k + 1) := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 he
  rw [Finset.mem_filter] at hu
  obtain ⟨hu, hd, hK⟩ := hu
  have hub := (Finset.mem_filter.1 hu).1
  obtain ⟨hp, hsa, -⟩ := mem_famB.1 hub
  refine ⟨⟨hsa.sortedGT_ofFn, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro p hp'
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hp'
    exact (hp i).2
  · simp only [List.prod_ofFn]
    exact hd
  · simp only [List.prod_ofFn]
    exact hK.pos
  · simp only [List.length_ofFn]
    exact j.2
  · rw [readOff_ofFn]
    exact rev_mem hq hrev bx j hj hbj hbl hn hu hd hK
  · simp only [List.length_ofFn]

omit [Route] in
/-- Finite sets on which a function takes two different values are disjoint. -/
theorem disjoint_of_tag {α β : Type*} [DecidableEq α] (f : α → β) {s t : Finset α} {a b : β}
    (hs : ∀ x ∈ s, f x = a) (ht : ∀ x ∈ t, f x = b) (hab : a ≠ b) : Disjoint s t :=
  Finset.disjoint_left.2 fun x hx hy => hab ((hs x hx).symm.trans (ht x hy))

/-- **The tuples of the atoms' boxes that count `n` are tuples of the box that count it, each once.** For a box
`[c3, c2, c1]` that passes `revOK`, at a large modulus, any cells `I1`, `D`, `I2` and `n ∈ (N₁, N₂]`: the tuples
`u` of the five atoms' boxes, with product between `x^{(DEN−h₁+1)/DEN}` and `x^{(DEN−l₁)/DEN}`, `∏u | n` and
`n/∏u` prime, number at most the tuples of the box that count `n`. -/
theorem rev_inject_pt [RouteOK] {q : ℕ} (hq : Big q) {c1 c2 c3 : Cell} (hrev : revOK [c3, c2, c1] = true)
    (I1 D I2 : Cell) {n : ℕ} (hn : n ∈ Ioc (N1 q) (N2 q)) :
    ((famK q (e1 c1 + 1) (e2 c1 - 1) 3 (boxFn [c3, c2, I1] 3 rfl)).filter
        fun u => (∏ i, u i) ∣ n ∧ (n / ∏ i, u i).Prime).card +
      ((famK q (e1 c1 + 1) (e2 c1 - 1) 3 (boxFn [c3, I1, c2] 3 rfl)).filter
        fun u => (∏ i, u i) ∣ n ∧ (n / ∏ i, u i).Prime).card +
      ((famK q (e1 c1 + 1) (e2 c1 - 1) 4 (boxFn [c3, D, I2, c2] 4 rfl)).filter
        fun u => (∏ i, u i) ∣ n ∧ (n / ∏ i, u i).Prime).card +
      ((famK q (e1 c1 + 1) (e2 c1 - 1) 4 (boxFn [c3, D, c2, I2] 4 rfl)).filter
        fun u => (∏ i, u i) ∣ n ∧ (n / ∏ i, u i).Prime).card +
      ((famK q (e1 c1 + 1) (e2 c1 - 1) 4 (boxFn [c3, c2, D, I2] 4 rfl)).filter
        fun u => (∏ i, u i) ∣ n ∧ (n / ∏ i, u i).Prime).card ≤
      ((famB q (boxFn [c3, c2, c1] 3 rfl)).filter
        fun rt => (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last 2)) n).card := by
  obtain ⟨C, hC⟩ : ∃ C, C = (famB q (boxFn [c3, c2, c1] 3 rfl)).filter
      (fun rt => (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last 2)) n) := ⟨_, rfl⟩
  rw [← hC]
  obtain ⟨S1, hS1⟩ : ∃ S1, S1 = (famK q (e1 c1 + 1) (e2 c1 - 1) 3 (boxFn [c3, c2, I1] 3 rfl)).filter
      (fun u => (∏ i, u i) ∣ n ∧ (n / ∏ i, u i).Prime) := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ S2, S2 = (famK q (e1 c1 + 1) (e2 c1 - 1) 3 (boxFn [c3, I1, c2] 3 rfl)).filter
      (fun u => (∏ i, u i) ∣ n ∧ (n / ∏ i, u i).Prime) := ⟨_, rfl⟩
  obtain ⟨S3, hS3⟩ : ∃ S3, S3 = (famK q (e1 c1 + 1) (e2 c1 - 1) 4 (boxFn [c3, D, I2, c2] 4 rfl)).filter
      (fun u => (∏ i, u i) ∣ n ∧ (n / ∏ i, u i).Prime) := ⟨_, rfl⟩
  obtain ⟨S4, hS4⟩ : ∃ S4, S4 = (famK q (e1 c1 + 1) (e2 c1 - 1) 4 (boxFn [c3, D, c2, I2] 4 rfl)).filter
      (fun u => (∏ i, u i) ∣ n ∧ (n / ∏ i, u i).Prime) := ⟨_, rfl⟩
  obtain ⟨S5, hS5⟩ : ∃ S5, S5 = (famK q (e1 c1 + 1) (e2 c1 - 1) 4 (boxFn [c3, c2, D, I2] 4 rfl)).filter
      (fun u => (∏ i, u i) ∣ n ∧ (n / ∏ i, u i).Prime) := ⟨_, rfl⟩
  rw [← hS1, ← hS2, ← hS3, ← hS4, ← hS5]
  obtain ⟨E1, hE1⟩ : ∃ E1 : Finset (ℕ × List ℕ), E1 = S1.image fun u => (((1 : Fin 3) : ℕ), List.ofFn u) :=
    ⟨_, rfl⟩
  obtain ⟨E2, hE2⟩ : ∃ E2 : Finset (ℕ × List ℕ), E2 = S2.image fun u => (((0 : Fin 3) : ℕ), List.ofFn u) :=
    ⟨_, rfl⟩
  obtain ⟨E3, hE3⟩ : ∃ E3 : Finset (ℕ × List ℕ), E3 = S3.image fun u => (((0 : Fin 4) : ℕ), List.ofFn u) :=
    ⟨_, rfl⟩
  obtain ⟨E4, hE4⟩ : ∃ E4 : Finset (ℕ × List ℕ), E4 = S4.image fun u => (((1 : Fin 4) : ℕ), List.ofFn u) :=
    ⟨_, rfl⟩
  obtain ⟨E5, hE5⟩ : ∃ E5 : Finset (ℕ × List ℕ), E5 = S5.image fun u => (((2 : Fin 4) : ℕ), List.ofFn u) :=
    ⟨_, rfl⟩
  have hinj3 : ∀ a : ℕ, Function.Injective fun u : Fin 3 → ℕ => (a, List.ofFn u) :=
    fun a u v h => List.ofFn_injective (Prod.mk.inj h).2
  have hinj4 : ∀ a : ℕ, Function.Injective fun u : Fin 4 → ℕ => (a, List.ofFn u) :=
    fun a u v h => List.ofFn_injective (Prod.mk.inj h).2
  have hc1 : E1.card = S1.card := by rw [hE1]; exact Finset.card_image_of_injective _ (hinj3 _)
  have hc2 : E2.card = S2.card := by rw [hE2]; exact Finset.card_image_of_injective _ (hinj3 _)
  have hc3 : E3.card = S3.card := by rw [hE3]; exact Finset.card_image_of_injective _ (hinj4 _)
  have hc4 : E4.card = S4.card := by rw [hE4]; exact Finset.card_image_of_injective _ (hinj4 _)
  have hc5 : E5.card = S5.card := by rw [hE5]; exact Finset.card_image_of_injective _ (hinj4 _)
  have hf1 : ∀ e ∈ E1, GoodL n e ∧ readOff n e ∈ C ∧ (e.1, e.2.length) = (1, 3) := fun e he => by
    rw [hC]
    exact enc_facts hq hrev (boxFn [c3, c2, I1] 3 rfl) (1 : Fin 3) (by decide) (by rw [boxFn3]; rfl)
      (by rw [boxFn3]; rfl) hn (by rw [hE1, hS1] at he; exact he)
  have hf2 : ∀ e ∈ E2, GoodL n e ∧ readOff n e ∈ C ∧ (e.1, e.2.length) = (0, 3) := fun e he => by
    rw [hC]
    exact enc_facts hq hrev (boxFn [c3, I1, c2] 3 rfl) (0 : Fin 3) (by decide) (by rw [boxFn3]; rfl)
      (by rw [boxFn3]; rfl) hn (by rw [hE2, hS2] at he; exact he)
  have hf3 : ∀ e ∈ E3, GoodL n e ∧ readOff n e ∈ C ∧ (e.1, e.2.length) = (0, 4) := fun e he => by
    rw [hC]
    exact enc_facts hq hrev (boxFn [c3, D, I2, c2] 4 rfl) (0 : Fin 4) (by decide) (by rw [boxFn4]; rfl)
      (by rw [boxFn4]; rfl) hn (by rw [hE3, hS3] at he; exact he)
  have hf4 : ∀ e ∈ E4, GoodL n e ∧ readOff n e ∈ C ∧ (e.1, e.2.length) = (1, 4) := fun e he => by
    rw [hC]
    exact enc_facts hq hrev (boxFn [c3, D, c2, I2] 4 rfl) (1 : Fin 4) (by decide) (by rw [boxFn4]; rfl)
      (by rw [boxFn4]; rfl) hn (by rw [hE4, hS4] at he; exact he)
  have hf5 : ∀ e ∈ E5, GoodL n e ∧ readOff n e ∈ C ∧ (e.1, e.2.length) = (2, 4) := fun e he => by
    rw [hC]
    exact enc_facts hq hrev (boxFn [c3, c2, D, I2] 4 rfl) (2 : Fin 4) (by decide) (by rw [boxFn4]; rfl)
      (by rw [boxFn4]; rfl) hn (by rw [hE5, hS5] at he; exact he)
  have hall : ∀ e ∈ E1 ∪ E2 ∪ E3 ∪ E4 ∪ E5, GoodL n e ∧ readOff n e ∈ C := by
    intro e he
    simp only [Finset.mem_union] at he
    rcases he with (((he | he) | he) | he) | he
    · exact ⟨(hf1 e he).1, (hf1 e he).2.1⟩
    · exact ⟨(hf2 e he).1, (hf2 e he).2.1⟩
    · exact ⟨(hf3 e he).1, (hf3 e he).2.1⟩
    · exact ⟨(hf4 e he).1, (hf4 e he).2.1⟩
    · exact ⟨(hf5 e he).1, (hf5 e he).2.1⟩
  have hinj : (E1 ∪ E2 ∪ E3 ∪ E4 ∪ E5).card ≤ C.card :=
    Finset.card_le_card_of_injOn (readOff n) (fun e he => (hall e he).2)
      fun e he e' he' h => readOff_inj (hall e he).1 (hall e' he').1 h
  have dj : ∀ {s t : Finset (ℕ × List ℕ)} {a b : ℕ × ℕ}, (∀ e ∈ s, (e.1, e.2.length) = a) →
      (∀ e ∈ t, (e.1, e.2.length) = b) → a ≠ b → Disjoint s t :=
    fun hs ht hab => disjoint_of_tag (fun e : ℕ × List ℕ => (e.1, e.2.length)) hs ht hab
  have t1 := fun e he => (hf1 e he).2.2
  have t2 := fun e he => (hf2 e he).2.2
  have t3 := fun e he => (hf3 e he).2.2
  have t4 := fun e he => (hf4 e he).2.2
  have t5 := fun e he => (hf5 e he).2.2
  have d2 : Disjoint E1 E2 := dj t1 t2 (by decide)
  have d3 : Disjoint (E1 ∪ E2) E3 := Finset.disjoint_union_left.2 ⟨dj t1 t3 (by decide), dj t2 t3 (by decide)⟩
  have d4 : Disjoint (E1 ∪ E2 ∪ E3) E4 :=
    Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2 ⟨dj t1 t4 (by decide), dj t2 t4 (by decide)⟩,
      dj t3 t4 (by decide)⟩
  have d5 : Disjoint (E1 ∪ E2 ∪ E3 ∪ E4) E5 :=
    Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2
      ⟨dj t1 t5 (by decide), dj t2 t5 (by decide)⟩, dj t3 t5 (by decide)⟩, dj t4 t5 (by decide)⟩
  have hcard : (E1 ∪ E2 ∪ E3 ∪ E4 ∪ E5).card = E1.card + E2.card + E3.card + E4.card + E5.card := by
    rw [Finset.card_union_of_disjoint d5, Finset.card_union_of_disjoint d4, Finset.card_union_of_disjoint d3,
      Finset.card_union_of_disjoint d2]
  omega

/-- **The primes over the atoms' boxes are terms of the box.** For a box `[c3, c2, c1]` that passes `revOK`, at a
large modulus, weights `g ≥ 0` and any cells `I1`, `D`, `I2`: the sum over the five atoms' boxes of the weights of
the `n = p·r'`, `p` prime and `r'` between `x^{(DEN−h₁+1)/DEN}` and `x^{(DEN−l₁)/DEN}`, is at most the term of the
box. -/
theorem rev_inject [RouteOK] {q : ℕ} (hq : Big q) {c1 c2 c3 : Cell} (hrev : revOK [c3, c2, c1] = true) (g : ℕ → ℝ)
    (hg : ∀ n, 0 ≤ g n) (I1 D I2 : Cell) :
    famPr g (N1 q) (N2 q) (famK q (e1 c1 + 1) (e2 c1 - 1) 3 (boxFn [c3, c2, I1] 3 rfl)) +
      famPr g (N1 q) (N2 q) (famK q (e1 c1 + 1) (e2 c1 - 1) 3 (boxFn [c3, I1, c2] 3 rfl)) +
      famPr g (N1 q) (N2 q) (famK q (e1 c1 + 1) (e2 c1 - 1) 4 (boxFn [c3, D, I2, c2] 4 rfl)) +
      famPr g (N1 q) (N2 q) (famK q (e1 c1 + 1) (e2 c1 - 1) 4 (boxFn [c3, D, c2, I2] 4 rfl)) +
      famPr g (N1 q) (N2 q) (famK q (e1 c1 + 1) (e2 c1 - 1) 4 (boxFn [c3, c2, D, I2] 4 rfl)) ≤
      famI g (N1 q) (N2 q) (famB q (boxFn [c3, c2, c1] 3 rfl)) := by
  rw [famI_eq_sum_card, famPr_eq_sum_card, famPr_eq_sum_card, famPr_eq_sum_card, famPr_eq_sum_card,
    famPr_eq_sum_card, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [← mul_add, ← mul_add, ← mul_add, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (hg n)
  exact_mod_cast rev_inject_pt hq hrev I1 D I2 hn

end SieveAd

#print axioms SieveAd.rev_inject
