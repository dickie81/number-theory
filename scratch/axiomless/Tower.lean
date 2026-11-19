import AxiomTools

/-!
# Number theory with no axioms

Every theorem and definition of this file depends on no axiom: not `propext`, not `Quot.sound`, not
`Classical.choice`. The last command of the file checks it. Lean core's own lemmas on division, divisibility and
subtraction mostly depend on `propext` (LOG.md, entry 3), so the file proves what it needs from the lemmas of core
that are free of axioms, with `induction`, `cases`, `rw` by equations, `exact` and `decide`.

Because nothing here is an axiom, every definition computes in the kernel: the proof that there is a prime above
`n` is a function that returns one (`nextPrime`), and the proof that a number is a product of primes is a function
that factors it (`factor`).
-/

namespace Ax

universe u

/-! ## Arithmetic -/

theorem mul_assoc (a b c : Nat) : a * b * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ c ih => rw [Nat.mul_add_one, Nat.mul_add_one, Nat.left_distrib, ih]

theorem add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm (a + b) c, Nat.left_distrib, Nat.mul_comm c a, Nat.mul_comm c b]

theorem add_sub_cancel (a b : Nat) : a + b - b = a := by
  induction b with
  | zero => rfl
  | succ b ih => exact (Nat.succ_sub_succ (a + b) b).trans ih

theorem add_left_cancel {a b c : Nat} (h : a + b = a + c) : b = c := by
  have h1 : a + b - a = a + c - a := congrArg (· - a) h
  rw [Nat.add_comm a b, Nat.add_comm a c, add_sub_cancel, add_sub_cancel] at h1
  exact h1

theorem eq_zero_of_add_eq_self {a b : Nat} (h : a + b = a) : b = 0 :=
  add_left_cancel (h.trans (Nat.add_zero a).symm)

theorem succ_ne_zero (n : Nat) : n + 1 ≠ 0 := fun h => Nat.noConfusion h

theorem pos_of_mul_pos_right {a b : Nat} (h : 0 < a * b) : 0 < b :=
  Nat.pos_of_ne_zero fun hb => by rw [hb, Nat.mul_zero] at h; exact Nat.lt_irrefl 0 h

theorem pos_of_mul_pos_left {a b : Nat} (h : 0 < a * b) : 0 < a :=
  pos_of_mul_pos_right (Nat.mul_comm a b ▸ h)

/-! ## Divisibility -/

theorem dvd_refl (a : Nat) : a ∣ a := ⟨1, (Nat.mul_one a).symm⟩

theorem dvd_zero (a : Nat) : a ∣ 0 := ⟨0, rfl⟩

theorem dvd_trans {a b c : Nat} : a ∣ b → b ∣ c → a ∣ c
  | ⟨x, hx⟩, ⟨y, hy⟩ => ⟨x * y, by rw [hy, hx, mul_assoc]⟩

theorem dvd_mul_right_of_dvd {a b : Nat} (h : a ∣ b) (c : Nat) : a ∣ b * c :=
  dvd_trans h (Nat.dvd_mul_right b c)

theorem dvd_add {a b c : Nat} : a ∣ b → a ∣ c → a ∣ b + c
  | ⟨x, hx⟩, ⟨y, hy⟩ => ⟨x + y, by rw [hx, hy, Nat.left_distrib]⟩

/-- If `a` divides `b + c` and `b`, it divides `c`. No subtraction is needed. -/
theorem dvd_of_dvd_add {a b c : Nat} : a ∣ b + c → a ∣ b → a ∣ c
  | ⟨y, hy⟩, ⟨x, hx⟩ => by
    cases Nat.le_total x y with
    | inl hxy =>
      obtain ⟨k, hk⟩ := Nat.le.dest hxy
      refine ⟨k, add_left_cancel (a := b) ?_⟩
      rw [hy, ← hk, Nat.left_distrib, hx]
    | inr hyx =>
      obtain ⟨k, hk⟩ := Nat.le.dest hyx
      have h0 : c + a * k = 0 := by
        apply eq_zero_of_add_eq_self (a := b)
        rw [← Nat.add_assoc, hy, ← Nat.left_distrib, hk, hx]
      rw [Nat.eq_zero_of_add_eq_zero_right h0]
      exact dvd_zero a

theorem le_of_dvd {a b : Nat} (hb : 0 < b) : a ∣ b → a ≤ b
  | ⟨c, hc⟩ => by
    have hc0 : 0 < c := pos_of_mul_pos_right (hc ▸ hb)
    rw [hc]
    exact Nat.le_mul_of_pos_right a hc0

theorem eq_zero_of_zero_dvd {a : Nat} : 0 ∣ a → a = 0
  | ⟨c, hc⟩ => by rw [hc, Nat.zero_mul]

/-- A remainder strictly between `0` and `d` witnesses that `d` does not divide `n`. -/
theorem not_dvd_of_rem {d q r n : Nat} (hr0 : 0 < r) (hrd : r < d) (h : d * q + r = n) : ¬ d ∣ n
  | ⟨c, hc⟩ => by
    cases Nat.lt_or_ge q c with
    | inr hcq =>
      -- n = d * c ≤ d * q < d * q + r = n
      have h1 : d * c ≤ d * q := Nat.mul_le_mul_left d hcq
      have h2 : d * q < d * q + r := Nat.lt_add_of_pos_right hr0
      rw [h, hc] at h2
      exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt h1 h2)
    | inl hqc =>
      -- n = d * q + r < d * q + d = d * (q + 1) ≤ d * c = n
      have h1 : d * (q + 1) ≤ d * c := Nat.mul_le_mul_left d hqc
      have h2 : d * q + r < d * q + d := Nat.add_lt_add_left hrd (d * q)
      rw [h, hc, ← Nat.mul_add_one] at h2
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h2 h1)

/-! ## Search

`P` is a decidable predicate. `search` looks for the least number satisfying `P`, from `start` upwards, for `fuel`
steps, where `start + fuel = bound`. It returns the least one, or a proof that there is none below `bound`. -/

/-- `k n`, with `n` evaluated first. The kernel substitutes arguments unevaluated, so a number that a recursion
passes on (`start + 1`, then `start + 1 + 1`, …) would be recomputed at every use; the match makes the kernel
reduce `n` to a numeral, and passes the numeral. -/
def strict {α : Nat → Sort u} (n : Nat) (k : (m : Nat) → α m) : α n :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

/-- The recursive call is the whole result of a step, so the kernel's evaluation does not nest. -/
def search (P : Nat → Prop) [DecidablePred P] (bound : Nat) :
    (fuel start : Nat) → start + fuel = bound → (∀ k, k < start → ¬ P k) →
      {m : Nat // P m ∧ ∀ k, k < m → ¬ P k} ⊕' (∀ k, k < bound → ¬ P k)
  | 0, _, he, h => .inr (he ▸ h)
  | f + 1, s, he, h =>
    if hp : P s then .inl ⟨s, hp, h⟩
    else
      strict (α := fun t => t + f = bound → (∀ k, k < t → ¬ P k) →
          {m : Nat // P m ∧ ∀ k, k < m → ¬ P k} ⊕' (∀ k, k < bound → ¬ P k)) (s + 1)
        (fun t he' ht => search P bound f t he' ht)
        ((Nat.succ_add_eq_add_succ s f).trans he)
        (fun k hk hpk => (Nat.lt_succ_iff_lt_or_eq.mp hk).elim (fun hlt => h k hlt hpk) (fun heq => hp (heq ▸ hpk)))

/-- The least number principle for a decidable predicate, as a function: from one `n` with `P n`, the least. -/
def least (P : Nat → Prop) [DecidablePred P] (n : Nat) (h : P n) : {m : Nat // P m ∧ ∀ k, k < m → ¬ P k} :=
  match search P (n + 1) (n + 1) 0 (Nat.zero_add _) (fun k hk => absurd hk (Nat.not_lt_zero k)) with
  | .inl r => r
  | .inr hno => absurd h (hno n (Nat.lt_succ_self n))

/-- A bounded existential over a decidable predicate is decidable. Core's instance depends on `propext`. -/
def decExistsLT (P : Nat → Prop) [DecidablePred P] (n : Nat) : Decidable (∃ k, k < n ∧ P k) :=
  match search P n n 0 (Nat.zero_add _) (fun k hk => absurd hk (Nat.not_lt_zero k)) with
  | .inl ⟨m, hm, hmin⟩ =>
    -- the least `m` with `P m`: it is below `n` or it is not
    if hmn : m < n then .isTrue ⟨m, hmn, hm⟩
    else .isFalse (fun ⟨k, hk, hpk⟩ => by
      cases Nat.lt_or_ge k m with
      | inl hkm => exact hmin k hkm hpk
      | inr hmk => exact hmn (Nat.lt_of_le_of_lt hmk hk))
  | .inr hno => .isFalse (fun ⟨k, hk, hpk⟩ => hno k hk hpk)

/-! ## Deciding divisibility

`n / d` and `n % d` are computed by core's functions, which the kernel runs on numerals with GMP. Nothing is used
about what they compute: the quotient and the remainder are only checked. If neither check succeeds (it cannot
happen, but core's proof of that depends on `propext`), a bounded search decides. -/

theorem dvd_iff_exists_lt {d n : Nat} : d ∣ n ↔ ∃ c, c < n + 1 ∧ n = d * c := by
  constructor
  · intro ⟨c, hc⟩
    cases Nat.eq_zero_or_pos d with
    | inl hd => exact ⟨0, Nat.succ_pos n, by rw [hc, hd, Nat.zero_mul, Nat.zero_mul]⟩
    | inr hd => exact ⟨c, Nat.lt_succ_of_le (hc ▸ Nat.le_mul_of_pos_left c hd), hc⟩
  · intro ⟨c, _, hc⟩
    exact ⟨c, hc⟩

instance decDvd (d n : Nat) : Decidable (d ∣ n) :=
  if h : d * (n / d) = n then .isTrue ⟨n / d, h.symm⟩
  else if h' : 0 < n % d ∧ n % d < d ∧ d * (n / d) + n % d = n then .isFalse (not_dvd_of_rem h'.1 h'.2.1 h'.2.2)
  else
    match decExistsLT (fun c => n = d * c) (n + 1) with
    | .isTrue h => .isTrue (dvd_iff_exists_lt.mpr h)
    | .isFalse h => .isFalse (fun hd => h (dvd_iff_exists_lt.mp hd))

/-! ## Primes -/

def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

theorem Prime.pos {p : Nat} (hp : Prime p) : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1

/-- The least divisor of `n` that is at least `2` is prime. -/
def primeFactor (n : Nat) (h : 2 ≤ n) : {p : Nat // Prime p ∧ p ∣ n} :=
  match least (fun d => 2 ≤ d ∧ d ∣ n) n ⟨h, dvd_refl n⟩ with
  | ⟨m, ⟨hm2, hmn⟩, hmin⟩ =>
    ⟨m, ⟨hm2, fun d hd => by
      have hm0 : 0 < m := Nat.lt_of_lt_of_le (by decide) hm2
      cases Nat.lt_or_ge d 2 with
      | inl hd2 =>
        cases d with
        | zero => exact absurd (eq_zero_of_zero_dvd hd) (Nat.ne_of_gt hm0)
        | succ d =>
          cases d with
          | zero => exact Or.inl rfl
          | succ d => exact absurd hd2 (Nat.not_lt_of_le (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le d))))
      | inr hd2 =>
        cases Nat.eq_or_lt_of_le (le_of_dvd hm0 hd) with
        | inl heq => exact Or.inr heq
        | inr hlt => exact absurd ⟨hd2, dvd_trans hd hmn⟩ (hmin d hlt)⟩, hmn⟩

theorem exists_prime_dvd {n : Nat} (h : 2 ≤ n) : ∃ p, Prime p ∧ p ∣ n :=
  ⟨(primeFactor n h).1, (primeFactor n h).2⟩

/-! ## Euclid: there is a prime above every number -/

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos : ∀ n, 0 < fact n
  | 0 => Nat.zero_lt_one
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

theorem dvd_fact : ∀ {k n : Nat}, 0 < k → k ≤ n → k ∣ fact n
  | _, 0, hk, hle => absurd hk (Nat.not_lt_of_le hle)
  | _, n + 1, hk, hle =>
    match Nat.le_or_eq_of_le_succ hle with
    | .inl h => dvd_trans (dvd_fact hk h) (Nat.dvd_mul_left (fact n) (n + 1))
    | .inr h => h ▸ Nat.dvd_mul_right (n + 1) (fact n)

/-- Euclid's proof, as a function: a prime factor of `n! + 1` is a prime above `n`. -/
def nextPrime (n : Nat) : {p : Nat // n < p ∧ Prime p} :=
  match primeFactor (fact n + 1) (Nat.succ_le_succ (fact_pos n)) with
  | ⟨p, hp, hdvd⟩ =>
    ⟨p, Nat.lt_of_not_le fun hle =>
      have h1 : p ∣ 1 := dvd_of_dvd_add hdvd (dvd_fact hp.pos hle)
      absurd hp.1 (Nat.not_le_of_lt (Nat.lt_succ_of_le (le_of_dvd Nat.zero_lt_one h1))), hp⟩

theorem exists_prime_gt (n : Nat) : ∃ p, n < p ∧ Prime p :=
  ⟨(nextPrime n).1, (nextPrime n).2⟩

/-- Primality is decidable: `p ≥ 2` is prime if and only if its least divisor above `1` is `p`. -/
instance decPrime (p : Nat) : Decidable (Prime p) :=
  if h : 2 ≤ p then
    if e : (primeFactor p h).1 = p then .isTrue (e ▸ (primeFactor p h).2.1)
    else .isFalse fun hp =>
      (hp.2 _ (primeFactor p h).2.2).elim
        (fun h1 => absurd (primeFactor p h).2.1.1 (h1 ▸ by decide)) e
  else .isFalse fun hp => h hp.1

/-! ## Division with remainder, and Euclid's lemma -/

theorem div_rem (d : Nat) (hd : 0 < d) : ∀ n, ∃ q r, n = d * q + r ∧ r < d
  | 0 => ⟨0, 0, rfl, hd⟩
  | n + 1 => by
    obtain ⟨q, r, h, hr⟩ := div_rem d hd n
    cases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hr) with
    | inl heq =>
      have heq' : r + 1 = d := heq
      refine ⟨q + 1, 0, ?_, hd⟩
      rw [h, Nat.mul_add_one, Nat.add_assoc, heq']
      rfl
    | inr hlt => exact ⟨q, r + 1, by rw [h, Nat.add_assoc], hlt⟩

/-- Euclid's lemma. The least `m > 0` with `p ∣ m * b` divides every such number, among them `p` and `a`. -/
theorem Prime.dvd_mul {p a b : Nat} (hp : Prime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  cases decDvd p a with
  | isTrue hpa => exact Or.inl hpa
  | isFalse hpa =>
    refine Or.inr ?_
    obtain ⟨m, ⟨hm0, hmb⟩, hmin⟩ := least (fun x => 0 < x ∧ p ∣ x * b) p ⟨hp.pos, Nat.dvd_mul_right p b⟩
    have key : ∀ x, 0 < x → p ∣ x * b → m ∣ x := by
      intro x hx hxb
      obtain ⟨q, r, hqr, hr⟩ := div_rem m hm0 x
      cases Nat.eq_zero_or_pos r with
      | inl hr0 => exact ⟨q, by rw [hqr, hr0, Nat.add_zero]⟩
      | inr hr0 =>
        have h1 : p ∣ m * q * b + r * b := by rw [← add_mul, ← hqr]; exact hxb
        have h2 : p ∣ m * q * b := by
          rw [mul_assoc, Nat.mul_comm q b, ← mul_assoc]; exact dvd_mul_right_of_dvd hmb q
        exact absurd ⟨hr0, dvd_of_dvd_add h1 h2⟩ (hmin r hr)
    have ha0 : 0 < a := Nat.pos_of_ne_zero fun h0 => hpa (h0 ▸ dvd_zero p)
    cases hp.2 m (key p hp.pos (Nat.dvd_mul_right p b)) with
    | inl h1 => rw [h1, Nat.one_mul] at hmb; exact hmb
    | inr hmp => exact absurd (hmp ▸ key a ha0 h) hpa

/-- The square root of a prime is irrational: `a² = p·b²` only with `b = 0`. By descent from `(a, b)` to `(b, a/p)`. -/
theorem Prime.sq_ne {p : Nat} (hp : Prime p) (a : Nat) : ∀ b, a * a = p * (b * b) → b = 0 := by
  induction a using Nat.strongRecOn with
  | _ a ih =>
    intro b h
    cases Nat.eq_zero_or_pos b with
    | inl hb => exact hb
    | inr hb =>
      have hpa : p ∣ a := (hp.dvd_mul ⟨b * b, h⟩).elim id id
      obtain ⟨c, hc⟩ := hpa
      -- b * b = p * (c * c)
      have h' : b * b = p * (c * c) := by
        apply Nat.eq_of_mul_eq_mul_left hp.pos
        rw [← h, hc, mul_assoc, Nat.mul_comm c (p * c), mul_assoc]
      -- b < a
      have hbb : 0 < b * b := Nat.mul_pos hb hb
      have hlt : b * b < a * a := by
        rw [h]
        exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hbb) (Nat.two_mul (b * b) ▸ Nat.mul_le_mul_right (b * b) hp.1)
      have hba : b < a := Nat.lt_of_not_le fun hab => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt (Nat.mul_le_mul hab hab))
      have hc0 : c = 0 := ih b hba c h'
      rw [hc0] at h'
      exact (Nat.mul_eq_zero.mp h').elim id id

/-! ## The fundamental theorem of arithmetic -/

def prod : List Nat → Nat
  | [] => 1
  | a :: l => a * prod l

def AllPrime : List Nat → Prop
  | [] => True
  | a :: l => Prime a ∧ AllPrime l

/-- From a proof that `d` divides `n`, the quotient: core's `n / d` if it passes the check, else a search. -/
def quot (d n : Nat) (hd : 0 < d) (h : d ∣ n) : {c : Nat // n = d * c} :=
  if hq : n = d * (n / d) then ⟨n / d, hq⟩
  else
    match search (fun c => n = d * c) (n + 1) (n + 1) 0 (Nat.zero_add _) (fun k hk => absurd hk (Nat.not_lt_zero k)) with
    | .inl ⟨c, hc, _⟩ => ⟨c, hc⟩
    | .inr hno => False.elim <|
      let ⟨c, hc⟩ := h
      hno c (Nat.lt_succ_of_le (hc ▸ Nat.le_mul_of_pos_left c hd)) hc

/-- Existence, as a function: split off the least prime factor, at most `fuel` times. The quotient is matched
against `0` and `m + 1` so that the kernel evaluates it before the next step (see `strict`). -/
def factorFuel : (fuel n : Nat) → 0 < n → n ≤ fuel → {l : List Nat // AllPrime l ∧ prod l = n}
  | 0, _, hn, hle => absurd hn (Nat.not_lt_of_le hle)
  | f + 1, n, hn, hle =>
    if h1 : n = 1 then ⟨[], trivial, h1.symm⟩
    else
      have h2 : 2 ≤ n := Nat.lt_of_le_of_ne hn (fun h => h1 h.symm)
      match primeFactor n h2 with
      | ⟨p, hp, hpn⟩ =>
        match quot p n hp.pos hpn with
        | ⟨0, hm⟩ => absurd hn (by rw [hm, Nat.mul_zero]; exact Nat.lt_irrefl 0)
        | ⟨m + 1, hm⟩ =>
          have hmn : m + 1 < n := by
            rw [hm]
            exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.succ_pos m))
              (Nat.two_mul (m + 1) ▸ Nat.mul_le_mul_right (m + 1) hp.1)
          match factorFuel f (m + 1) (Nat.succ_pos m) (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hmn hle)) with
          | ⟨l, hl, hprod⟩ => ⟨p :: l, ⟨hp, hl⟩, by rw [hm, ← hprod]; rfl⟩

/-- Every positive number is a product of primes. The list comes out in increasing order. -/
def factor (n : Nat) (hn : 0 < n) : {l : List Nat // AllPrime l ∧ prod l = n} :=
  factorFuel n n hn (Nat.le_refl n)

theorem exists_factorization {n : Nat} (hn : 0 < n) : ∃ l, AllPrime l ∧ prod l = n :=
  ⟨(factor n hn).1, (factor n hn).2⟩

/-- How many times `q` occurs in a list. -/
def count (q : Nat) : List Nat → Nat
  | [] => 0
  | a :: l => if a = q then count q l + 1 else count q l

theorem count_cons_eq {q a : Nat} (l : List Nat) (h : a = q) : count q (a :: l) = count q l + 1 := by
  show (if a = q then count q l + 1 else count q l) = count q l + 1
  split
  · rfl
  · contradiction

theorem count_cons_ne {q a : Nat} (l : List Nat) (h : a ≠ q) : count q (a :: l) = count q l := by
  show (if a = q then count q l + 1 else count q l) = count q l
  split
  · contradiction
  · rfl

theorem prime_of_count_pos {q : Nat} : ∀ {l : List Nat}, AllPrime l → 0 < count q l → Prime q
  | [], _, h => absurd h (Nat.lt_irrefl 0)
  | a :: l, hl, h => by
    cases Nat.decEq a q with
    | isTrue haq => exact haq ▸ hl.1
    | isFalse haq => rw [count_cons_ne l haq] at h; exact prime_of_count_pos hl.2 h

/-- `q ^ (count q l)` divides the product of `l`. -/
theorem pow_count_dvd (q : Nat) : ∀ l : List Nat, q ^ count q l ∣ prod l
  | [] => dvd_refl 1
  | a :: l => by
    cases Nat.decEq a q with
    | isTrue haq =>
      obtain ⟨c, hc⟩ := pow_count_dvd q l
      refine ⟨c, ?_⟩
      show a * prod l = _
      rw [count_cons_eq l haq, Nat.pow_succ, hc, haq, mul_assoc, Nat.mul_comm (q ^ count q l) (q * c),
        mul_assoc, Nat.mul_comm c]
    | isFalse haq =>
      rw [count_cons_ne l haq]
      exact dvd_trans (pow_count_dvd q l) (Nat.dvd_mul_left (prod l) a)

/-- A power of a prime `q` that divides `a * m`, with `a` a prime other than `q`, divides `m`. -/
theorem pow_dvd_of_dvd_mul {q a : Nat} (hq : Prime q) (ha : Prime a) (hne : a ≠ q) :
    ∀ (k m : Nat), q ^ k ∣ a * m → q ^ k ∣ m
  | 0, m, _ => Nat.one_dvd m
  | k + 1, m, ⟨c, hc⟩ => by
    have hqm : q ∣ m := by
      have : q ∣ a * m := ⟨q ^ k * c, by rw [hc, Nat.pow_succ, Nat.mul_comm (q ^ k) q, mul_assoc]⟩
      cases hq.dvd_mul this with
      | inl hqa =>
        cases ha.2 q hqa with
        | inl h1 => exact absurd hq.1 (h1 ▸ by decide)
        | inr h2 => exact absurd h2.symm hne
      | inr h => exact h
    obtain ⟨m', hm'⟩ := hqm
    have : q ^ k ∣ a * m' := by
      refine ⟨c, Nat.eq_of_mul_eq_mul_left hq.pos ?_⟩
      rw [← mul_assoc, Nat.mul_comm q a, mul_assoc, ← hm', hc, Nat.pow_succ, Nat.mul_comm (q ^ k) q, mul_assoc]
    obtain ⟨e, he⟩ := pow_dvd_of_dvd_mul hq ha hne k m' this
    exact ⟨e, by rw [hm', he, Nat.pow_succ, Nat.mul_comm (q ^ k) q, mul_assoc]⟩

/-- If `q ^ k` divides a product of primes, then `q` occurs at least `k` times among them. -/
theorem le_count_of_pow_dvd {q : Nat} (hq : Prime q) : ∀ (l : List Nat), AllPrime l → ∀ k, q ^ k ∣ prod l → k ≤ count q l
  | [], _, k, h => by
    cases k with
    | zero => exact Nat.le_refl 0
    | succ k =>
      have h1 : q ∣ 1 := dvd_trans ⟨q ^ k, by rw [Nat.pow_succ, Nat.mul_comm]⟩ h
      exact absurd hq.1 (Nat.not_le_of_lt (Nat.lt_succ_of_le (le_of_dvd Nat.zero_lt_one h1)))
  | a :: l, hl, k, h => by
    cases Nat.decEq a q with
    | isTrue haq =>
      rw [count_cons_eq l haq]
      cases k with
      | zero => exact Nat.zero_le _
      | succ k =>
        obtain ⟨c, hc⟩ := h
        apply Nat.succ_le_succ
        apply le_count_of_pow_dvd hq l hl.2 k
        refine ⟨c, Nat.eq_of_mul_eq_mul_left hq.pos ?_⟩
        have hc' : q * prod l = q ^ (k + 1) * c := haq ▸ hc
        rw [hc', Nat.pow_succ, Nat.mul_comm (q ^ k) q, mul_assoc]
    | isFalse haq =>
      rw [count_cons_ne l haq]
      exact le_count_of_pow_dvd hq l hl.2 k (pow_dvd_of_dvd_mul hq hl.1 haq k (prod l) h)

/-- Uniqueness: two lists of primes with the same product hold each number the same number of times. -/
theorem factorization_unique {l₁ l₂ : List Nat} (h₁ : AllPrime l₁) (h₂ : AllPrime l₂) (h : prod l₁ = prod l₂)
    (q : Nat) : count q l₁ = count q l₂ := by
  have half : ∀ {l l' : List Nat}, AllPrime l → AllPrime l' → prod l = prod l' → count q l ≤ count q l' := by
    intro l l' hl hl' hp
    cases Nat.eq_zero_or_pos (count q l) with
    | inl h0 => rw [h0]; exact Nat.zero_le _
    | inr hpos => exact le_count_of_pow_dvd (prime_of_count_pos hl hpos) l' hl' _ (hp ▸ pow_count_dvd q l)
  exact Nat.le_antisymm (half h₁ h₂ h) (half h₂ h₁ h.symm)

end Ax

#axioms_table Ax
