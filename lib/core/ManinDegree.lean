/-
# The degree of a rational function, and Gauss's lemma for two linear forms

Plain statement. For a rational function `x ∈ k(t)` written as `p/q` in lowest terms, `rdeg x = max (deg p) (deg q)`
(`rdeg_div`). If `x₁ + x₂ = W₁/W₀` and `x₁x₂ = W₂/W₀` for polynomials `W₀ ≠ 0`, `W₁`, `W₂` with no common
non-unit factor, then `rdeg x₁ + rdeg x₂ = max (deg W₀) (deg W₁) (deg W₂)` (`rdeg_add_rdeg_of_vieta`). No hypothesis.

This is the degree bookkeeping of Manin's proof of Hasse's bound (`ManinHasse`): the `x`-coordinates of `P + P₀` and
`P − P₀` are the two roots of `W₀Z² − W₁Z + W₂`, and the sum of their degrees is read off the coefficients.
* `rdeg_div`: mutual divisibility of the two lowest-terms representations.
* `max_natDegree_prod`: Gauss's lemma for the degree at infinity. The top coefficients of
  `(s₁Z − r₁)(s₂Z − r₂)` are the product of the top coefficients of the factors, and `k[Z]` is a domain.
* `prim3_prod`: Gauss's lemma for primes. A prime dividing the three coefficients of `(s₁Z − r₁)(s₂Z − r₂)` divides
  both coefficients of one factor.
* `rdeg_add_rdeg_of_vieta`: two triples of polynomials with no common factor that are proportional over `k(t)` differ
  by a nonzero constant.
-/
import Mathlib

open Polynomial

namespace ManinDegree

variable {k : Type*} [Field k]

/-- The degree of a rational function: the larger of the degrees of its numerator and denominator in lowest terms. -/
noncomputable def rdeg (x : RatFunc k) : ℕ := max x.num.natDegree x.denom.natDegree

/-- Three polynomials with no common non-unit factor. -/
def Prim3 (a b c : k[X]) : Prop := ∀ d : k[X], d ∣ a → d ∣ b → d ∣ c → IsUnit d

lemma natDegree_eq_of_dvd_dvd {p q : k[X]} (h₁ : p ∣ q) (h₂ : q ∣ p) : p.natDegree = q.natDegree :=
  natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (associated_of_dvd_dvd h₁ h₂))

/-- **The degree of `p/q` in lowest terms is `max (deg p) (deg q)`.** -/
lemma rdeg_div {p q : k[X]} (hpq : IsCoprime p q) (hq : q ≠ 0) :
    rdeg (algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q) = max p.natDegree q.natDegree := by
  set x := algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q
  have h : x.num * q = p * x.denom := (RatFunc.num_mul_eq_mul_denom_iff hq).2 rfl
  have hc := RatFunc.isCoprime_num_denom x
  have h1 : q ∣ x.denom := hpq.symm.dvd_of_dvd_mul_left (h ▸ dvd_mul_left q x.num)
  have h2 : x.denom ∣ q := hc.symm.dvd_of_dvd_mul_left (h.symm ▸ dvd_mul_left x.denom p)
  have h3 : p ∣ x.num := hpq.dvd_of_dvd_mul_right (h.symm ▸ dvd_mul_right p x.denom)
  have h4 : x.num ∣ p := hc.dvd_of_dvd_mul_right (h ▸ dvd_mul_right x.num q)
  rw [rdeg, natDegree_eq_of_dvd_dvd h4 h3, natDegree_eq_of_dvd_dvd h2 h1]

/-- The degree of a polynomial as a rational function is its degree. -/
lemma rdeg_algebraMap (p : k[X]) : rdeg (algebraMap k[X] (RatFunc k) p) = p.natDegree := by
  have h := rdeg_div (p := p) (q := 1) isCoprime_one_right one_ne_zero
  rw [map_one, div_one] at h
  rw [h, natDegree_one]
  exact max_eq_left (Nat.zero_le _)

/-- The coefficient of `t^(max (deg r) (deg s))` in `r` or in `s` is nonzero. -/
lemma coeff_max_ne_zero {r s : k[X]} (h : r ≠ 0 ∨ s ≠ 0) :
    r.coeff (max r.natDegree s.natDegree) ≠ 0 ∨ s.coeff (max r.natDegree s.natDegree) ≠ 0 := by
  rcases le_total r.natDegree s.natDegree with hrs | hsr
  · rw [max_eq_right hrs]
    by_cases hs : s = 0
    · have hr : r ≠ 0 := h.resolve_right (not_not.2 hs)
      have h0 : r.natDegree = 0 := by
        have := hrs; rw [hs, natDegree_zero] at this; omega
      left
      rw [hs, natDegree_zero, ← h0]
      exact leadingCoeff_ne_zero.2 hr
    · exact Or.inr (leadingCoeff_ne_zero.2 hs)
  · rw [max_eq_left hsr]
    by_cases hr : r = 0
    · have hs : s ≠ 0 := h.resolve_left (not_not.2 hr)
      have h0 : s.natDegree = 0 := by
        have := hsr; rw [hr, natDegree_zero] at this; omega
      right
      rw [hr, natDegree_zero, ← h0]
      exact leadingCoeff_ne_zero.2 hs
    · exact Or.inl (leadingCoeff_ne_zero.2 hr)

/-- **Gauss's lemma at infinity for two linear forms**: the largest degree among the coefficients of
`(s₁Z − r₁)(s₂Z − r₂)` is the sum of the largest degrees among the coefficients of the factors. -/
lemma max_natDegree_prod {r₁ s₁ r₂ s₂ : k[X]} (h₁ : r₁ ≠ 0 ∨ s₁ ≠ 0) (h₂ : r₂ ≠ 0 ∨ s₂ ≠ 0) :
    max (s₁ * s₂).natDegree (max (s₁ * r₂ + r₁ * s₂).natDegree (r₁ * r₂).natDegree) =
      max r₁.natDegree s₁.natDegree + max r₂.natDegree s₂.natDegree := by
  set d₁ := max r₁.natDegree s₁.natDegree
  set d₂ := max r₂.natDegree s₂.natDegree
  have hr₁ : r₁.natDegree ≤ d₁ := le_max_left _ _
  have hs₁ : s₁.natDegree ≤ d₁ := le_max_right _ _
  have hr₂ : r₂.natDegree ≤ d₂ := le_max_left _ _
  have hs₂ : s₂.natDegree ≤ d₂ := le_max_right _ _
  apply le_antisymm
  · refine max_le (natDegree_mul_le.trans (add_le_add hs₁ hs₂)) (max_le ?_ (natDegree_mul_le.trans
      (add_le_add hr₁ hr₂)))
    exact (natDegree_add_le _ _).trans (max_le (natDegree_mul_le.trans (add_le_add hs₁ hr₂))
      (natDegree_mul_le.trans (add_le_add hr₁ hs₂)))
  · have c0 : (s₁ * s₂).coeff (d₁ + d₂) = s₁.coeff d₁ * s₂.coeff d₂ := coeff_mul_add_eq_of_natDegree_le hs₁ hs₂
    have c1 : (s₁ * r₂ + r₁ * s₂).coeff (d₁ + d₂) = s₁.coeff d₁ * r₂.coeff d₂ + r₁.coeff d₁ * s₂.coeff d₂ := by
      rw [coeff_add, coeff_mul_add_eq_of_natDegree_le hs₁ hr₂, coeff_mul_add_eq_of_natDegree_le hr₁ hs₂]
    have c2 : (r₁ * r₂).coeff (d₁ + d₂) = r₁.coeff d₁ * r₂.coeff d₂ := coeff_mul_add_eq_of_natDegree_le hr₁ hr₂
    have key : (s₁ * s₂).coeff (d₁ + d₂) ≠ 0 ∨ (s₁ * r₂ + r₁ * s₂).coeff (d₁ + d₂) ≠ 0 ∨
        (r₁ * r₂).coeff (d₁ + d₂) ≠ 0 := by
      rw [c0, c1, c2]
      by_contra hcon
      push Not at hcon
      obtain ⟨e0, e1, e2⟩ := hcon
      rcases coeff_max_ne_zero h₁ with hρ₁ | hσ₁
      · have hρ₂ : r₂.coeff d₂ = 0 := (mul_eq_zero.1 e2).resolve_left hρ₁
        have hσ₂ : s₂.coeff d₂ ≠ 0 := (coeff_max_ne_zero h₂).resolve_left (not_not.2 hρ₂)
        rw [hρ₂, mul_zero, zero_add] at e1
        exact mul_ne_zero hρ₁ hσ₂ e1
      · have hσ₂ : s₂.coeff d₂ = 0 := (mul_eq_zero.1 e0).resolve_left hσ₁
        have hρ₂ : r₂.coeff d₂ ≠ 0 := (coeff_max_ne_zero h₂).resolve_right (not_not.2 hσ₂)
        rw [hσ₂, mul_zero, add_zero] at e1
        exact mul_ne_zero hσ₁ hρ₂ e1
    rcases key with h | h | h
    · exact (le_natDegree_of_ne_zero h).trans (le_max_left _ _)
    · exact (le_natDegree_of_ne_zero h).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (le_natDegree_of_ne_zero h).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- A prime dividing a non-unit, or `X` if the polynomial is zero. -/
lemma exists_prime_dvd {d : k[X]} (hd : ¬IsUnit d) : ∃ π : k[X], Prime π ∧ π ∣ d := by
  by_cases h0 : d = 0
  · exact ⟨X, prime_X, h0 ▸ dvd_zero _⟩
  · obtain ⟨π, hπ, hπd⟩ := WfDvdMonoid.exists_irreducible_factor hd h0
    exact ⟨π, hπ.prime, hπd⟩

/-- A triple whose common divisors by primes are excluded is primitive. -/
lemma prim3_of_prime {a b c : k[X]} (h : ∀ π : k[X], Prime π → π ∣ a → π ∣ b → π ∣ c → False) :
    Prim3 a b c := by
  intro d hda hdb hdc
  by_contra hd
  obtain ⟨π, hπ, hπd⟩ := exists_prime_dvd hd
  exact h π hπ (hπd.trans hda) (hπd.trans hdb) (hπd.trans hdc)

/-- **Gauss's lemma for primes**: the coefficients of `(s₁Z − r₁)(s₂Z − r₂)` have no common factor when those of
each factor have none. -/
lemma prim3_prod {r₁ s₁ r₂ s₂ : k[X]} (h₁ : IsCoprime r₁ s₁) (h₂ : IsCoprime r₂ s₂) :
    Prim3 (s₁ * s₂) (s₁ * r₂ + r₁ * s₂) (r₁ * r₂) := by
  refine prim3_of_prime fun π hπ h0 h1 h2 => ?_
  have hn : ∀ {r s : k[X]}, IsCoprime r s → π ∣ r → π ∣ s → False := fun hrs hr hs =>
    hπ.not_isUnit (hrs.isUnit_of_dvd' hr hs)
  rcases hπ.dvd_or_dvd h0 with hs₁ | hs₂
  · have hr₂ : π ∣ r₂ := (hπ.dvd_or_dvd h2).resolve_left fun hr₁ => hn h₁ hr₁ hs₁
    have h' : π ∣ r₁ * s₂ := (dvd_add_right (dvd_mul_of_dvd_left hs₁ r₂)).1 h1
    rcases hπ.dvd_or_dvd h' with hr₁ | hs₂
    · exact hn h₁ hr₁ hs₁
    · exact hn h₂ hr₂ hs₂
  · have hr₁ : π ∣ r₁ := (hπ.dvd_or_dvd h2).resolve_right fun hr₂ => hn h₂ hr₂ hs₂
    have h' : π ∣ s₁ * r₂ := (dvd_add_left (dvd_mul_of_dvd_right hs₂ r₁)).1 h1
    rcases hπ.dvd_or_dvd h' with hs₁ | hr₂
    · exact hn h₁ hr₁ hs₁
    · exact hn h₂ hr₂ hs₂

lemma natDegree_eq_of_mul_unit {p q α β : k[X]} (hα : IsUnit α) (hβ : IsUnit β) (h : p * β = q * α) :
    p.natDegree = q.natDegree := by
  obtain ⟨a, ha, rfl⟩ := Polynomial.isUnit_iff.1 hα
  obtain ⟨b, hb, rfl⟩ := Polynomial.isUnit_iff.1 hβ
  have := congrArg natDegree h
  rwa [natDegree_mul_C hb.ne_zero, natDegree_mul_C ha.ne_zero] at this

/-- **The degrees of the two roots of `W₀Z² − W₁Z + W₂`**: if `x₁ + x₂ = W₁/W₀` and `x₁x₂ = W₂/W₀`, with `W₀ ≠ 0`
and no common factor of `W₀`, `W₁`, `W₂`, then `rdeg x₁ + rdeg x₂` is the largest degree among the `Wᵢ`. -/
lemma rdeg_add_rdeg_of_vieta {x₁ x₂ : RatFunc k} {W₀ W₁ W₂ : k[X]} (hW₀ : W₀ ≠ 0) (hW : Prim3 W₀ W₁ W₂)
    (hsum : x₁ + x₂ = algebraMap k[X] (RatFunc k) W₁ / algebraMap k[X] (RatFunc k) W₀)
    (hprod : x₁ * x₂ = algebraMap k[X] (RatFunc k) W₂ / algebraMap k[X] (RatFunc k) W₀) :
    rdeg x₁ + rdeg x₂ = max W₀.natDegree (max W₁.natDegree W₂.natDegree) := by
  classical
  set r₁ := x₁.num
  set s₁ := x₁.denom
  set r₂ := x₂.num
  set s₂ := x₂.denom
  have hs₁ : s₁ ≠ 0 := RatFunc.denom_ne_zero x₁
  have hs₂ : s₂ ≠ 0 := RatFunc.denom_ne_zero x₂
  have hT₀ : s₁ * s₂ ≠ 0 := mul_ne_zero hs₁ hs₂
  have inj := IsFractionRing.injective k[X] (RatFunc k)
  have hι : ∀ {p : k[X]}, p ≠ 0 → algebraMap k[X] (RatFunc k) p ≠ 0 := fun hp h =>
    hp (inj (h.trans (map_zero _).symm))
  have e₁ : x₁ = algebraMap k[X] (RatFunc k) r₁ / algebraMap k[X] (RatFunc k) s₁ := (RatFunc.num_div_denom x₁).symm
  have e₂ : x₂ = algebraMap k[X] (RatFunc k) r₂ / algebraMap k[X] (RatFunc k) s₂ := (RatFunc.num_div_denom x₂).symm
  -- the triples are proportional
  have p1 : W₁ * (s₁ * s₂) = (s₁ * r₂ + r₁ * s₂) * W₀ := by
    apply inj
    rw [e₁, e₂] at hsum
    have h0 := hι hW₀
    have h1 := hι hs₁
    have h2 := hι hs₂
    field_simp at hsum
    simp only [map_mul, map_add]
    linear_combination -hsum
  have p2 : W₂ * (s₁ * s₂) = (r₁ * r₂) * W₀ := by
    apply inj
    rw [e₁, e₂] at hprod
    have h0 := hι hW₀
    have h1 := hι hs₁
    have h2 := hι hs₂
    field_simp at hprod
    simp only [map_mul]
    linear_combination -hprod
  -- cancel the common factor of `W₀` and `s₁s₂`
  obtain ⟨g, α, β, hg0, hα, hβ, hαβ⟩ : ∃ g α β : k[X], g ≠ 0 ∧ W₀ = g * α ∧ s₁ * s₂ = g * β ∧ IsCoprime α β := by
    obtain ⟨α, hα⟩ := EuclideanDomain.gcd_dvd_left W₀ (s₁ * s₂)
    obtain ⟨β, hβ⟩ := EuclideanDomain.gcd_dvd_right W₀ (s₁ * s₂)
    have hg0 : EuclideanDomain.gcd W₀ (s₁ * s₂) ≠ 0 := fun h => hW₀ (EuclideanDomain.gcd_eq_zero_iff.1 h).1
    refine ⟨_, α, β, hg0, hα, hβ, EuclideanDomain.gcdA W₀ (s₁ * s₂), EuclideanDomain.gcdB W₀ (s₁ * s₂), ?_⟩
    have hb := EuclideanDomain.gcd_eq_gcd_ab W₀ (s₁ * s₂)
    apply mul_left_cancel₀ hg0
    linear_combination -hb - EuclideanDomain.gcdA W₀ (s₁ * s₂) * hα - EuclideanDomain.gcdB W₀ (s₁ * s₂) * hβ
  have hcancel : ∀ {P T : k[X]}, P * (s₁ * s₂) = T * W₀ → P * β = T * α := fun {P T} h =>
    mul_left_cancel₀ hg0 (by linear_combination h - P * hβ + T * hα)
  have q0 : W₀ * β = (s₁ * s₂) * α := by linear_combination β * hα - α * hβ
  have q1 := hcancel p1
  have q2 := hcancel p2
  -- `β` divides the product triple and `α` the `W` triple, so both are units
  have hβu : IsUnit β := prim3_prod (RatFunc.isCoprime_num_denom x₁) (RatFunc.isCoprime_num_denom x₂) β
    (hαβ.symm.dvd_of_dvd_mul_right ⟨W₀, by rw [mul_comm β W₀, q0]⟩)
    (hαβ.symm.dvd_of_dvd_mul_right ⟨W₁, by rw [mul_comm β W₁, q1]⟩)
    (hαβ.symm.dvd_of_dvd_mul_right ⟨W₂, by rw [mul_comm β W₂, q2]⟩)
  have hαu : IsUnit α := hW α
    (hαβ.dvd_of_dvd_mul_right ⟨s₁ * s₂, by rw [q0, mul_comm]⟩)
    (hαβ.dvd_of_dvd_mul_right ⟨s₁ * r₂ + r₁ * s₂, by rw [q1, mul_comm]⟩)
    (hαβ.dvd_of_dvd_mul_right ⟨r₁ * r₂, by rw [q2, mul_comm]⟩)
  rw [natDegree_eq_of_mul_unit hαu hβu q0, natDegree_eq_of_mul_unit hαu hβu q1,
    natDegree_eq_of_mul_unit hαu hβu q2, max_natDegree_prod (Or.inr hs₁) (Or.inr hs₂)]
  rfl

end ManinDegree
