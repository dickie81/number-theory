import ThetaNorm

/-!
# The Heisenberg algebra of the theta functions and the injectivity identity

D1b-1 of the D1b plan: the algebra of the Heisenberg operators `U_x G(z) = G(z + x)·e^{−πH(z, x) − πH(x, x)/2}`
(`ThetaChain.opU`, for the form `H = s·Σ z·w̄`, `ThetaChain.Hf`) on the theta spaces
`Th(Λ) = {G holomorphic : α(x)·U_xG = G, x ∈ Λ}` (`ThetaChain.Th`), and the averaging operator
`Iop(Λ₁, Λ₂)G = [Λ₂ : Λ₁ ∩ Λ₂]^{−1/2}·Σ_{q ∈ Λ₂/(Λ₁ ∩ Λ₂)} α(q)·U_qG` (`ThetaChain.Iop`).

**The commutation law.** Expanding `H(x + y, x + y)` gives `U_xU_y = e^{−πi·Im H(x, y)}·U_{x+y}` (`opU_opU`), so
`U_xU_y = e^{−2πi·Im H(x, y)}·U_yU_x`. A **theta lattice** (`IsThetaLat`) is one on which `Im H` is integral and the
semicharacter obeys `α(x + y) = α(x)α(y)(−1)^{Im H(x, y)}`; then `x ↦ α(x)·U_x` is a homomorphism on it
(`al_opU_comp`), the stabiliser of a function in a theta lattice is a subgroup, so membership in `Th(Λ)` may be
checked on generators (`mem_Th_of_le_closure`), and `Im H ∈ ℤ` with `2·sd·Re H ≡ Im H (mod 2)` and `sd·H(x, x) ∈ ℤ`
is a criterion for a theta lattice (`isThetaLat_of_int`). `Λ` is **self-dual** (`IsEDual`) if `Im H(x, y) ∈ ℤ` for
all `x ∈ Λ` forces `y ∈ Λ`; `IsCommens` is commensurability.

**`Iop` maps theta spaces to theta spaces** (`Iop_mem_Th`). For `G ∈ Th(Λ₁)` and `Λ₂` a theta lattice the summand
`α(q)·U_qG` depends only on `q mod Λ₁ ∩ Λ₂` (`al_opU_add_mem`), and `α(x)·U_x`, `x ∈ Λ₂`, permutes the cosets. So the
`Quotient.out` representatives of `Iop` do not matter (`Iop_eq_finsum`). The theta-lattice property of `Λ₁` is not
used.

**The injectivity identity** (`Iop_Iop_eq_smul`, replacing a `dim Th = 1` input). For `Λ₁` a self-dual theta lattice,
`Λ₂` a theta lattice commensurable with it, and `G ∈ Th(Λ₁)`: `α(x)·U_xU_yG = e^{−2πi·Im H(x, y)}·U_yG` for `x ∈ Λ₁`
(`al_opU_opU_swap`), so `Iop(Λ₂, Λ₁)Iop(Λ₁, Λ₂)G = (idx₁idx₂)^{−1/2}·Σ_y (Σ_x e^{−2πi·Im H(x, y)})·α(y)U_yG`. The inner
sum is a character sum over `Λ₁/(Λ₁ ∩ Λ₂)` (`sum_char_out_eq_zero`), which vanishes unless `y ∈ Λ₁` (self-duality), that
is unless `y ≡ 0`. So the composite is `√(idx₁/idx₂)·G`, `idx_i = [Λ_i : Λ₁ ∩ Λ₂]`, and `Iop(Λ₁, Λ₂)` is injective on
`Th(Λ₁)`. No character theory beyond `χ(a₀)·S = S` is used.

**Transport and tensor powers.** Along an `H`-isometry `g` the theta spaces, the theta and self-dual lattices,
commensurability and `Iop` move together (`comp_mem_Th`, `isThetaLat_comap`, `isEDual_comap`, `isCommens_comap`,
`Iop_comp`; the last on `Th(Λ₁)` with `Λ₂` a theta lattice, as otherwise the `Quotient.out` choices matter), and the
fourth tensor power maps `Th(Λ)` to `Th(Λ⁴)` when `sd·H(x, x)` is integral on `Λ` (`tens4_mem_Th`); this holds on an
`ω`-stable theta lattice (`sdNorm_int_of_smul_mem`).

**Main declarations:** `IsThetaLat`, `IsEDual`, `IsCommens`, `opU_opU`, `Iop_mem_Th`, `Iop_Iop_eq_smul`,
`comp_mem_Th`, `Iop_comp`, `mem_Th_of_le_closure`, `isThetaLat_of_int`, `tens4_mem_Th`.
-/

namespace ThetaHeis

open ThetaChain ThetaNorm Complex

noncomputable section

/-! ## The form `H` -/

section Form

variable {ι : Type*} [Fintype ι] (s : ℝ)

/-- **`H` is additive in its first argument.** -/
theorem Hf_add_left (x y z : ι → ℂ) : Hf s (x + y) z = Hf s x z + Hf s y z := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

/-- **`H` is additive in its second argument.** -/
theorem Hf_add_right (x y z : ι → ℂ) : Hf s x (y + z) = Hf s x y + Hf s x z := by
  simp only [Hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

/-- **`H` is `ℂ`-linear in its first argument.** -/
theorem Hf_smul_left (c : ℂ) (x y : ι → ℂ) : Hf s (c • x) y = c * Hf s x y := by
  simp only [Hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => by ring

/-- **`H` is conjugate-linear in its second argument.** -/
theorem Hf_smul_right (c : ℂ) (x y : ι → ℂ) : Hf s x (c • y) = starRingEnd ℂ c * Hf s x y := by
  simp only [Hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => by ring

/-- **`H` is hermitian**: `H(y, x) = conj H(x, y)`. -/
theorem Hf_swap (x y : ι → ℂ) : Hf s y x = starRingEnd ℂ (Hf s x y) := by
  simp only [Hf, map_mul, Complex.conj_ofReal, map_sum, Complex.conj_conj]
  refine congrArg _ (Finset.sum_congr rfl fun p _ => mul_comm _ _)

/-- **`Im H` is alternating**: `Im H(y, x) = −Im H(x, y)`. -/
theorem Hf_swap_im (x y : ι → ℂ) : (Hf s y x).im = -(Hf s x y).im := by
  rw [Hf_swap, Complex.conj_im]

/-- **`Re H` is symmetric.** -/
theorem Hf_swap_re (x y : ι → ℂ) : (Hf s y x).re = (Hf s x y).re := by
  rw [Hf_swap, Complex.conj_re]

/-- **`H(0, y) = 0`.** -/
theorem Hf_zero_left (y : ι → ℂ) : Hf s 0 y = 0 := by simp [Hf]

/-- **`H(x, 0) = 0`.** -/
theorem Hf_zero_right (x : ι → ℂ) : Hf s x 0 = 0 := by simp [Hf]

/-- **`H(−x, y) = −H(x, y)`.** -/
theorem Hf_neg_left (x y : ι → ℂ) : Hf s (-x) y = -Hf s x y := by
  simpa using Hf_smul_left s (-1) x y

/-- **`H(x, −y) = −H(x, y)`.** -/
theorem Hf_neg_right (x y : ι → ℂ) : Hf s x (-y) = -Hf s x y := by
  simpa using Hf_smul_right s (-1) x y

/-- **The real part of `H(x + y, x + y)`**: `Re H(x, x) + Re H(y, y) + 2·Re H(x, y)`. -/
theorem Hf_add_add_re (x y : ι → ℂ) :
    (Hf s (x + y) (x + y)).re = (Hf s x x).re + (Hf s y y).re + 2 * (Hf s x y).re := by
  rw [Hf_add_left, Hf_add_right, Hf_add_right]
  simp only [Complex.add_re, Hf_swap_re s x y]
  ring

end Form

/-! ## The semicharacter and the Heisenberg operators -/

section Opers

variable {ι : Type*} [Fintype ι] {s sd : ℝ}

/-- **`α(x)² = 1`.** -/
theorem al_mul_self (x : ι → ℂ) : al s sd x * al s sd x = 1 := by
  rw [al, ← mul_zpow]
  norm_num

/-- **`α(0) = 1`.** -/
theorem al_zero : al s sd (0 : ι → ℂ) = 1 := by
  simp [al, Hf_zero_left]

/-- **`α(−x) = α(x)`.** -/
theorem al_neg (x : ι → ℂ) : al s sd (-x) = al s sd x := by
  simp only [al, Hf_neg_left, Hf_neg_right, neg_neg]

/-- **`α(x) = (−1)^m`** when `sd·Re H(x, x) = m ∈ ℤ`. -/
theorem al_eq_of_int {x : ι → ℂ} {m : ℤ} (h : sd * (Hf s x x).re = m) : al s sd x = (-1) ^ m := by
  rw [al, h, round_intCast]

/-- **`e^{−πi·n} = (−1)^n`** for `n ∈ ℤ`. -/
theorem exp_neg_pi_int (n : ℤ) : Complex.exp (-(Real.pi : ℂ) * Complex.I * (n : ℂ)) = (-1) ^ n := by
  rw [show -(Real.pi : ℂ) * Complex.I * (n : ℂ) = n * (-(Real.pi * Complex.I)) by ring, Complex.exp_int_mul,
    Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- **`e^{−2πi·n} = 1`** for `n ∈ ℤ`. -/
theorem exp_neg_two_pi_int (n : ℤ) : Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) = 1 :=
  Complex.exp_eq_one_iff.mpr ⟨-n, by push_cast; ring⟩

/-- **`U_x G` explicitly.** -/
theorem opU_apply (x : ι → ℂ) (G : (ι → ℂ) → ℂ) (z : ι → ℂ) :
    opU s x G z = G (z + x) * Complex.exp (-Real.pi * Hf s z x - Real.pi * Hf s x x / 2) := rfl

/-- **`U_x` is linear: scalars.** -/
theorem opU_smul (x : ι → ℂ) (c : ℂ) (G : (ι → ℂ) → ℂ) : opU s x (c • G) = c • opU s x G := by
  funext z
  simp only [opU, Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- **`U_x` is linear: finite sums.** -/
theorem opU_sum {α : Type*} (S : Finset α) (x : ι → ℂ) (F : α → (ι → ℂ) → ℂ) :
    opU s x (∑ a ∈ S, F a) = ∑ a ∈ S, opU s x (F a) := by
  funext z
  simp only [opU, Finset.sum_apply, Finset.sum_mul]

/-- **`U_x` keeps holomorphy.** -/
theorem differentiable_opU (x : ι → ℂ) {G : (ι → ℂ) → ℂ} (hG : Differentiable ℂ G) :
    Differentiable ℂ (opU s x G) := by
  have hH : Differentiable ℂ fun z : ι → ℂ => Hf s z x := by
    unfold Hf
    fun_prop
  exact (hG.comp (differentiable_id.add_const x)).mul
    ((((hH.const_mul _).sub_const _)).cexp)

/-- **The commutation law** `U_xU_y = e^{−πi·Im H(x, y)}·U_{x+y}` (expand `H(x + y, x + y)`, and
`H(x, y) − H(y, x) = 2i·Im H(x, y)`). -/
theorem opU_opU (s : ℝ) (x y : ι → ℂ) (G : (ι → ℂ) → ℂ) :
    opU s x (opU s y G) = Complex.exp (-(Real.pi : ℂ) * Complex.I * (Hf s x y).im) • opU s (x + y) G := by
  funext z
  simp only [opU, Pi.smul_apply, smul_eq_mul, add_assoc]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
  congr 2
  rw [Hf_add_left, Hf_add_right, Hf_add_left, Hf_add_right, Hf_add_right, Hf_swap s x y]
  have h := Complex.sub_conj (Hf s x y)
  push_cast at h
  linear_combination (-(Real.pi : ℂ) / 2) * h

end Opers

/-! ## Sums over a finite quotient -/

section Quot

variable {A M : Type*} [AddCommGroup A] (K : AddSubgroup A)

/-- **A coset-invariant function at a representative**: `f((a mod K).out) = f(a)`. -/
theorem apply_out_mk {f : A → M} (hf : ∀ a, ∀ k ∈ K, f (a + k) = f a) (a : A) :
    f (Quotient.out (a : A ⧸ K)) = f a := by
  obtain ⟨k, hk⟩ := QuotientAddGroup.mk_out_eq_add K a
  rw [hk, hf a k k.2]

/-- **Translation permutes the cosets**: `Σ_q f(a + q.out) = Σ_q f(q.out)` for coset-invariant `f`. -/
theorem sum_out_add [AddCommMonoid M] [Fintype (A ⧸ K)] {f : A → M} (hf : ∀ a, ∀ k ∈ K, f (a + k) = f a) (a : A) :
    ∑ q : A ⧸ K, f (a + Quotient.out q) = ∑ q : A ⧸ K, f (Quotient.out q) :=
  Fintype.sum_equiv (Equiv.addLeft (a : A ⧸ K)) _ _ fun q => by
    have e : Equiv.addLeft (a : A ⧸ K) q = ((a + Quotient.out q : A) : A ⧸ K) := by
      rw [Equiv.coe_addLeft, QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
    rw [e, apply_out_mk K hf]

/-- **A nontrivial character sums to zero** over `A/K`: if `χ` is multiplicative, trivial on `K` and `χ(a₀) ≠ 1`,
then `Σ_q χ(q.out) = 0` (`χ(a₀)·S = S`). -/
theorem sum_char_out_eq_zero [Fintype (A ⧸ K)] {χ : A → ℂ} (hχ : ∀ a b, χ (a + b) = χ a * χ b)
    (hK : ∀ k ∈ K, χ k = 1) {a₀ : A} (ha₀ : χ a₀ ≠ 1) : ∑ q : A ⧸ K, χ (Quotient.out q) = 0 := by
  have hf : ∀ a, ∀ k ∈ K, χ (a + k) = χ a := fun a k hk => by rw [hχ, hK k hk, mul_one]
  have h := sum_out_add K hf a₀
  simp only [hχ, ← Finset.mul_sum] at h
  have h2 : (χ a₀ - 1) * ∑ q : A ⧸ K, χ (Quotient.out q) = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr ha₀)

/-- **The quotient of `Iop` is finite** for a finite index. -/
theorem finite_quot {Λ₁ Λ₂ : AddSubgroup A} (h : (Λ₁ ⊓ Λ₂).relIndex Λ₂ ≠ 0) :
    Finite (Λ₂ ⧸ (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂) := by
  have : ((Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂).FiniteIndex := ⟨h⟩
  infer_instance

end Quot

/-! ## Theta lattices and `Iop` -/

section Lattices

variable {ι : Type*} [Fintype ι] {s sd : ℝ}

/-- **`Λ` is a theta lattice**: `Im H` is integral on `Λ` and `α(x + y) = α(x)α(y)(−1)^{Im H(x, y)}`, so that
`x ↦ α(x)·U_x` is a homomorphism on `Λ` (`al_opU_comp`). -/
def IsThetaLat (s sd : ℝ) (Λ : AddSubgroup (ι → ℂ)) : Prop :=
  ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ n : ℤ, (Hf s x y).im = n ∧ al s sd (x + y) = al s sd x * al s sd y * (-1) ^ n

/-- **`Λ` is self-dual for `E = Im H`**: `Im H(x, y) ∈ ℤ` for all `x ∈ Λ` forces `y ∈ Λ`. -/
def IsEDual (s : ℝ) (Λ : AddSubgroup (ι → ℂ)) : Prop :=
  ∀ y : ι → ℂ, (∀ x ∈ Λ, ∃ n : ℤ, (Hf s x y).im = n) → y ∈ Λ

/-- **Commensurable lattices**: `Λ₁ ∩ Λ₂` has finite index in both. -/
def IsCommens (Λ₁ Λ₂ : AddSubgroup (ι → ℂ)) : Prop :=
  (Λ₁ ⊓ Λ₂).relIndex Λ₁ ≠ 0 ∧ (Λ₁ ⊓ Λ₂).relIndex Λ₂ ≠ 0

/-- **`x ↦ α(x)·U_x` is multiplicative** on a pair with `Im H(x, y) = n ∈ ℤ` and `α(x + y) = α(x)α(y)(−1)^n`
(`opU_opU` and `e^{−πin} = (−1)^n`). -/
theorem al_opU_comp {x y : ι → ℂ} {n : ℤ} (hn : (Hf s x y).im = n)
    (hal : al s sd (x + y) = al s sd x * al s sd y * (-1) ^ n) (G : (ι → ℂ) → ℂ) :
    al s sd x • opU s x (al s sd y • opU s y G) = al s sd (x + y) • opU s (x + y) G := by
  rw [opU_smul, opU_opU, hn, Complex.ofReal_intCast, exp_neg_pi_int, hal, smul_smul, smul_smul, mul_assoc]

/-- **On `Th(Λ)`, `U_x` is the scalar `α(x)`** for `x ∈ Λ`. -/
theorem opU_eq_of_mem_Th {Λ : AddSubgroup (ι → ℂ)} {G : (ι → ℂ) → ℂ} (hG : G ∈ Th s sd Λ) {x : ι → ℂ}
    (hx : x ∈ Λ) : opU s x G = al s sd x • G := by
  have h := congrArg (al s sd x • ·) (hG.2 x hx)
  simpa only [smul_smul, al_mul_self, one_smul] using h

/-- **The summand of `Iop` depends only on the coset**: for `G ∈ Th(Λ₁)`, `Λ₂` a theta lattice, `q ∈ Λ₂` and
`r ∈ Λ₁ ∩ Λ₂`, `α(q + r)·U_{q+r}G = α(q)·U_qG`. -/
theorem al_opU_add_mem {Λ₁ Λ₂ : AddSubgroup (ι → ℂ)} (h₂ : IsThetaLat s sd Λ₂) {G : (ι → ℂ) → ℂ}
    (hG : G ∈ Th s sd Λ₁) {q r : ι → ℂ} (hq : q ∈ Λ₂) (hr₁ : r ∈ Λ₁) (hr₂ : r ∈ Λ₂) :
    al s sd (q + r) • opU s (q + r) G = al s sd q • opU s q G := by
  obtain ⟨n, hn, hal⟩ := h₂ q hq r hr₂
  rw [← al_opU_comp hn hal G, hG.2 r hr₁]

/-- **Membership in a theta space is checked on generators**: in a theta lattice the stabiliser
`{x : α(x)·U_xG = G}` is a subgroup. -/
theorem mem_Th_of_le_closure {Λ : AddSubgroup (ι → ℂ)} (hΛ : IsThetaLat s sd Λ) {T : Set (ι → ℂ)} (hT : T ⊆ Λ)
    (hle : Λ ≤ AddSubgroup.closure T) {G : (ι → ℂ) → ℂ} (hd : Differentiable ℂ G)
    (hgen : ∀ x ∈ T, al s sd x • opU s x G = G) : G ∈ Th s sd Λ := by
  refine ⟨hd, fun x hx => ?_⟩
  refine (AddSubgroup.closure_induction (p := fun x _ => x ∈ Λ ∧ al s sd x • opU s x G = G)
    (fun x hx => ⟨hT hx, hgen x hx⟩) ⟨zero_mem _, by rw [al_zero, opU_zero, one_smul]⟩
    (fun x y _ _ hx hy => ⟨add_mem hx.1 hy.1, ?_⟩) (fun x _ hx => ⟨neg_mem hx.1, ?_⟩) (hle hx)).2
  · obtain ⟨n, hn, hal⟩ := hΛ x hx.1 y hy.1
    rw [← al_opU_comp hn hal, hy.2, hx.2]
  · obtain ⟨n, hn, hal⟩ := hΛ (-x) (neg_mem hx.1) x hx.1
    have h := al_opU_comp hn hal G
    rwa [hx.2, neg_add_cancel, al_zero, opU_zero, one_smul] at h

/-- **A criterion for a theta lattice**: `sd·H(x, x) ∈ ℤ`, `Im H(x, y) ∈ ℤ` and `2·sd·Re H(x, y) ≡ Im H(x, y)
(mod 2)` on `Λ` (then `sd·H(x + y, x + y) = sd·H(x, x) + sd·H(y, y) + 2·sd·Re H(x, y)`). -/
theorem isThetaLat_of_int {Λ : AddSubgroup (ι → ℂ)} (h1 : ∀ x ∈ Λ, ∃ m : ℤ, sd * (Hf s x x).re = m)
    (h2 : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ n k : ℤ, (Hf s x y).im = n ∧ sd * (2 * (Hf s x y).re) = n + 2 * k) :
    IsThetaLat s sd Λ := by
  intro x hx y hy
  obtain ⟨n, k, hn, hk⟩ := h2 x hx y hy
  obtain ⟨mx, hmx⟩ := h1 x hx
  obtain ⟨my, hmy⟩ := h1 y hy
  refine ⟨n, hn, ?_⟩
  have hxy : sd * (Hf s (x + y) (x + y)).re = ((mx + my + n + 2 * k : ℤ) : ℝ) := by
    rw [Hf_add_add_re]
    push_cast
    linear_combination hmx + hmy + hk
  rw [al_eq_of_int hxy, al_eq_of_int hmx, al_eq_of_int hmy, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num),
    zpow_add₀ (by norm_num), zpow_mul]
  norm_num

/-- **The summand of `Iop` on `Λ₂`** is invariant under `Λ₁ ∩ Λ₂` (`al_opU_add_mem`). -/
theorem summand_add_mem {Λ₁ Λ₂ : AddSubgroup (ι → ℂ)} (h₂ : IsThetaLat s sd Λ₂) {G : (ι → ℂ) → ℂ}
    (hG : G ∈ Th s sd Λ₁) (q : Λ₂) (k : Λ₂) (hk : k ∈ (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂) :
    al s sd ((q + k : Λ₂) : ι → ℂ) • opU s ((q + k : Λ₂) : ι → ℂ) G = al s sd (q : ι → ℂ) • opU s q G := by
  rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_inf] at hk
  rw [AddSubgroup.coe_add]
  exact al_opU_add_mem h₂ hG q.2 hk.1 k.2

/-- **`Iop` is linear: scalars.** -/
theorem Iop_smul (Λ₁ Λ₂ : AddSubgroup (ι → ℂ)) (c : ℂ) (G : (ι → ℂ) → ℂ) :
    Iop s sd Λ₁ Λ₂ (c • G) = c • Iop s sd Λ₁ Λ₂ G := by
  simp only [Iop, opU_smul, smul_comm _ c, ← smul_finsum]

/-- **`Iop` maps `Th(Λ₁)` to `Th(Λ₂)`** for commensurable theta lattices: `α(x)·U_x`, `x ∈ Λ₂`, permutes the
summands (`al_opU_comp`, `summand_add_mem`). The theta-lattice property of `Λ₁` is not needed. -/
theorem Iop_mem_Th {Λ₁ Λ₂ : AddSubgroup (ι → ℂ)} (_h₁ : IsThetaLat s sd Λ₁) (h₂ : IsThetaLat s sd Λ₂)
    (hc : IsCommens Λ₁ Λ₂) {G : (ι → ℂ) → ℂ} (hG : G ∈ Th s sd Λ₁) : Iop s sd Λ₁ Λ₂ G ∈ Th s sd Λ₂ := by
  have := finite_quot hc.2
  let _ := Fintype.ofFinite (Λ₂ ⧸ (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂)
  rw [Iop, finsum_eq_sum_of_fintype]
  refine ⟨(Differentiable.sum fun q _ => (differentiable_opU _ hG.1).const_smul _).const_smul _,
    fun x hx => ?_⟩
  rw [opU_smul, opU_sum, smul_comm, Finset.smul_sum]
  congr 1
  rw [← sum_out_add (f := fun q : Λ₂ => al s sd (q : ι → ℂ) • opU s q G) _ (summand_add_mem h₂ hG) ⟨x, hx⟩]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨n, hn, hal⟩ := h₂ x hx _ (Quotient.out q).2
  rw [al_opU_comp hn hal, AddSubgroup.coe_add]

end Lattices

/-! ## The injectivity identity -/

section Inj

variable {ι : Type*} [Fintype ι] {s sd : ℝ}

/-- **The swap on `Th(Λ₁)`**: `α(p)·U_pU_qG = e^{−2πi·Im H(p, q)}·U_qG` for `p ∈ Λ₁` (`U_pU_q` and `U_qU_p` differ by
`e^{−2πi·Im H(p, q)}`, and `α(p)·U_pG = G`). -/
theorem al_opU_opU_swap {Λ₁ : AddSubgroup (ι → ℂ)} {G : (ι → ℂ) → ℂ} (hG : G ∈ Th s sd Λ₁) {p : ι → ℂ}
    (hp : p ∈ Λ₁) (q : ι → ℂ) :
    al s sd p • opU s p (opU s q G) =
      Complex.exp (-2 * Real.pi * Complex.I * (Hf s p q).im) • opU s q G := by
  have h1 := opU_opU s p q G
  have h2 := opU_opU s q p G
  rw [opU_eq_of_mem_Th hG hp, opU_smul, add_comm q p, Hf_swap_im] at h2
  funext z
  have e1 := congrFun h1 z
  have e2 := congrFun h2 z
  simp only [Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
  set E := Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf s p q).im : ℂ))
  have hEE : E * Complex.exp (-(Real.pi : ℂ) * Complex.I * ((-(Hf s p q).im : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    push_cast
    ring
  have hE2 : Complex.exp (-2 * Real.pi * Complex.I * (Hf s p q).im) = E * E := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hA := al_mul_self (s := s) (sd := sd) p
  linear_combination al s sd p * e1 - al s sd p * E * E * e2 - al s sd p * E * opU s (p + q) G z * hEE +
    E ^ 2 * opU s q G z * hA - opU s q G z * hE2

/-- **`√a⁻¹·√b⁻¹·a = √(a/b)`** for `a > 0`, in `ℂ`. -/
theorem sqrt_inv_mul_aux {a b : ℝ} (ha : 0 < a) :
    ((Real.sqrt a : ℂ))⁻¹ * (((Real.sqrt b : ℂ))⁻¹ * (a : ℂ)) = ((Real.sqrt (a / b) : ℝ) : ℂ) := by
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hsa : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
  have hr : (Real.sqrt a)⁻¹ * ((Real.sqrt b)⁻¹ * a) = Real.sqrt (a / b) := by
    rw [Real.sqrt_div ha.le, div_eq_mul_inv]
    calc (Real.sqrt a)⁻¹ * ((Real.sqrt b)⁻¹ * a)
        = (Real.sqrt a)⁻¹ * (Real.sqrt a * Real.sqrt a) * (Real.sqrt b)⁻¹ := by rw [hsa]; ring
      _ = Real.sqrt a * (Real.sqrt b)⁻¹ := by rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  exact_mod_cast hr

/-- **The injectivity identity**: for `Λ₁` a self-dual theta lattice, `Λ₂` a theta lattice commensurable with it, and
`G ∈ Th(Λ₁)`, going to `Λ₂` and back is the positive scalar `√([Λ₁ : Λ₁ ∩ Λ₂]/[Λ₂ : Λ₁ ∩ Λ₂])` (the character sum
`Σ_{x ∈ Λ₁/(Λ₁ ∩ Λ₂)} e^{−2πi·Im H(x, y)}` vanishes unless `y ∈ Λ₁`, `sum_char_out_eq_zero`). -/
theorem Iop_Iop_eq_smul {Λ₁ Λ₂ : AddSubgroup (ι → ℂ)} (h₁ : IsThetaLat s sd Λ₁) (hsd : IsEDual s Λ₁)
    (h₂ : IsThetaLat s sd Λ₂) (hc : IsCommens Λ₁ Λ₂) {G : (ι → ℂ) → ℂ} (hG : G ∈ Th s sd Λ₁) :
    Iop s sd Λ₂ Λ₁ (Iop s sd Λ₁ Λ₂ G) =
      ((Real.sqrt ((Λ₁ ⊓ Λ₂).relIndex Λ₁ / (Λ₁ ⊓ Λ₂).relIndex Λ₂ : ℝ) : ℝ) : ℂ) • G := by
  classical
  have hc1 : (Λ₂ ⊓ Λ₁).relIndex Λ₁ ≠ 0 := by rw [inf_comm]; exact hc.1
  have := finite_quot hc.2
  have := finite_quot hc1
  let _ := Fintype.ofFinite (Λ₂ ⧸ (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂)
  let _ := Fintype.ofFinite (Λ₁ ⧸ (Λ₂ ⊓ Λ₁).addSubgroupOf Λ₁)
  set χ : (Λ₂ ⧸ (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂) → Λ₁ → ℂ := fun q p =>
    Complex.exp (-2 * Real.pi * Complex.I * (Hf s (p : ι → ℂ) ((Quotient.out q : Λ₂) : ι → ℂ)).im) with hχ
  -- the character sums
  have hchar : ∀ q, ∑ p : Λ₁ ⧸ (Λ₂ ⊓ Λ₁).addSubgroupOf Λ₁, χ q (Quotient.out p) =
      if q = 0 then ((Λ₂ ⊓ Λ₁).relIndex Λ₁ : ℂ) else 0 := by
    intro q
    split_ifs with hq
    · have h0 : ((Quotient.out q : Λ₂) : ι → ℂ) ∈ Λ₁ := by
        have := (QuotientAddGroup.eq_zero_iff (Quotient.out q)).mp (by rw [QuotientAddGroup.out_eq', hq])
        exact (AddSubgroup.mem_inf.mp (AddSubgroup.mem_addSubgroupOf.mp this)).1
      have h1 : ∀ p : Λ₁, χ q p = 1 := fun p => by
        obtain ⟨n, hn, -⟩ := h₁ _ p.2 _ h0
        simp only [hχ, hn, Complex.ofReal_intCast, exp_neg_two_pi_int]
      simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rw [← Nat.card_eq_fintype_card]
      rfl
    · have hn0 : ((Quotient.out q : Λ₂) : ι → ℂ) ∉ Λ₁ := fun h => hq (by
        rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
        exact AddSubgroup.mem_inf.mpr ⟨h, (Quotient.out q).2⟩)
      have hx : ¬ ∀ x ∈ Λ₁, ∃ n : ℤ, (Hf s x ((Quotient.out q : Λ₂) : ι → ℂ)).im = n := fun h => hn0 (hsd _ h)
      push Not at hx
      obtain ⟨x, hx, hxn⟩ := hx
      refine sum_char_out_eq_zero _ (fun a b => ?_) (fun k hk => ?_) (a₀ := ⟨x, hx⟩) (fun h1 => ?_)
      · simp only [hχ, AddSubgroup.coe_add, Hf_add_left, Complex.add_im, Complex.ofReal_add, mul_add,
          Complex.exp_add]
      · rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_inf] at hk
        obtain ⟨n, hn, -⟩ := h₂ _ hk.1 _ (Quotient.out q).2
        simp only [hχ, hn, Complex.ofReal_intCast, exp_neg_two_pi_int]
      · obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
        refine hxn (-n) ?_
        have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
        have h3 : (((Hf s x ((Quotient.out q : Λ₂) : ι → ℂ)).im : ℝ) : ℂ) = ((-n : ℤ) : ℂ) := by
          apply mul_left_cancel₀ h2
          push_cast
          linear_combination -hn
        exact_mod_cast h3
  have key : ∀ (p : Λ₁ ⧸ (Λ₂ ⊓ Λ₁).addSubgroupOf Λ₁) (q : Λ₂ ⧸ (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂) (z : ι → ℂ),
      al s sd ((Quotient.out p : Λ₁) : ι → ℂ) *
        opU s ((Quotient.out p : Λ₁) : ι → ℂ) (opU s ((Quotient.out q : Λ₂) : ι → ℂ) G) z =
        χ q (Quotient.out p) * opU s ((Quotient.out q : Λ₂) : ι → ℂ) G z := fun p q z => by
    have := congrFun (al_opU_opU_swap hG (Quotient.out p).2 ((Quotient.out q : Λ₂) : ι → ℂ)) z
    simpa only [Pi.smul_apply, smul_eq_mul] using this
  funext z
  rw [Iop, Iop, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, opU_smul, opU_sum]
  have hstep : ∀ (c : ℂ) (p : Λ₁ ⧸ (Λ₂ ⊓ Λ₁).addSubgroupOf Λ₁),
      al s sd ((Quotient.out p : Λ₁) : ι → ℂ) * (c * ∑ q : Λ₂ ⧸ (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂,
        al s sd ((Quotient.out q : Λ₂) : ι → ℂ) *
          opU s ((Quotient.out p : Λ₁) : ι → ℂ) (opU s ((Quotient.out q : Λ₂) : ι → ℂ) G) z) =
        c * ∑ q : Λ₂ ⧸ (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂, χ q (Quotient.out p) *
          (al s sd ((Quotient.out q : Λ₂) : ι → ℂ) * opU s ((Quotient.out q : Λ₂) : ι → ℂ) G z) := by
    intro c p
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    linear_combination (c * al s sd ((Quotient.out q : Λ₂) : ι → ℂ)) * key p q z
  rw [Finset.sum_congr rfl fun p _ => hstep _ p, ← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.sum_mul, hchar]
  rw [Finset.sum_eq_single (0 : Λ₂ ⧸ (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂)
    (fun q _ hq => by rw [ite_eq_right hq, zero_mul]) (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl]
  have h0 : ((Quotient.out (0 : Λ₂ ⧸ (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂) : Λ₂) : ι → ℂ) ∈ Λ₁ := by
    have := (QuotientAddGroup.eq_zero_iff (Quotient.out (0 : Λ₂ ⧸ (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂))).mp
      (QuotientAddGroup.out_eq' _)
    exact (AddSubgroup.mem_inf.mp (AddSubgroup.mem_addSubgroupOf.mp this)).1
  have hG0 := congrFun (hG.2 _ h0) z
  simp only [Pi.smul_apply, smul_eq_mul] at hG0
  rw [hG0, inf_comm Λ₂ Λ₁]
  have hpos : (0 : ℝ) < ((Λ₁ ⊓ Λ₂).relIndex Λ₁ : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hc.1
  have := sqrt_inv_mul_aux (b := ((Λ₁ ⊓ Λ₂).relIndex Λ₂ : ℝ)) hpos
  push_cast at this ⊢
  linear_combination G z * this

end Inj

/-! ## Transport along `H`-isometries -/

section Transport

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {s sd : ℝ}

/-- **`U` commutes with an additive `H`-isometry**: `U_x(G ∘ g) = (U_{g x}G) ∘ g`. -/
theorem opU_comp {g : (κ → ℂ) → (ι → ℂ)} (hadd : ∀ a b, g (a + b) = g a + g b)
    (hg : ∀ z w, Hf s (g z) (g w) = Hf s z w) (x : κ → ℂ) (G : (ι → ℂ) → ℂ) :
    opU s x (G ∘ g) = opU s (g x) G ∘ g := by
  funext z
  simp only [opU, Function.comp, hadd, hg]

omit [Fintype ι] in
/-- **A linear map of `ℂ^κ` is holomorphic.** -/
theorem differentiable_linearMap (g : (κ → ℂ) →ₗ[ℂ] (ι → ℂ)) : Differentiable ℂ g := by
  rw [← LinearMap.coe_toContinuousLinearMap' g]
  exact (LinearMap.toContinuousLinearMap g).differentiable

/-- **Transport of theta spaces** along an `H`-isometry `g`: `G ∈ Th(Λ)` gives `G ∘ g ∈ Th(g⁻¹Λ)`. -/
theorem comp_mem_Th (g : (κ → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (hg : ∀ z w, Hf s (g z) (g w) = Hf s z w)
    {Λ : AddSubgroup (ι → ℂ)} {G : (ι → ℂ) → ℂ} (hG : G ∈ Th s sd Λ) :
    G ∘ g ∈ Th s sd (Λ.comap g.toLinearMap.toAddMonoidHom) := by
  refine ⟨hG.1.comp (differentiable_linearMap g.toLinearMap), fun x hx => ?_⟩
  have hx' : g x ∈ Λ := hx
  rw [opU_comp (map_add g) hg, al, ← hg x x]
  funext z
  exact congrFun (hG.2 _ hx') (g z)

/-- **Transport of theta lattices** along an `H`-isometry. -/
theorem isThetaLat_comap (g : (κ → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (hg : ∀ z w, Hf s (g z) (g w) = Hf s z w)
    {Λ : AddSubgroup (ι → ℂ)} (hΛ : IsThetaLat s sd Λ) : IsThetaLat s sd (Λ.comap g.toLinearMap.toAddMonoidHom) := by
  intro x hx y hy
  obtain ⟨n, hn, hal⟩ := hΛ (g x) hx (g y) hy
  refine ⟨n, by rw [← hg]; exact hn, ?_⟩
  simpa only [al, ← map_add, hg] using hal

/-- **Transport of self-duality** along an `H`-isometry. -/
theorem isEDual_comap (g : (κ → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (hg : ∀ z w, Hf s (g z) (g w) = Hf s z w)
    {Λ : AddSubgroup (ι → ℂ)} (hΛ : IsEDual s Λ) : IsEDual s (Λ.comap g.toLinearMap.toAddMonoidHom) := by
  intro y hy
  refine hΛ (g y) fun x hx => ?_
  obtain ⟨n, hn⟩ := hy (g.symm x) (by simpa using hx)
  exact ⟨n, by rw [← hn, ← hg, LinearEquiv.apply_symm_apply]⟩

/-- **Indices under an additive bijection**: `[K : g⁻¹C ∩ L] = [gK : C ∩ gL]`. -/
theorem relIndex_comap_inf {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (f : X →+ Y)
    (hi : Function.Injective f) (hs : Function.Surjective f) (C : AddSubgroup Y) (L K : AddSubgroup X) :
    (C.comap f ⊓ L).relIndex K = (C ⊓ L.map f).relIndex (K.map f) := by
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hi, AddSubgroup.map_inf _ _ _ hi,
    AddSubgroup.map_comap_eq_self_of_surjective hs]

omit [Fintype ι] in
/-- **Transport of commensurability** along a linear bijection: `C` and `gL` commensurable gives `g⁻¹C` and `L`
commensurable. -/
theorem isCommens_comap (g : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) {C L : AddSubgroup (ι → ℂ)}
    (hc : IsCommens C (L.map g.toLinearMap.toAddMonoidHom)) :
    IsCommens (C.comap g.toLinearMap.toAddMonoidHom) L := by
  have hi : Function.Injective g.toLinearMap.toAddMonoidHom := g.injective
  have hs : Function.Surjective g.toLinearMap.toAddMonoidHom := g.surjective
  refine ⟨?_, ?_⟩
  · rw [relIndex_comap_inf _ hi hs, AddSubgroup.map_comap_eq_self_of_surjective hs]
    exact hc.1
  · rw [relIndex_comap_inf _ hi hs]
    exact hc.2

end Transport

/-! ## The fourth tensor power -/

section Tens

variable {Φ : Type*} [Fintype Φ] {s sd : ℝ}

/-- **`H` on `ℂ^{Fin 4 × Φ}` is the sum of `H` on the slices.** -/
theorem Hf_slice (v w : Fin 4 × Φ → ℂ) : Hf s v w = ∑ k : Fin 4, Hf s (slice k v) (slice k w) := by
  simp only [Hf, ← Finset.mul_sum, Fintype.sum_prod_type]
  rfl

/-- **`sd·H(x, x)` is integral on an `ω`-stable theta lattice** (`Im ω = sd`): `sd·H(x, x) = Im H(ωx, x)`. -/
theorem sdNorm_int_of_smul_mem {ι : Type*} [Fintype ι] {Λ : AddSubgroup (ι → ℂ)} (hΛ : IsThetaLat s sd Λ)
    {w : ℂ} (hw : w.im = sd) (hωΛ : ∀ x ∈ Λ, w • x ∈ Λ) : ∀ x ∈ Λ, ∃ m : ℤ, sd * (Hf s x x).re = m := by
  intro x hx
  obtain ⟨n, hn, -⟩ := hΛ _ (hωΛ x hx) x hx
  have h0 : (Hf s x x).im = 0 := by linarith [Hf_swap_im s x x]
  refine ⟨n, ?_⟩
  rw [← hn, Hf_smul_left, Complex.mul_im, h0, hw]
  ring

/-- **The fourth tensor power maps `Th(Λ)` to `Th(Λ⁴)`** when `sd·H(x, x)` is integral on `Λ` (so that
`α(v) = Π_k α(v_k)`; `sdNorm_int_of_smul_mem`): `U_v θ^{⊗4} = ⊗_k U_{v_k}θ`. -/
theorem tens4_mem_Th {Λ : AddSubgroup (Φ → ℂ)} (hint : ∀ x ∈ Λ, ∃ m : ℤ, sd * (Hf s x x).re = m)
    {θ : (Φ → ℂ) → ℂ} (hθ : θ ∈ Th s sd Λ) : tens4 θ ∈ Th s sd (pow4 Λ) := by
  have hsl : ∀ k : Fin 4, Differentiable ℂ (slice (Φ := Φ) k) := fun k =>
    differentiable_linearMap (LinearMap.funLeft ℂ ℂ (fun p : Φ => (k, p)))
  refine ⟨?_, fun v hv => ?_⟩
  · have h1 : Differentiable ℂ θ := hθ.1
    unfold tens4
    fun_prop
  have hvk : ∀ k, slice k v ∈ Λ := fun k => AddSubgroup.mem_comap.mp (AddSubgroup.mem_iInf.mp hv k)
  choose m hm using fun k => hint _ (hvk k)
  have hal : al s sd v = ∏ k : Fin 4, al s sd (slice k v) := by
    have hsum : sd * (Hf s v v).re = ((∑ k, m k : ℤ) : ℝ) := by
      rw [Hf_slice, Complex.re_sum, Finset.mul_sum]
      push_cast
      exact Finset.sum_congr rfl fun k _ => hm k
    rw [al_eq_of_int hsum, Finset.prod_congr rfl fun k _ => al_eq_of_int (hm k), Fin.sum_univ_four,
      Fin.prod_univ_four, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num), zpow_add₀ (by norm_num)]
  funext z
  have hk : ∀ k : Fin 4, al s sd (slice k v) * opU s (slice k v) θ (slice k z) = θ (slice k z) :=
    fun k => congrFun (hθ.2 _ (hvk k)) (slice k z)
  simp only [Pi.smul_apply, smul_eq_mul, opU, tens4, map_add] at hk ⊢
  have hexp : -(Real.pi : ℂ) * Hf s z v - Real.pi * Hf s v v / 2 =
      ∑ k : Fin 4, (-(Real.pi : ℂ) * Hf s (slice k z) (slice k v) - Real.pi * Hf s (slice k v) (slice k v) / 2) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div, ← Finset.mul_sum, ← Hf_slice, ← Hf_slice]
  rw [hal, hexp, Complex.exp_sum, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← hk k]

end Tens

/-! ## Representatives and `Iop` along isometries -/

section Reps

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {s sd : ℝ}

/-- **The representatives of `Iop` do not matter**: for `G ∈ Th(Λ₁)`, `Λ₂` a theta lattice and any choice `σ(q) ∈ Λ₂`
of representatives, `Iop(Λ₁, Λ₂)G = [Λ₂ : Λ₁ ∩ Λ₂]^{−1/2}·Σ_q α(σ q)·U_{σ q}G` (`summand_add_mem`). -/
theorem Iop_eq_finsum {Λ₁ Λ₂ : AddSubgroup (ι → ℂ)} (h₂ : IsThetaLat s sd Λ₂) {G : (ι → ℂ) → ℂ}
    (hG : G ∈ Th s sd Λ₁) (σ : Λ₂ ⧸ (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂ → Λ₂) (hσ : ∀ q, (σ q : Λ₂ ⧸ _) = q) :
    Iop s sd Λ₁ Λ₂ G = ((Real.sqrt ((Λ₁ ⊓ Λ₂).relIndex Λ₂ : ℝ))⁻¹ : ℂ) •
      ∑ᶠ q : Λ₂ ⧸ (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂, al s sd (σ q : ι → ℂ) • opU s (σ q : ι → ℂ) G := by
  rw [Iop]
  congr 1
  refine finsum_congr fun q => ?_
  conv_lhs => rw [← hσ q]
  exact apply_out_mk (f := fun q : Λ₂ => al s sd (q : ι → ℂ) • opU s q G) _ (summand_add_mem h₂ hG) (σ q)

/-- **`Iop` commutes with an `H`-isometry** on theta functions: `Iop(g⁻¹Λ₁, g⁻¹Λ₂)(G ∘ g) = (Iop(Λ₁, Λ₂)G) ∘ g` for
`G ∈ Th(Λ₁)` and `Λ₂` a theta lattice. The representatives `g(q.out)` and `(g q).out` differ by an element of
`Λ₁ ∩ Λ₂` (`summand_add_mem`); without the two hypotheses the `Quotient.out` choices of `Iop` would matter. -/
theorem Iop_comp (g : (κ → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (hg : ∀ z w, Hf s (g z) (g w) = Hf s z w)
    (Λ₁ Λ₂ : AddSubgroup (ι → ℂ)) (G : (ι → ℂ) → ℂ) (h₂ : IsThetaLat s sd Λ₂) (hG : G ∈ Th s sd Λ₁) :
    Iop s sd (Λ₁.comap g.toLinearMap.toAddMonoidHom) (Λ₂.comap g.toLinearMap.toAddMonoidHom) (G ∘ g) =
      Iop s sd Λ₁ Λ₂ G ∘ g := by
  set f := g.toLinearMap.toAddMonoidHom with hf
  have hfs : Function.Surjective f := g.surjective
  have hidx : (Λ₁.comap f ⊓ Λ₂.comap f).relIndex (Λ₂.comap f) = (Λ₁ ⊓ Λ₂).relIndex Λ₂ := by
    rw [← AddSubgroup.comap_inf, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hfs]
  by_cases h0 : (Λ₁ ⊓ Λ₂).relIndex Λ₂ = 0
  · funext z
    simp [Iop, hidx, h0]
  set K := (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂ with hK_def
  set K' := (Λ₁.comap f ⊓ Λ₂.comap f).addSubgroupOf (Λ₂.comap f) with hK'_def
  have := finite_quot h0
  have : Finite (Λ₂.comap f ⧸ K') := finite_quot (by rw [hidx]; exact h0)
  let _ := Fintype.ofFinite (Λ₂ ⧸ K)
  let _ := Fintype.ofFinite (Λ₂.comap f ⧸ K')
  let e : Λ₂.comap f → Λ₂ := fun x => ⟨g x, x.2⟩
  have hK : ∀ k : Λ₂.comap f, k ∈ K' ↔ e k ∈ K := fun k => by
    rw [hK_def, hK'_def, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_addSubgroupOf, ← AddSubgroup.comap_inf,
      AddSubgroup.mem_comap]
    rfl
  have he_add : ∀ a b : Λ₂.comap f, e (a + b) = e a + e b := fun a b =>
    Subtype.ext (by simp [e, map_add])
  have he_neg : ∀ a : Λ₂.comap f, e (-a) = -e a := fun a => Subtype.ext (by simp [e, map_neg])
  let ψ : (Λ₂.comap f ⧸ K') → Λ₂ ⧸ K := fun q' => (e (Quotient.out q') : Λ₂ ⧸ K)
  have hψ : Function.Bijective ψ := by
    refine ⟨fun a b hab => ?_, fun q => ?_⟩
    · rw [← QuotientAddGroup.out_eq' a, ← QuotientAddGroup.out_eq' b, QuotientAddGroup.eq, hK, he_add, he_neg]
      exact QuotientAddGroup.eq.mp hab
    · have hy : g.symm (Quotient.out q : Λ₂) ∈ Λ₂.comap f := by
        change g (g.symm (Quotient.out q : Λ₂)) ∈ Λ₂
        rw [LinearEquiv.apply_symm_apply]
        exact (Quotient.out q).2
      set y : Λ₂.comap f := ⟨_, hy⟩
      refine ⟨(y : Λ₂.comap f ⧸ K'), ?_⟩
      obtain ⟨k, hk⟩ := QuotientAddGroup.mk_out_eq_add K' y
      have hek : e (y + k) = Quotient.out q + e k := by
        rw [he_add]
        congr 1
        exact Subtype.ext (by simp [e, y, LinearEquiv.apply_symm_apply])
      change ((e (Quotient.out (y : Λ₂.comap f ⧸ K')) : Λ₂) : Λ₂ ⧸ K) = q
      rw [hk, hek, QuotientAddGroup.mk_add, QuotientAddGroup.out_eq',
        (QuotientAddGroup.eq_zero_iff _).mpr ((hK k).mp k.2), add_zero]
  funext z
  rw [Iop, Iop, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, hidx]
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  congr 1
  refine Fintype.sum_bijective ψ hψ _ _ fun q' => ?_
  have h1 := congrFun (apply_out_mk (f := fun q : Λ₂ => al s sd (q : ι → ℂ) • opU s q G) _
    (summand_add_mem h₂ hG) (e (Quotient.out q'))) (g z)
  simp only [Pi.smul_apply, smul_eq_mul] at h1
  change _ = al s sd ((Quotient.out ((e (Quotient.out q') : Λ₂) : Λ₂ ⧸ K) : Λ₂) : ι → ℂ) *
    opU s ((Quotient.out ((e (Quotient.out q') : Λ₂) : Λ₂ ⧸ K) : Λ₂) : ι → ℂ) G (g z)
  rw [h1, opU_comp (map_add g) hg, al, al, ← hg]
  rfl

end Reps

end

end ThetaHeis
