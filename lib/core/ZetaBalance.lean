import Mathlib
import WindowGRH

/-!
# The balance identity

A step of the library's proof of the Riemann hypothesis for `ζ` and every Dirichlet `L`-function
(`docs/rh-rebuild.md`, "Blueprint for steps 3 and 4"): Lemma B, an exact identity between a sum over the prime powers
inert in `ℚ(√−d)` and the ramp errors (`WindowGRH.rampErr`) of a family of Dirichlet characters of level
`N = QS·q·d`.

**The setting** (`Setting`): primes `q` and `d` with `q ≡ 3 (mod 4)` and `(2/d) = (q/d) = 1`; a modulus `QS` prime to
`q` whose every prime `p` has `(p/d) = 1`; and a subgroup `K` of `(ℤ/QS)ˣ`. The archive takes `QS = 2^{e+2}` and
`K = {±1}` for `ζ`, and for a primitive `χ` mod `f` a common multiple `QS` of `2^{e+2}` and `f` with
`K = {u ≡ ±1 (mod 2^{e+2}) : χ(u) = 1}`. Lemma B needs none of that: it holds for every `QS` and `K` as above.

**The group.** `A = (ℤ/QS)ˣ/K` (`Setting.A`), `Φ = {±1} × A` (`Φ`) and `G = {±1} × Φ` (`G`), in which `Φ` is the
subgroup `{1} × Φ` of index `2`. The class of `n` prime to `N` is `[n] = ((n/d), (n/q), [n]_A)`, with `[n]_A` the
class in `A` (`Setting.clsA`). For `t ∈ A`, `n` prime to `QS·q` has the partner `ρ_t(n) = ((−n/q), [n]_A t) ∈ Φ`
(`Setting.partner`), and `ρ ∈ Φ` the image `γ_t(ρ) = c ρ (1, 1, t)⁻¹ ∉ Φ` (`γ`), with `c = (−1, −1, 1)` (`c`).

**The characters** of `G` are the triples `χ = (α, β, ξ)` (`Dual`), `α, β ∈ {0, 1}` (as `false`, `true`) and
`ξ : A → ℂˣ`, with `χ(s_d, s_q, u) = s_d^α s_q^β ξ(u)` (`eval`). The Dirichlet character `D_χ = χ_d^α χ_q^β ξ̃` mod
`N` (`Setting.D`), with `χ_p = (·/p)` (`legChar`) and `ξ̃(n) = ξ([n]_A)` mod `QS` (`Setting.lift`), has
`D_χ(n) = χ([n])` for `n` prime to `N`. Its error is `g_χ = rampErr χ*` (`Setting.g`), `χ*` the primitive character
inducing `D_χ`.

**The sums.** For `a ∈ ℝ` and weights `W : Φ → (0, ∞)`:
* `ASK(a, t, W) = Σ_{(n, QS·q) = 1} Λ(n)(1 − χ_d(n))(a/n − W(ρ_t(n)))⁺` (`Setting.ASK`), a finite sum;
* `MAIN(a, W) = a(log a − 1 − γ + Re L'/L(1, χ_d) − |Φ|⁻¹ Σ_{ρ ∈ Φ} log W(ρ))` (`Setting.MAIN`);
* the gap `Σ_{t ∈ TT} Σ_{j < m} [ASK(a_t, t, w_{u₀,j}) − MAIN(a_t, w_{u₀,j})]` (`Setting.gap`), for later use.

**Lemma B** (`Setting.balance`), for every real `a`:
`ASK(a, t, W) − MAIN(a, W) = Re |Φ|⁻¹ Σ_{ρ ∈ Φ} W(ρ) Σ_χ conj χ(γ_t(ρ)) g_χ(a/W(ρ))`.

**The proof.** `W·g_χ(a/W)` is the ramp sum `Σ_n Λ(n) χ*(n) (a/n − W)⁺` plus a main term (`Setting.mul_g`).

1. *`χ*` at prime powers* (`Setting.prim_D`): `χ*(n) = (χ_d^α)*(n) (χ_q^β)*(n) ξ̃*(n)`. The levels `d`, `q` and `QS`
   are prime to each other. At a prime `p`, a factor whose level is prime to `p` splits off the primitive character
   (`prim_mul_apply`), and the remaining factor keeps its primitive character under the change of level.
2. *The kernel* (`Setting.kernel`). So at `ρ = (s, u)` the sum `Σ_χ conj χ(γ_t(ρ)) χ*(n)` factorises as
   `(1 − χ_d(n))(1 − s χ_q(n)) Σ_ξ conj ξ(u t⁻¹) ξ̃*(n)`. For `n` a power of a prime dividing `QS·q` the first factor
   vanishes, as `(q/d) = 1` and `(p/d) = 1` for `p ∣ QS`. For `n` prime to `QS·q` the second factor is
   `2·1[s = (−n/q)]`, as `(−1/q) = −1`, and the third `|A|·1[u = [n]_A t]`, by orthogonality on `A`
   (`sum_conj_mul`). So the kernel is `|Φ|(1 − χ_d(n))·1[ρ = ρ_t(n)]`, and the ramp sums add up to `|Φ|·ASK`. The
   powers of `d` need no case of their own: there `χ_d(n) = 0`.
3. *The main terms* (`Setting.sum_main`). `Σ_{ρ ∈ Φ} conj χ(γ_t(ρ))` is `|Φ|`, `−|Φ|` or `0` as `χ = 1`,
   `χ = (1, 0, 1)` or neither (`sum_conj_eval_γ`), and `χ* = 1` only for `χ = 1` (`Setting.D_eq_one_iff`, from
   step 1 at `d`, at `q` and at the primes of `QS`). The `L'/L(1, χ*)` terms leave `−|Φ| a L'/L(1, χ_d)`
   (`Setting.LFunction_D_d`), and the `χ = 1` terms `Σ_ρ ((1 + γ)a − a log(a/W(ρ)))`: together `−|Φ|·MAIN`.

**Design.** `A` is the quotient group, and its characters are the homomorphisms `A →* ℂˣ`; their orthogonality
comes from Mathlib's duality for finite abelian groups (`sum_dual_apply`). The objects that need only a finite
abelian group (`Φ`, `G`, `Dual`, `γ`, orthogonality) are stated for any. The signs are `ℤˣ`, and the characters
of `{±1}` are indexed by `Bool`. Lemma B is stated with real parts, and `MAIN` takes `Re L'/L(1, χ_d)`: the proof
computes the right side in `ℂ` as `ASK − MAIN` with `L'/L(1, χ_d)` in place of its real part. That `L'/L(1, χ_d)`
is real, as `χ_d` is, is not needed.

**Against the blueprint and the archive.**
* `d ≡ 3 (mod 4)` is not used. It gives `(−1/d) = −1`, which makes `c` the class `[−1]` when `−1 ∈ K`, and, with
  `q ≡ 3 (mod 4)`, `(d/q) = −1`. But `γ_t` is defined from `c = (−1, −1, 1)` directly, and at `n = dⁱ` the sign factor
  `1 + s(−dⁱ/q)` is `2·1[s = (−dⁱ/q)]` whatever `(d/q)` is.
* For an odd `χ`, `−1 ∉ K`, so `[−1]_A ≠ 1` and complex conjugation, `(−1, −1, [−1]_A)`, is not `c`; the archive
  twists its Artin map so that it is. Lemma B never uses `[−1] = c`: it is an identity for the `c` above whatever `K`
  is, so it needs no twist. Taking `(−1, −1, [−1]_A)` instead of `c` would only replace the translate `t` by
  `[−1]_A t`, on both sides.
* `q ≠ d` and `d ≠ 2` follow from `(q/d) = (2/d) = 1`, `q ≠ 2` from `q ≡ 3 (mod 4)`, and `d ∤ QS` from
  `(p/d) = 1` for `p ∣ QS`.
* `a > 0` is not needed.
-/

open Complex ComplexConjugate DirichletCharacter
open scoped ArithmeticFunction.vonMangoldt

namespace ZetaBalance

/-! ## Primitive characters -/

/-- The conductor of a character of nonzero level is nonzero. -/
instance conductor_neZero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : NeZero χ.conductor :=
  ⟨χ.conductor_ne_zero⟩

/-- `ψ*(n) = ψ(n)` for a primitive `ψ`. -/
theorem prim_apply_of_isPrimitive {M : ℕ} {ψ : DirichletCharacter ℂ M} (hψ : ψ.IsPrimitive) (n : ℕ) :
    ψ.primitiveCharacter n = ψ n := by
  by_cases h : IsCoprime (n : ℤ) M
  · simpa using primitiveCharacter_apply_of_isCoprime ψ h
  · have h1 := (apply_eq_zero_iff ψ n).2 h
    have h2 := (apply_eq_zero_iff ψ.primitiveCharacter n).2 (by rwa [(isPrimitive_def ψ).1 hψ])
    simp only [Int.cast_natCast] at h1 h2
    rw [h1, h2]

/-- The primitive character of `ψ` changed to a higher level is that of `ψ`. -/
theorem prim_changeLevel {M N : ℕ} [NeZero N] (h : M ∣ N) (ψ : DirichletCharacter ℂ M) (n : ℕ) :
    (changeLevel h ψ).primitiveCharacter n = ψ.primitiveCharacter n := by
  simpa using primitiveCharacter_changeLevel_apply h ψ n

/-- The primitive character of the trivial character is `1` everywhere. -/
theorem prim_one_apply {N : ℕ} [NeZero N] (n : ℕ) : (1 : DirichletCharacter ℂ N).primitiveCharacter n = 1 := by
  rw [primitiveCharacter_one]
  have : Subsingleton (ZMod (1 : DirichletCharacter ℂ N).conductor) := ZMod.subsingleton_iff.2 conductor_one
  exact MulChar.one_apply (isUnit_of_subsingleton _)

/-- `χ* = 1` exactly when `χ = 1`. -/
theorem prim_eq_one_iff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : χ.primitiveCharacter = 1 ↔ χ = 1 := by
  rw [eq_one_iff_conductor_eq_one, (isPrimitive_def _).1 χ.primitiveCharacter_isPrimitive,
    ← eq_one_iff_conductor_eq_one]

/-- **An unramified factor**: for a prime `p ∤ M` and `ψ` mod `M`, the primitive character of `ψ·D`, at a level
`N` divisible by `M`, takes at `p` the value `ψ*(p) D*(p)`. -/
theorem prim_mul_apply {M N : ℕ} [NeZero N] (h : M ∣ N) (ψ : DirichletCharacter ℂ M)
    (D : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) :
    (changeLevel h ψ * D).primitiveCharacter p = ψ.primitiveCharacter p * D.primitiveCharacter p := by
  have hN : N ≠ 0 := NeZero.ne N
  have hN' : ordCompl[p] N ∣ N := Nat.ordCompl_dvd N p
  have : NeZero (ordCompl[p] N) := ⟨(Nat.ordCompl_pos p hN).ne'⟩
  have hpN' : IsCoprime (p : ℤ) (ordCompl[p] N : ℕ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.coprime_ordCompl hp hN)
  have hpM' : IsCoprime (p : ℤ) M := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)
  have hMN' : M ∣ ordCompl[p] N := Nat.dvd_ordCompl_of_dvd_not_dvd h hpM
  have hzero : ∀ {K : ℕ} (X : DirichletCharacter ℂ K), X p = 0 ↔ p ∣ K := fun X => by
    rw [← Int.cast_natCast, apply_eq_zero_iff, Nat.isCoprime_iff_coprime, Nat.Prime.coprime_iff_not_dvd hp,
      not_not]
  -- the case `p ∤ cond D`, for every `ψ`: then `ψ·D` comes from the part `N'` of `N` prime to `p`
  have key : ∀ (ψ : DirichletCharacter ℂ M) (D : DirichletCharacter ℂ N), ¬ p ∣ D.conductor →
      (changeLevel h ψ * D).primitiveCharacter p = ψ p * D.primitiveCharacter p := by
    intro ψ D hD
    have hf : D.conductor ∣ ordCompl[p] N := Nat.dvd_ordCompl_of_dvd_not_dvd D.conductor_dvd_level hD
    have he : changeLevel h ψ * D =
        changeLevel hN' (changeLevel hMN' ψ * changeLevel hf D.primitiveCharacter) := by
      rw [map_mul, ← changeLevel_trans, ← changeLevel_trans, changeLevel_primitiveCharacter]
    have h1 := primitiveCharacter_apply_of_isCoprime
      (changeLevel hMN' ψ * changeLevel hf D.primitiveCharacter) hpN'
    rw [MulChar.mul_apply, changeLevel_eq_cast_of_dvd' _ _ hpN', changeLevel_eq_cast_of_dvd' _ _ hpN'] at h1
    rw [he, prim_changeLevel]
    simpa using h1
  have hψp : ψ.primitiveCharacter p = ψ p := by simpa using primitiveCharacter_apply_of_isCoprime ψ hpM'
  rw [hψp]
  by_cases hD : p ∣ D.conductor
  · -- then `D*(p) = 0`, and `(ψD)*(p) ≠ 0` would give `D*(p) = ψ⁻¹(p) (ψD)*(p) ≠ 0`
    rw [(hzero D.primitiveCharacter).2 hD, mul_zero]
    by_contra hne
    have := key ψ⁻¹ _ (fun hc => hne ((hzero _).2 hc))
    rw [map_inv, inv_mul_cancel_left, (hzero D.primitiveCharacter).2 hD] at this
    exact mul_ne_zero (fun h0 => hpM ((hzero ψ⁻¹).1 h0)) hne this.symm
  · exact key ψ D hD

/-- Two characters with the same values have the same `L`-function, also at levels that are equal only
propositionally. -/
theorem LFunction_congr {M M' : ℕ} [NeZero M] [NeZero M'] (h : M = M') {ψ : DirichletCharacter ℂ M}
    {ψ' : DirichletCharacter ℂ M'} (hv : ∀ n : ℕ, ψ n = ψ' n) : LFunction ψ = LFunction ψ' := by
  subst h
  congr
  refine MulChar.ext' fun x => ?_
  rw [← ZMod.natCast_zmod_val x]
  exact hv x.val

/-! ## Legendre characters -/

/-- `χ_p = (·/p)`, the Legendre symbol as a Dirichlet character mod `p`. -/
noncomputable def legChar (p : ℕ) [Fact p.Prime] : DirichletCharacter ℂ p :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

/-- `χ_p` is the quadratic character of `ℤ/p`. -/
theorem legChar_apply {p : ℕ} [Fact p.Prime] (x : ZMod p) : legChar p x = quadraticChar (ZMod p) x := by
  simp [legChar, MulChar.ringHomComp_apply]

/-- `χ_p(0) = 0`. -/
theorem legChar_zero {p : ℕ} [Fact p.Prime] : legChar p 0 = 0 := by
  rw [legChar_apply, quadraticChar_zero, Int.cast_zero]

/-- `χ_p(n) = (n/p)`. -/
theorem legChar_natCast {p : ℕ} [Fact p.Prime] (n : ℕ) : legChar p n = legendreSym p n := by
  rw [legChar_apply, legendreSym, Int.cast_natCast]

/-- For an odd prime `p`, `χ_p` is primitive. -/
theorem legChar_isPrimitive {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) : (legChar p).IsPrimitive := by
  rcases (Nat.dvd_prime hp.out).1 (legChar p).conductor_dvd_level with h | h
  · refine absurd (eq_one_iff_conductor_eq_one.2 h) ?_
    exact (MulChar.ringHomComp_ne_one_iff (Int.castRingHom ℂ).injective_int).2
      (quadraticChar_ne_one (by rwa [ZMod.ringChar_zmod_n]))
  · exact h

/-- `χ_p^α`, for `α ∈ {0, 1}` (`false`, `true`). -/
noncomputable def legPow (p : ℕ) [Fact p.Prime] (α : Bool) : DirichletCharacter ℂ p :=
  if α then legChar p else 1

/-- `(χ_p^α)*(n) = χ_p(n)^α`, for an odd prime `p` and every `n`. -/
theorem prim_legPow {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (α : Bool) (n : ℕ) :
    (legPow p α).primitiveCharacter n = if α then legChar p n else 1 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  cases α
  · exact prim_one_apply n
  · exact prim_apply_of_isPrimitive (legChar_isPrimitive hp) n

/-! ## The characters of a finite abelian group -/

section Characters

variable {A : Type*} [CommGroup A] [Fintype A]

/-- `ξ(a)` is a root of unity, of norm `1`. -/
theorem norm_apply (ξ : A →* ℂˣ) (a : A) : ‖(ξ a : ℂ)‖ = 1 :=
  ((Units.coeHom ℂ).comp ξ |>.isOfFinOrder (isOfFinOrder_of_finite a)).norm_eq_one

/-- `conj ξ(a) = ξ(a⁻¹)`. -/
theorem conj_apply (ξ : A →* ℂˣ) (a : A) : conj (ξ a : ℂ) = ξ a⁻¹ := by
  rw [← Complex.inv_eq_conj (norm_apply ξ a), map_inv, Units.val_inv_eq_inv_val]

/-- `Σ_u ξ(u) = |A|·1[ξ = 1]`, over `u ∈ A`. -/
theorem sum_apply_dual (ξ : A →* ℂˣ) :
    ∑ u, (ξ u : ℂ) = if ξ = 1 then (Fintype.card A : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · exact sum_hom_units_eq_zero ((Units.coeHom ℂ).comp ξ) fun h' =>
      h (MonoidHom.ext fun u => Units.ext (by simpa using DFunLike.congr_fun h' u))

/-- `Σ_u conj ξ(u v) = |A|·1[ξ = 1]`, over `u ∈ A`. -/
theorem sum_conj_apply_mul (ξ : A →* ℂˣ) (v : A) :
    ∑ u, conj (ξ (u * v) : ℂ) = if ξ = 1 then (Fintype.card A : ℂ) else 0 := by
  rw [← map_sum, Fintype.sum_bijective _ (Group.mulRight_bijective v) _ (fun w => (ξ w : ℂ)) fun _ => rfl,
    sum_apply_dual]
  split_ifs <;> simp

variable [Fintype (A →* ℂˣ)]

/-- `A` has `|A|` characters. -/
theorem card_dual : Fintype.card (A →* ℂˣ) = Fintype.card A := by
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity]

variable [DecidableEq A]

/-- `Σ_ξ ξ(a) = |A|·1[a = 1]`, over the characters `ξ` of `A`. -/
theorem sum_dual_apply (a : A) :
    ∑ ξ : A →* ℂˣ, (ξ a : ℂ) = if a = 1 then (Fintype.card A : ℂ) else 0 := by
  split_ifs with ha
  · subst ha
    simp only [map_one, Units.val_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, card_dual]
  · obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity A ℂ ha
    refine eq_zero_of_mul_eq_self_left (fun h => hψ (Units.ext h)) ?_
    rw [Finset.mul_sum]
    exact Fintype.sum_bijective _ (Group.mulLeft_bijective ψ) _ _ fun ξ => by simp

/-- **Orthogonality on `A`**: `Σ_ξ conj ξ(v) ξ(w) = |A|·1[v = w]`. -/
theorem sum_conj_mul (v w : A) :
    ∑ ξ : A →* ℂˣ, conj (ξ v : ℂ) * ξ w = if v = w then (Fintype.card A : ℂ) else 0 := by
  simp only [conj_apply, ← Units.val_mul, ← map_mul, sum_dual_apply, inv_mul_eq_one]

end Characters

/-! ## `Φ`, `G` and the characters of `G` -/

/-- `Φ = {±1} × A`. -/
abbrev Φ (A : Type*) := ℤˣ × A

/-- `G = {±1} × Φ = {±1} × {±1} × A`; `Φ` is its subgroup `{1} × Φ`, of index `2`. -/
abbrev G (A : Type*) := ℤˣ × Φ A

section Group

variable {A : Type*} [CommGroup A]

/-- `c = (−1, −1, 1)`, the class of `−1` when `d ≡ q ≡ 3 (mod 4)` and `−1 ∈ K`. -/
def c (A : Type*) [CommGroup A] : G A := (-1, -1, 1)

/-- `γ_t(ρ) = c·ρ·(1, 1, t)⁻¹`, which lies outside `Φ`. -/
def γ (t : A) (ρ : Φ A) : G A := c A * (1, ρ) * (1, 1, t)⁻¹

/-- `γ_t(1, s, u) = (−1, −s, u t⁻¹)`. -/
theorem γ_apply (t : A) (s : ℤˣ) (u : A) : γ t (s, u) = (-1, -s, u * t⁻¹) := by
  simp [γ, c]

/-- The characters of `G`: triples `(α, β, ξ)`, with `α, β ∈ {0, 1}` (`false`, `true`) and `ξ` a character
of `A`. -/
abbrev Dual (A : Type*) [CommGroup A] := Bool × Bool × (A →* ℂˣ)

/-- `σ^α` for `σ ∈ {±1}` and `α ∈ {0, 1}`. -/
def sgnPow (α : Bool) (σ : ℤˣ) : ℂ := if α then ((σ : ℤ) : ℂ) else 1

/-- `χ(s_d, s_q, u) = s_d^α s_q^β ξ(u)` for `χ = (α, β, ξ)`. -/
def eval (χ : Dual A) (g : G A) : ℂ := sgnPow χ.1 g.1 * sgnPow χ.2.1 g.2.1 * (χ.2.2 g.2.2 : ℂ)

/-- `conj χ(γ_t(1, s, u)) = (−1)^α (−s)^β conj ξ(u t⁻¹)`. -/
theorem conj_eval_γ (χ : Dual A) (t : A) (s : ℤˣ) (u : A) :
    conj (eval χ (γ t (s, u))) = sgnPow χ.1 (-1) * sgnPow χ.2.1 (-s) * conj (χ.2.2 (u * t⁻¹) : ℂ) := by
  have h : ∀ (α : Bool) (σ : ℤˣ), conj (sgnPow α σ) = sgnPow α σ := fun α σ => by
    cases α <;> simp [sgnPow]
  rw [γ_apply, eval, map_mul, map_mul, h, h]

/-- A sum over the characters of `G` of a product of functions of `α`, of `β` and of `ξ`. -/
theorem sum_dual_mul [Fintype (A →* ℂˣ)] (f g : Bool → ℂ) (h : (A →* ℂˣ) → ℂ) :
    ∑ χ : Dual A, f χ.1 * g χ.2.1 * h χ.2.2 = (f true + f false) * (g true + g false) * ∑ ξ, h ξ := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.mul_sum]
  ring

/-- **The main-term coefficient**: `Σ_{ρ ∈ Φ} conj χ(γ_t(ρ)) = Σ_{g ∉ Φ} conj χ(g)` is `|Φ|` at `χ = 1`, `−|Φ|` at
`χ = (1, 0, 1)` (which gives `χ_d`), and `0` otherwise. -/
theorem sum_conj_eval_γ [Fintype A] (χ : Dual A) (t : A) :
    ∑ ρ : Φ A, conj (eval χ (γ t ρ)) =
      if χ.2.1 = false ∧ χ.2.2 = 1 then sgnPow χ.1 (-1) * Fintype.card (Φ A) else 0 := by
  have hs : ∑ s : ℤˣ, sgnPow χ.2.1 (-s) = if χ.2.1 = false then 2 else 0 := by
    rw [UnitsInt.univ, Finset.sum_pair (by decide)]
    cases χ.2.1 <;> norm_num [sgnPow]
  rw [Fintype.sum_prod_type]
  simp only [conj_eval_γ, ← Finset.mul_sum, sum_conj_apply_mul, ← Finset.sum_mul, hs, Fintype.card_prod,
    Fintype.card_units_int]
  by_cases hβ : χ.2.1 = false <;> by_cases hξ : χ.2.2 = 1 <;> simp [hβ, hξ]
  ring

end Group

/-! ## Signs -/

/-- The Legendre symbol `(a/p)` as a sign in `{±1}`, for `a` prime to `p` (and `1` for `p ∣ a`). -/
def sgn (p : ℕ) [Fact p.Prime] (a : ℤ) : ℤˣ := if legendreSym p a = -1 then -1 else 1

/-- `sgn p a = (a/p)` for `a` prime to `p`. -/
theorem sgn_coe {p : ℕ} [Fact p.Prime] {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    ((sgn p a : ℤ) : ℂ) = legendreSym p a := by
  unfold sgn
  rcases legendreSym.eq_one_or_neg_one p ha with h | h <;> simp [h]

/-- `s σ + 1 = 2·1[s = σ]` on `{±1}`. -/
theorem units_mul_add_one (s σ : ℤˣ) : ((s : ℤ) : ℂ) * ((σ : ℤ) : ℂ) + 1 = if s = σ then 2 else 0 := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or σ with rfl | rfl <;>
    norm_num [show (1 : ℤˣ) ≠ -1 by decide, show (-1 : ℤˣ) ≠ 1 by decide]

/-! ## The setting -/

/-- The setting of Lemma B: primes `q` and `d` with `q ≡ 3 (mod 4)` and `(2/d) = (q/d) = 1`, a modulus `QS` prime to
`q` whose every prime `p` has `(p/d) = 1` (it splits in `ℚ(√−d)` when `d ≡ 3 (mod 4)`), and a subgroup `K` of
`(ℤ/QS)ˣ`. -/
structure Setting where
  /-- The prime `q`. -/
  q : ℕ
  /-- The prime `d`. -/
  d : ℕ
  /-- The modulus `QS` of `A`. -/
  QS : ℕ
  /-- The subgroup `K` of `(ℤ/QS)ˣ`, with `A = (ℤ/QS)ˣ/K`. -/
  K : Subgroup (ZMod QS)ˣ
  [q_prime : Fact q.Prime]
  [d_prime : Fact d.Prime]
  [QS_neZero : NeZero QS]
  /-- `q ≡ 3 (mod 4)`. -/
  q_mod_four : q % 4 = 3
  /-- `(2/d) = 1`. -/
  two_mod_d : legendreSym d 2 = 1
  /-- `(q/d) = 1`. -/
  q_mod_d : legendreSym d q = 1
  /-- `q ∤ QS`. -/
  q_coprime : q.Coprime QS
  /-- Every prime `p ∣ QS` has `(p/d) = 1`. -/
  split : ∀ p : ℕ, p.Prime → p ∣ QS → legendreSym d p = 1

attribute [instance] Setting.q_prime Setting.d_prime Setting.QS_neZero

namespace Setting

variable (S : Setting)

/-! ### The group `A` and its characters -/

/-- `A = (ℤ/QS)ˣ/K`. -/
def A : Type := (ZMod S.QS)ˣ ⧸ S.K

noncomputable instance : CommGroup S.A := QuotientGroup.Quotient.commGroup _
instance : Finite S.A := inferInstanceAs (Finite ((ZMod S.QS)ˣ ⧸ S.K))
noncomputable instance : Fintype S.A := Fintype.ofFinite _
noncomputable instance : DecidableEq S.A := Classical.decEq _
noncomputable instance : Fintype (S.A →* ℂˣ) := Fintype.ofFinite _

/-- The quotient map `(ℤ/QS)ˣ → A`. -/
noncomputable def mkA : (ZMod S.QS)ˣ →* S.A := QuotientGroup.mk' _

/-- The quotient map is onto. -/
theorem mkA_surjective : Function.Surjective S.mkA := QuotientGroup.mk'_surjective _

/-- The class `[n]_A` of `n` prime to `QS` (and `1` for the others). -/
noncomputable def clsA (n : ℕ) : S.A := if h : IsUnit (n : ZMod S.QS) then S.mkA h.unit else 1

/-- `ξ̃`, the character mod `QS` with `ξ̃(n) = ξ([n]_A)` for `n` prime to `QS`. -/
noncomputable def lift (ξ : S.A →* ℂˣ) : DirichletCharacter ℂ S.QS :=
  MulChar.ofUnitHom (ξ.comp S.mkA)

/-- `ξ̃(n) = ξ([n]_A)` for `n` prime to `QS`. -/
theorem lift_apply (ξ : S.A →* ℂˣ) {n : ℕ} (hn : IsUnit (n : ZMod S.QS)) : S.lift ξ n = ξ (S.clsA n) := by
  conv_lhs => rw [← hn.unit_spec]
  rw [clsA, dite_eq_left hn, lift, MulChar.ofUnitHom_coe]
  rfl

/-- `1̃ = 1`. -/
theorem lift_one : S.lift 1 = 1 :=
  MulChar.ext fun u => by simp [lift]

/-- `ξ̃^k = (ξ^k)~`. -/
theorem lift_pow (ξ : S.A →* ℂˣ) (k : ℕ) : S.lift (ξ ^ k) = S.lift ξ ^ k :=
  MulChar.ext fun u => by simp [lift, MulChar.pow_apply_coe]

/-- `ξ̃ = 1` only for `ξ = 1`. -/
theorem eq_one_of_lift_eq_one {ξ : S.A →* ℂˣ} (h : S.lift ξ = 1) : ξ = 1 := by
  ext a
  obtain ⟨u, rfl⟩ := S.mkA_surjective a
  have := congr_arg (fun ψ : DirichletCharacter ℂ _ => ψ u) h
  simpa [lift, MulChar.ofUnitHom_coe] using this

/-- `ξ̃*` vanishes at a prime of `QS` unless `ξ = 1`: otherwise the conductor of `ξ̃`, a divisor of `QS`, would be
prime to `QS`. -/
theorem eq_one_of_prim_lift {ξ : S.A →* ℂˣ}
    (h : ∀ p : ℕ, p.Prime → p ∣ S.QS → (S.lift ξ).primitiveCharacter p ≠ 0) : ξ = 1 := by
  refine S.eq_one_of_lift_eq_one (eq_one_iff_conductor_eq_one.2 ?_)
  refine Nat.Coprime.eq_one_of_dvd (Nat.coprime_of_dvd fun p hp hpQ hpc => ?_).symm
    (S.lift ξ).conductor_dvd_level
  have h1 := (apply_ne_zero_iff (S.lift ξ).primitiveCharacter (p : ℤ)).1 (by simpa using h p hp hpQ)
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.isCoprime_iff_coprime.1 h1) hpc

/-! ### The primes and the level -/

/-- `q` is odd. -/
theorem q_ne_two : S.q ≠ 2 := fun h => by have := S.q_mod_four; omega

/-- `d` is odd, as `(2/d) ≠ 0`. -/
theorem d_ne_two : S.d ≠ 2 := fun h => by
  have h0 : ((2 : ℤ) : ZMod S.d) = 0 := by simpa using (ZMod.natCast_eq_zero_iff 2 S.d).2 ⟨1, by rw [h]⟩
  have := S.two_mod_d
  rw [(legendreSym.eq_zero_iff S.d 2).2 h0] at this
  exact zero_ne_one this

/-- `q ≠ d`, as `(q/d) ≠ 0`. -/
theorem q_ne_d : S.q ≠ S.d := fun h => by
  have h0 : ((S.q : ℤ) : ZMod S.d) = 0 := by
    simpa using (ZMod.natCast_eq_zero_iff S.q S.d).2 ⟨1, by rw [h, mul_one]⟩
  have := S.q_mod_d
  rw [(legendreSym.eq_zero_iff S.d S.q).2 h0] at this
  exact zero_ne_one this

/-- `q ∤ QS`. -/
theorem q_not_dvd : ¬ S.q ∣ S.QS := (Nat.Prime.coprime_iff_not_dvd Fact.out).1 S.q_coprime

/-- `d ∤ QS`, as `(d/d) = 0`. -/
theorem d_not_dvd : ¬ S.d ∣ S.QS := fun h => by
  have := S.split S.d Fact.out h
  rw [(legendreSym.eq_zero_iff S.d S.d).2 (by simp)] at this
  exact zero_ne_one this

/-- The level `N = QS·q·d`. -/
def N : ℕ := S.QS * S.q * S.d

instance : NeZero S.N :=
  ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne _) (Fact.out : S.q.Prime).ne_zero) (Fact.out : S.d.Prime).ne_zero⟩

/-- `d ∣ N`. -/
theorem d_dvd_N : S.d ∣ S.N := dvd_mul_left _ _

/-- `q ∣ N`. -/
theorem q_dvd_N : S.q ∣ S.N := (dvd_mul_left _ _).mul_right _

/-- `QS ∣ N`. -/
theorem QS_dvd_N : S.QS ∣ S.N := (dvd_mul_right _ _).mul_right _

/-! ### The sums -/

/-- The partner `ρ_t(n) = ((−n/q), [n]_A t) ∈ Φ` of `n` prime to `QS·q`. -/
noncomputable def partner (t : S.A) (n : ℕ) : Φ S.A := (sgn S.q (-n), S.clsA n * t)

/-- `D_χ = χ_d^α χ_q^β ξ̃` at level `N`, for `χ = (α, β, ξ)`. -/
noncomputable def D (χ : Dual S.A) : DirichletCharacter ℂ S.N :=
  changeLevel S.d_dvd_N (legPow S.d χ.1) * changeLevel S.q_dvd_N (legPow S.q χ.2.1) *
    changeLevel S.QS_dvd_N (S.lift χ.2.2)

/-- The error `g_χ`: `WindowGRH.rampErr` of the primitive character `χ*` inducing `D_χ`. -/
noncomputable def g (χ : Dual S.A) (y : ℝ) : ℂ := WindowGRH.rampErr (S.D χ).primitiveCharacter y

/-- `ASK(a, t, W) = Σ_{(n, QS·q) = 1} Λ(n)(1 − χ_d(n))(a/n − W(ρ_t(n)))⁺`, a finite sum. -/
noncomputable def ASK (a : ℝ) (t : S.A) (W : Φ S.A → ℝ) : ℝ :=
  ∑' n : ℕ, if n.Coprime (S.QS * S.q) then Λ n * (1 - legendreSym S.d n) * max (a / n - W (S.partner t n)) 0
    else 0

/-- `MAIN(a, W) = a(log a − 1 − γ + Re L'/L(1, χ_d) − |Φ|⁻¹ Σ_{ρ ∈ Φ} log W(ρ))`. -/
noncomputable def MAIN (a : ℝ) (W : Φ S.A → ℝ) : ℝ :=
  a * (Real.log a - 1 - Real.eulerMascheroniConstant + (logDeriv (LFunction (legChar S.d)) 1).re -
    (Fintype.card (Φ S.A) : ℝ)⁻¹ * ∑ ρ, Real.log (W ρ))

/-- The gap `Σ_{t ∈ TT} Σ_{j < m} [ASK(a_t, t, w_{u₀, j}) − MAIN(a_t, w_{u₀, j})]`. -/
noncomputable def gap (TT : Finset S.A) (m : ℕ) (a : S.A → ℝ) (w : S.A → Fin m → Φ S.A → ℝ) (u₀ : S.A) : ℝ :=
  ∑ t ∈ TT, ∑ j, (S.ASK (a t) t (w u₀ j) - S.MAIN (a t) (w u₀ j))

/-! ### Primitive values -/

/-- **`χ*` at prime powers**: `χ*(n) = (χ_d^α)*(n) (χ_q^β)*(n) ξ̃*(n)`. At a prime `p`, each factor of level prime
to `p` splits off (`prim_mul_apply`), and the remaining one keeps its primitive character. -/
theorem prim_D (χ : Dual S.A) {n : ℕ} (hn : IsPrimePow n) :
    (S.D χ).primitiveCharacter n = (legPow S.d χ.1).primitiveCharacter n *
      (legPow S.q χ.2.1).primitiveCharacter n * (S.lift χ.2.2).primitiveCharacter n := by
  obtain ⟨p, k, hp, -, rfl⟩ := (isPrimePow_nat_iff _).1 hn
  simp only [Nat.cast_pow, map_pow, ← mul_pow]
  congr 1
  have hqp : S.q.Prime := Fact.out
  have hdp : S.d.Prime := Fact.out
  unfold D
  by_cases hpd : p = S.d
  · subst hpd
    rw [show ∀ x y z : DirichletCharacter ℂ S.N, x * y * z = y * (z * x) from fun x y z => by ac_rfl,
      prim_mul_apply _ _ _ hp fun h => S.q_ne_d ((Nat.prime_dvd_prime_iff_eq hp hqp).1 h).symm,
      prim_mul_apply _ _ _ hp S.d_not_dvd, prim_changeLevel]
    ring
  by_cases hpq : p = S.q
  · subst hpq
    rw [show ∀ x y z : DirichletCharacter ℂ S.N, x * y * z = x * (z * y) from fun x y z => by ac_rfl,
      prim_mul_apply _ _ _ hp fun h => S.q_ne_d ((Nat.prime_dvd_prime_iff_eq hp hdp).1 h),
      prim_mul_apply _ _ _ hp S.q_not_dvd, prim_changeLevel]
    ring
  · rw [mul_assoc, prim_mul_apply _ _ _ hp fun h => hpd ((Nat.prime_dvd_prime_iff_eq hp hdp).1 h),
      prim_mul_apply _ _ _ hp fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hqp).1 h), prim_changeLevel]
    ring

/-- `D_χ = 1` only for `χ = 1`: otherwise `χ*` vanishes at `d`, at `q` or at a prime of `QS`. -/
theorem D_eq_one_iff (χ : Dual S.A) : S.D χ = 1 ↔ χ = (false, false, 1) := by
  constructor
  · intro h
    have hc : (S.D χ).conductor = 1 := eq_one_iff_conductor_eq_one.1 h
    have hne : ∀ {p : ℕ}, p.Prime → (S.D χ).primitiveCharacter p ≠ 0 := fun {p} _ => by
      have := (apply_ne_zero_iff (S.D χ).primitiveCharacter (p : ℤ)).2
        (by rw [hc, Nat.cast_one]; exact isCoprime_one_right)
      simpa using this
    have hd := hne (Fact.out : S.d.Prime)
    have hq := hne (Fact.out : S.q.Prime)
    rw [S.prim_D χ (Fact.out : S.d.Prime).isPrimePow, prim_legPow S.d_ne_two] at hd
    rw [S.prim_D χ (Fact.out : S.q.Prime).isPrimePow, prim_legPow S.q_ne_two (n := S.q)] at hq
    have hξ : χ.2.2 = 1 := S.eq_one_of_prim_lift fun p hp _ => by
      have h2 := hne hp
      rw [S.prim_D χ hp.isPrimePow] at h2
      exact right_ne_zero_of_mul h2
    obtain ⟨α, β, ξ⟩ := χ
    have hα : α = false := by
      cases α
      · rfl
      · simp [legChar_zero] at hd
    have hβ : β = false := by
      cases β
      · rfl
      · simp [legChar_zero] at hq
    simp only at hξ
    rw [hα, hβ, hξ]
  · rintro rfl
    simp [D, legPow, lift_one]

/-- `L(s, χ*) = L(s, χ_d)` at `χ = (1, 0, 1)`. -/
theorem LFunction_D_d : LFunction (S.D (true, false, 1)).primitiveCharacter = LFunction (legChar S.d) := by
  have hD : S.D (true, false, 1) = changeLevel S.d_dvd_N (legChar S.d) := by simp [D, legPow, lift_one]
  have hprim := legChar_isPrimitive S.d_ne_two
  refine LFunction_congr ?_ fun n => ?_
  · rw [hD, conductor_changeLevel, (isPrimitive_def _).1 hprim]
  · rw [hD, prim_changeLevel, prim_apply_of_isPrimitive hprim]

/-! ### The kernel -/

/-- **The kernel**: for a prime power `n` and `ρ ∈ Φ`, `Σ_χ conj χ(γ_t(ρ)) χ*(n)` is `|Φ|(1 − χ_d(n))` if `n` is
prime to `QS·q` and `ρ = ρ_t(n)`, and `0` otherwise. -/
theorem kernel (t : S.A) (ρ : Φ S.A) {n : ℕ} (hn : IsPrimePow n) :
    ∑ χ : Dual S.A, conj (eval χ (γ t ρ)) * (S.D χ).primitiveCharacter n =
      Fintype.card (Φ S.A) * if n.Coprime (S.QS * S.q) ∧ ρ = S.partner t n then 1 - legChar S.d n else 0 := by
  obtain ⟨s, u⟩ := ρ
  have hfac : ∀ χ : Dual S.A, conj (eval χ (γ t (s, u))) * (S.D χ).primitiveCharacter n =
      sgnPow χ.1 (-1) * (legPow S.d χ.1).primitiveCharacter n *
      (sgnPow χ.2.1 (-s) * (legPow S.q χ.2.1).primitiveCharacter n) *
      (conj (χ.2.2 (u * t⁻¹) : ℂ) * (S.lift χ.2.2).primitiveCharacter n) := fun χ => by
    rw [conj_eval_γ, S.prim_D χ hn]
    ring
  rw [Finset.sum_congr rfl fun χ _ => hfac χ,
    sum_dual_mul (fun α => sgnPow α (-1) * (legPow S.d α).primitiveCharacter n)
      (fun β => sgnPow β (-s) * (legPow S.q β).primitiveCharacter n)
      (fun ξ => conj (ξ (u * t⁻¹) : ℂ) * (S.lift ξ).primitiveCharacter n)]
  simp only [sgnPow, prim_legPow S.d_ne_two, prim_legPow S.q_ne_two, ite_true, Bool.false_eq_true, ite_false,
    Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, one_mul]
  by_cases hc : n.Coprime (S.QS * S.q)
  · -- `n` prime to `QS·q`
    obtain ⟨hcQ, hcq⟩ := Nat.coprime_mul_iff_right.1 hc
    have hunit : IsUnit (n : ZMod S.QS) := (ZMod.isUnit_iff_coprime _ _).2 hcQ
    have hq0 : (n : ZMod S.q) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => (Nat.Prime.coprime_iff_not_dvd (Fact.out : S.q.Prime)).1 hcq.symm h
    have hξ : ∑ ξ : S.A →* ℂˣ, conj (ξ (u * t⁻¹) : ℂ) * (S.lift ξ).primitiveCharacter n =
        if u * t⁻¹ = S.clsA n then (Fintype.card S.A : ℂ) else 0 := by
      rw [← sum_conj_mul]
      refine Finset.sum_congr rfl fun ξ _ => ?_
      have hcop : IsCoprime (n : ℤ) (S.QS : ℕ) := Nat.isCoprime_iff_coprime.2 hcQ
      have := primitiveCharacter_apply_of_isCoprime (S.lift ξ) hcop
      simp only [Int.cast_natCast] at this
      rw [this, S.lift_apply ξ hunit]
    -- `(−n/q) = −(n/q)`, as `q ≡ 3 (mod 4)`
    have hsgn : legChar S.q n = -((sgn S.q (-n) : ℤ) : ℂ) := by
      have hq0' : ((-n : ℤ) : ZMod S.q) ≠ 0 := by push_cast; exact neg_ne_zero.2 hq0
      rw [sgn_coe hq0', show (-n : ℤ) = -1 * n by ring, legendreSym.mul, legendreSym.at_neg_one S.q_ne_two,
        ZMod.χ₄_nat_three_mod_four S.q_mod_four, legChar_natCast]
      push_cast
      ring
    rw [hξ, hsgn, show -((s : ℤ) : ℂ) * -((sgn S.q (-n) : ℤ) : ℂ) + 1 =
      ((s : ℤ) : ℂ) * ((sgn S.q (-n) : ℤ) : ℂ) + 1 by ring, units_mul_add_one,
      Fintype.card_prod, Fintype.card_units_int]
    simp only [partner, Prod.mk.injEq, mul_inv_eq_iff_eq_mul]
    split_ifs <;> simp_all
    ring
  · -- `n` a power of a prime of `QS·q`: `χ_d(n) = 1`
    obtain ⟨p, k, hp, -, rfl⟩ := (isPrimePow_nat_iff _).1 hn
    have hpQq : p ∣ S.QS * S.q := by
      by_contra h
      exact hc (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 h))
    have h1 : legChar S.d (p ^ k : ℕ) = 1 := by
      rw [Nat.cast_pow, map_pow, legChar_natCast]
      rcases (Nat.Prime.dvd_mul hp).1 hpQq with h | h
      · simp only [S.split p hp h, Int.cast_one, one_pow]
      · rw [(Nat.prime_dvd_prime_iff_eq hp (Fact.out : S.q.Prime)).1 h]
        simp only [S.q_mod_d, Int.cast_one, one_pow]
    rw [h1, ite_eq_right (fun h => hc h.1)]
    ring

/-! ### Lemma B -/

/-- The ramp sum up to any `K ≥ y`, as a sum of ramps `(y/n − 1)⁺`. -/
theorem rampSum_eq_sum (f : ℕ → ℂ) {y : ℝ} {K : ℕ} (hK : ⌊y⌋₊ ≤ K) :
    RampLaplace.rampSum f y = ∑ n ∈ Finset.Icc 1 K, (Λ n : ℂ) * f n * ((max (y / n - 1) 0 : ℝ) : ℂ) := by
  rw [RampLaplace.rampSum_eq_tsum]
  refine tsum_eq_sum fun n hn => ?_
  rcases Nat.eq_zero_or_pos n with rfl | h1
  · simp
  · have h2 : y < n := Nat.lt_of_floor_lt (by rw [Finset.mem_Icc] at hn; omega)
    rw [max_eq_right (by rw [sub_nonpos, div_le_one₀ (by positivity)]; exact h2.le)]
    simp

/-- `W·g_χ(a/W)` is the ramp sum `Σ_{n ≤ K} Λ(n) χ*(n) (a/n − W)⁺` plus the main term: `(1 + γ)a − a log(a/W)` if
`χ* = 1`, and `a·L'/L(1, χ*)` otherwise. -/
theorem mul_g (χ : Dual S.A) {a w : ℝ} (hw : 0 < w) {K : ℕ} (hK : ⌊a / w⌋₊ ≤ K) :
    (w : ℂ) * S.g χ (a / w) = ∑ n ∈ Finset.Icc 1 K,
      (Λ n : ℂ) * (S.D χ).primitiveCharacter n * ((max (a / n - w) 0 : ℝ) : ℂ) +
      if (S.D χ).primitiveCharacter = 1 then
        (((1 + Real.eulerMascheroniConstant) * a - a * Real.log (a / w) : ℝ) : ℂ)
      else (a : ℂ) * logDeriv (LFunction (S.D χ).primitiveCharacter) 1 := by
  have hw0 : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have hramp : (w : ℂ) * RampLaplace.rampSum (fun n => (S.D χ).primitiveCharacter n) (a / w) =
      ∑ n ∈ Finset.Icc 1 K, (Λ n : ℂ) * (S.D χ).primitiveCharacter n * ((max (a / n - w) 0 : ℝ) : ℂ) := by
    rw [rampSum_eq_sum _ hK, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn : (n : ℝ) ≠ 0 := by have := (Finset.mem_Icc.1 hn).1; positivity
    have h : w * max (a / w / n - 1) 0 = max (a / n - w) 0 := by
      rw [mul_max_of_nonneg _ _ hw.le, mul_zero]
      congr 1
      field_simp
    rw [← h]
    push_cast
    ring
  unfold g WindowGRH.rampErr
  split_ifs with h
  · rw [mul_add, mul_sub, hramp]
    push_cast
    field_simp
    ring
  · rw [mul_add, hramp]
    push_cast
    field_simp

/-- **The main terms**: summed over `ρ ∈ Φ` and `χ`, they leave
`Σ_ρ ((1 + γ)a − a log(a/W(ρ))) − |Φ| a L'/L(1, χ_d)`. -/
theorem sum_main (t : S.A) (a : ℝ) (W : Φ S.A → ℝ) :
    ∑ ρ, ∑ χ : Dual S.A, conj (eval χ (γ t ρ)) * (if (S.D χ).primitiveCharacter = 1 then
        (((1 + Real.eulerMascheroniConstant) * a - a * Real.log (a / W ρ) : ℝ) : ℂ)
      else (a : ℂ) * logDeriv (LFunction (S.D χ).primitiveCharacter) 1) =
    ∑ ρ, (((1 + Real.eulerMascheroniConstant) * a - a * Real.log (a / W ρ) : ℝ) : ℂ) -
      Fintype.card (Φ S.A) * a * logDeriv (LFunction (legChar S.d)) 1 := by
  rw [Finset.sum_comm]
  have hχ : ∀ χ : Dual S.A, ∑ ρ, conj (eval χ (γ t ρ)) * (if (S.D χ).primitiveCharacter = 1 then
        (((1 + Real.eulerMascheroniConstant) * a - a * Real.log (a / W ρ) : ℝ) : ℂ)
      else (a : ℂ) * logDeriv (LFunction (S.D χ).primitiveCharacter) 1) =
      (if χ = (false, false, 1) then
        ∑ ρ, (((1 + Real.eulerMascheroniConstant) * a - a * Real.log (a / W ρ) : ℝ) : ℂ) else 0) +
      (if χ = (true, false, 1) then -(Fintype.card (Φ S.A) * a * logDeriv (LFunction (legChar S.d)) 1)
        else 0) := by
    intro χ
    by_cases h1 : χ = (false, false, 1)
    · subst h1
      have : (S.D (false, false, 1)).primitiveCharacter = 1 := (prim_eq_one_iff _).2 ((S.D_eq_one_iff _).2 rfl)
      simp [this, eval, sgnPow]
    · have hne : (S.D χ).primitiveCharacter ≠ 1 := fun h => h1 ((S.D_eq_one_iff χ).1 ((prim_eq_one_iff _).1 h))
      simp only [hne, ite_false, ite_eq_right h1, zero_add]
      rw [← Finset.sum_mul, sum_conj_eval_γ]
      by_cases h2 : χ = (true, false, 1)
      · subst h2
        simp [sgnPow, S.LFunction_D_d]
        ring
      · rw [ite_eq_right h2, ite_eq_right]
        · ring
        rintro ⟨hβ, hξ⟩
        obtain ⟨α, β, ξ⟩ := χ
        simp only at hβ hξ
        subst hβ hξ
        cases α
        · exact h1 rfl
        · exact h2 rfl
  rw [Finset.sum_congr rfl fun χ _ => hχ χ, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  ring

/-- **Lemma B, the balance identity**: for `a ∈ ℝ`, `t ∈ A` and `W : Φ → (0, ∞)`,
`ASK(a, t, W) − MAIN(a, W) = Re |Φ|⁻¹ Σ_{ρ ∈ Φ} W(ρ) Σ_χ conj χ(γ_t(ρ)) g_χ(a/W(ρ))`. -/
theorem balance (a : ℝ) (t : S.A) (W : Φ S.A → ℝ) (hW : ∀ ρ, 0 < W ρ) :
    S.ASK a t W - S.MAIN a W = ((Fintype.card (Φ S.A) : ℂ)⁻¹ *
      ∑ ρ, (W ρ : ℂ) * ∑ χ, conj (eval χ (γ t ρ)) * S.g χ (a / W ρ)).re := by
  set K := ∑ ρ, ⌊a / W ρ⌋₊
  have hK : ∀ ρ, ⌊a / W ρ⌋₊ ≤ K := fun ρ =>
    Finset.single_le_sum (f := fun ρ => ⌊a / W ρ⌋₊) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ρ)
  set M : Dual S.A → Φ S.A → ℂ := fun χ ρ => if (S.D χ).primitiveCharacter = 1 then
      (((1 + Real.eulerMascheroniConstant) * a - a * Real.log (a / W ρ) : ℝ) : ℂ)
    else (a : ℂ) * logDeriv (LFunction (S.D χ).primitiveCharacter) 1
  -- `ASK` as a finite sum
  have hASK : S.ASK a t W = ∑ n ∈ Finset.Icc 1 K, if n.Coprime (S.QS * S.q) then
      Λ n * (1 - legendreSym S.d n) * max (a / n - W (S.partner t n)) 0 else 0 := by
    refine tsum_eq_sum fun n hn => ?_
    split_ifs with hc
    · rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp
      · have hlt : a / W (S.partner t n) < n :=
          Nat.lt_of_floor_lt ((hK _).trans_lt (by rw [Finset.mem_Icc] at hn; omega))
        rw [div_lt_iff₀ (hW _)] at hlt
        rw [max_eq_right, mul_zero]
        rw [sub_nonpos, div_le_iff₀ (by exact_mod_cast hpos)]
        linarith
    · rfl
  -- each `W(ρ) Σ_χ conj χ(γ_t(ρ)) g_χ(a/W(ρ))`, expanded
  have h1 : ∀ ρ, (W ρ : ℂ) * ∑ χ, conj (eval χ (γ t ρ)) * S.g χ (a / W ρ) =
      ∑ n ∈ Finset.Icc 1 K, (Λ n : ℂ) * ((max (a / n - W ρ) 0 : ℝ) : ℂ) *
        ∑ χ, conj (eval χ (γ t ρ)) * (S.D χ).primitiveCharacter n +
      ∑ χ, conj (eval χ (γ t ρ)) * M χ ρ := by
    intro ρ
    rw [Finset.mul_sum, Finset.sum_congr rfl fun χ _ => by rw [mul_left_comm, S.mul_g χ (hW ρ) (hK ρ)]]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun χ _ => by ring
  -- the ramp parts: the kernel
  have h2 : ∑ ρ, ∑ n ∈ Finset.Icc 1 K, (Λ n : ℂ) * ((max (a / n - W ρ) 0 : ℝ) : ℂ) *
      ∑ χ, conj (eval χ (γ t ρ)) * (S.D χ).primitiveCharacter n =
      Fintype.card (Φ S.A) * (S.ASK a t W : ℂ) := by
    have hterm : ∀ ρ n, (Λ n : ℂ) * ((max (a / n - W ρ) 0 : ℝ) : ℂ) *
        ∑ χ, conj (eval χ (γ t ρ)) * (S.D χ).primitiveCharacter n =
        Fintype.card (Φ S.A) * if n.Coprime (S.QS * S.q) ∧ ρ = S.partner t n then
          ((Λ n * (1 - legendreSym S.d n) * max (a / n - W (S.partner t n)) 0 : ℝ) : ℂ) else 0 := by
      intro ρ n
      by_cases hΛ : Λ n = 0
      · simp [hΛ]
      · rw [S.kernel t ρ (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hΛ)]
        split_ifs with h
        · rw [h.2, legChar_natCast]
          push_cast
          ring
        · simp
    rw [Finset.sum_comm, hASK, ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_congr rfl fun ρ _ => hterm ρ n, ← Finset.mul_sum]
    by_cases hc : n.Coprime (S.QS * S.q)
    · simp only [and_iff_right hc, ite_eq_left hc, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    · simp [hc]
  rw [Finset.sum_congr rfl fun ρ _ => h1 ρ, Finset.sum_add_distrib, h2, S.sum_main t a W]
  have hlog : ∀ ρ, a * Real.log (a / W ρ) = a * Real.log a - a * Real.log (W ρ) := fun ρ => by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · rw [Real.log_div ha (hW ρ).ne']
      ring
  -- real parts: everything but `L'/L(1, χ_d)` is real
  set c : ℝ := (Fintype.card (Φ S.A) : ℝ)
  have hc : (Fintype.card (Φ S.A) : ℂ) = (c : ℂ) := by simp [c]
  have hc0 : c ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [hc, ← ofReal_sum, show (c : ℂ) * a * logDeriv (LFunction (legChar S.d)) 1 =
    ((c * a : ℝ) : ℂ) * logDeriv (LFunction (legChar S.d)) 1 by push_cast; ring, ← ofReal_inv, ← ofReal_mul,
    re_ofReal_mul, add_re, sub_re, ofReal_re, ofReal_re, re_ofReal_mul, MAIN]
  simp only [hlog, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  field_simp
  ring

end Setting

end ZetaBalance

#print axioms ZetaBalance.Setting.balance
