import Mathlib
import ZetaBalance

/-!
# The CM host of a setting

Layer L0 of the sharp frontier for the library's proof of the Riemann hypothesis (`docs/rh-rebuild.md`): the specific
fields and parameter shapes that a `ZetaBalance.Setting` determines. The layers L2 to L6 are generic in a CM field
`E`, a CM type `τ : Φ → (E →+* L)` and a coefficient field `L`; this layer and L7 know the specific ones.

**The ranks** (`Setting.Ranks`): `(k, m, t)` with `k, m` even, `t` odd, `2 ≤ m`, `m + 3 ≤ k`, `k + m + 4 ≤ t`,
`3m < t`, `m ≤ f ≤ k` for `f = |Φ| = 2|A|` (`Setting.f`), and `m² ≤ k + m(t + 1)`; with `N_j = k + j(t + 1)`,
`r = k + m − 1`, `nV = r + t` and `h = (t + 1)/2`.

**The Harish-Chandra parameters** (`Setting.Ranks.HC`, and `Setting.Ranks.HCFamily` for one at each `τ ∈ Φ`):
`u ∈ (ℤ + ½)^k`, `v ∈ ℤ^{k−1}` and `b, e ∈ ℤ^m`, with `v_i < u_i`, `u_{i+1} < v_i`, `−b_0 < u_{k−1}`,
`e_j − b_j ≥ (t + 3)/2` and `b_{j+1} − e_j ≥ (t + 3)/2`. The weights of the balance are `w_j(τ) = e_j(τ)` (`wj`).

**The prime classes** (`Setting.cls`): Frobenius at `p ∤ N` is `[p] = ((p/d), (p/q), [p]_A) ∈ G` (`Setting.frob`).
The class of `p` is *split* if `(p/d) = 1`, *signal* if not and Frobenius fixes `√−q`, i.e. `(p/q) = 1`, and *inert*
otherwise. `hP(p) = [p]_A` (`Setting.hP`); with a twist `c ∈ A` (`Setting.twA`: `[−1]_A` for odd `κ`, else `1`),
`hP_c(p) = c·[p]_A` (`Setting.hPtw`), `nP(p)` is `2·ord(hP_c²)` for signal `p` and `ord(hP_c)` otherwise
(`Setting.nP`), and the orbit position is `pos_p(σ, t; s) = (σ·(−1)^{[p signal, s odd]}, t·hP_c(p)^s)`
(`Setting.pos`).

**The twist** (verify-A F1). For odd `χ` the archive works in the coordinates of its twisted Artin map
`u ↦ ((u/d), (u/q), [u]_A·[−1]_A^{[(u/q) = −1]})`, where complex conjugation `c̃` is `(−1, −1, 1)` and its
`hP(p) = [p]_A·[−1]_A^{[(p/q) = −1]}` is the `A`-part of `c̃·Frob_p`. This layer keeps the untwisted coordinates
(`artin`, `τ`), where `c̃ = (−1, −1, [−1]_A)`. Read in them through the relabelling `(s, t) ↦ (s, t·[−1]_A^{[s = −1]})`
of `Φ` that matches the two CM types, the archive's orbits step by `[−1]_A·[p]_A`, the `A`-part of `c̃·Frob_p` here, at
inert and signal `p` alike: that is `hP_c` with `c = [−1]_A`. For even `χ` the archive's Artin map is untwisted
(its `K` contains `−1`, so `[−1]_A = 1`), and `c = 1`.

**The field** (`Setting.E`): `N = QS·q·d`, the Artin map `(ℤ/N)ˣ → G`, `n ↦ ((n/d), (n/q), [n]_A)` (`Setting.artin`),
and `E` the fixed field in `ℚ(ζ_N)` of the automorphisms whose exponent lies in its kernel. So `Gal(E/ℚ) ≅ G`, and
`E = ℚ(√−d)·ℚ(√−q)·ℚ(ζ_QS)^K` when `d ≡ 3 (mod 4)`. It is a number field, Galois and abelian over `ℚ`, totally
complex, hence CM (`IsCMField.of_isAbelianGalois`).

**The CM type** (`Setting.τ`): with a fixed `φ₀ : E → ℂ`, `τ(s, t) = φ₀ ∘ σ_{(1, s, t)}`, in Lemma B's coordinates
`Φ = {1} × Φ ⊂ G`. The normalising height `v_E = |d_E|^{1/[E:ℚ]}/2` of L7 is `Setting.vE`.

**Checks.** `f = 2|A|` (`Setting.f_eq`); `|Gal(E/ℚ)| = 4|A|` (`Setting.card_gal`), as the Artin map is onto
(`Setting.artin_surjective`, by the Chinese remainder theorem); and `τ(ρ)` does not depend on the lift of `(1, ρ)`
(`Setting.τ_eq`), as `H` fixes `E`.

**Choices.**
* Totally complex needs no `d ≡ 3 (mod 4)`: complex conjugation is `σ_{−1}`, whose `q`-coordinate is
  `(−1/q) = −1` as `q ≡ 3 (mod 4)`, so it moves `E`. The setting does not assume `d ≡ 3 (mod 4)`, so neither does
  this layer; with it, `{1} × Φ` is `Gal(E/ℚ(√−d))` and `τ` is the CM type lifted from `ℚ(√−d)`.
* The classes and positions are defined for every `p` from `[p]`, read through `ZetaBalance.sgn` and
  `Setting.clsA`, as in `Setting.partner`; only `p ∤ N` is meant.
* The half-integers `u_i` are rationals with `u_i − ½ ∈ ℤ`; the parameters are indexed by `Fin`.
-/

open NumberField

namespace ZetaBalance.Setting

variable (S : Setting)

/-! ## Ranks -/

/-- `f = |Φ| = 2|A|`, the size of the CM type. -/
noncomputable def f : ℕ := Fintype.card (Φ S.A)

/-- The ranks `(k, m, t)` (L0.5). -/
structure Ranks where
  /-- The rank `k`. -/
  k : ℕ
  /-- The rank `m`. -/
  m : ℕ
  /-- The rank `t`. -/
  t : ℕ
  /-- `k` is even. -/
  k_even : Even k
  /-- `m` is even. -/
  m_even : Even m
  /-- `t` is odd. -/
  t_odd : Odd t
  /-- `2 ≤ m`. -/
  two_le_m : 2 ≤ m
  /-- `m + 3 ≤ k`. -/
  m_add_three_le : m + 3 ≤ k
  /-- `k + m + 4 ≤ t`. -/
  k_add_m_add_four_le : k + m + 4 ≤ t
  /-- `3m < t`. -/
  three_m_lt : 3 * m < t
  /-- `m ≤ f`. -/
  m_le_f : m ≤ S.f
  /-- `f ≤ k`. -/
  f_le_k : S.f ≤ k
  /-- `m² ≤ k + m(t + 1)`. -/
  m_sq_le : m ^ 2 ≤ k + m * (t + 1)

namespace Ranks

variable {S} (R : S.Ranks)

/-- `N_j = k + j(t + 1)`. -/
def N (j : ℕ) : ℕ := R.k + j * (R.t + 1)

/-- `r = k + m − 1`. -/
def r : ℕ := R.k + R.m - 1

/-- `nV = r + t`. -/
def nV : ℕ := R.r + R.t


/-! ## Harish-Chandra parameters -/

/-- The Harish-Chandra parameter `(u, v, b, e)` at one `τ ∈ Φ` (L0.6). -/
structure HC where
  /-- `u ∈ (ℤ + ½)^k`. -/
  u : Fin R.k → ℚ
  /-- `v ∈ ℤ^{k−1}`. -/
  v : Fin (R.k - 1) → ℤ
  /-- `b ∈ ℤ^m`. -/
  b : Fin R.m → ℤ
  /-- `e ∈ ℤ^m`. -/
  e : Fin R.m → ℤ
  /-- Each `u_i` is a half-integer. -/
  u_half : ∀ i, ∃ n : ℤ, u i = n + 1 / 2
  /-- `v_i < u_i`. -/
  v_lt : ∀ i : Fin (R.k - 1), (v i : ℚ) < u (i.castLE (Nat.sub_le _ _))
  /-- `u_{i+1} < v_i`. -/
  lt_v : ∀ i : Fin (R.k - 1), u ⟨i + 1, by omega⟩ < v i
  /-- `−b_0 < u_{k−1}`. -/
  neg_b_lt : -(b ⟨0, by have := R.two_le_m; omega⟩ : ℚ) < u ⟨R.k - 1, by have := R.m_add_three_le; omega⟩
  /-- `e_j − b_j ≥ (t + 3)/2`. -/
  e_sub_b : ∀ j, ((R.t : ℤ) + 3) / 2 ≤ e j - b j
  /-- `b_{j+1} − e_j ≥ (t + 3)/2`. -/
  b_sub_e : ∀ (j : Fin R.m) (hj : (j : ℕ) + 1 < R.m), ((R.t : ℤ) + 3) / 2 ≤ b ⟨j + 1, hj⟩ - e j

/-- A family of Harish-Chandra parameters, one at each `τ ∈ Φ`. -/
abbrev HCFamily := Φ S.A → R.HC

/-- The weights of the balance, `w_j(τ) = e_j(τ)`. -/
def wj (hc : R.HCFamily) (j : Fin R.m) (τ : Φ S.A) : ℤ := (hc τ).e j

end Ranks

/-! ## Prime classes -/

/-- Frobenius at `p ∤ N`: its class `[p] = ((p/d), (p/q), [p]_A) ∈ G`. -/
noncomputable def frob (p : ℕ) : G S.A := (sgn S.d p, sgn S.q p, S.clsA p)

/-- The classes of the primes `p ∤ N`. -/
inductive PrimeClass
  /-- `(p/d) = 1`. -/
  | split
  /-- `(p/d) = −1` and Frobenius fixes `√−q`. -/
  | signal
  /-- `(p/d) = −1` and Frobenius moves `√−q`. -/
  | inert
  deriving DecidableEq

/-- The class of `p ∤ N`: split if `(p/d) = 1`; otherwise signal if `(p/q) = 1`, and inert if not. -/
noncomputable def cls (p : ℕ) : PrimeClass :=
  if (S.frob p).1 = 1 then .split else if (S.frob p).2.1 = 1 then .signal else .inert

/-- `hP(p) = [p]_A`, the `A`-part of Frobenius at `p`. -/
noncomputable def hP (p : ℕ) : S.A := (S.frob p).2.2

/-- **The twist** of a character `κ` of `A` (verify-A F1): `[−1]_A` when `κ` is odd, `κ([−1]_A) ≠ 1` (for `κ`
lifting `χ`, `κ([−1]_A) = χ(−1)`), and `1` when it is even. -/
noncomputable def twA (κ : S.A →* ℂˣ) : S.A := if κ (S.mkA (-1)) = 1 then 1 else S.mkA (-1)

/-- The twisted `hP_c(p) = c·[p]_A`: with `c = twA κ`, the archive's `hP` read in this layer's coordinates (module
docstring, "The twist"), at inert and signal `p`. -/
noncomputable def hPtw (c : S.A) (p : ℕ) : S.A := c * S.hP p

/-- `nP(p)`: `2·ord(hP_c(p)²)` for signal `p` and `ord(hP_c(p))` otherwise. -/
noncomputable def nP (c : S.A) (p : ℕ) : ℕ :=
  if S.cls p = .signal then 2 * orderOf (S.hPtw c p ^ 2) else orderOf (S.hPtw c p)

/-- The orbit position `pos_p(σ, t; s) = (σ·(−1)^{[p signal, s odd]}, t·hP_c(p)^s)`. -/
noncomputable def pos (c : S.A) (p : ℕ) (z : Φ S.A) (s : ℕ) : Φ S.A :=
  (z.1 * if S.cls p = .signal ∧ Odd s then -1 else 1, z.2 * S.hPtw c p ^ s)

/-! ## The field -/

/-- The Artin map `(ℤ/N)ˣ → G`, `n ↦ ((n/d), (n/q), [n]_A)`. -/
noncomputable def artin : (ZMod S.N)ˣ →* G S.A :=
  ((quadraticChar (ZMod S.d)).toUnitHom.comp (ZMod.unitsMap S.d_dvd_N)).prod
    (((quadraticChar (ZMod S.q)).toUnitHom.comp (ZMod.unitsMap S.q_dvd_N)).prod
      (S.mkA.comp (ZMod.unitsMap S.QS_dvd_N)))

/-- `N ≠ 0` in `ℚ`, for `CyclotomicField`. -/
instance : NeZero ((S.N : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.2 (NeZero.ne _)⟩

/-- `(·/p) : (ℤ/p)ˣ → {±1}` is onto for an odd prime `p`. -/
theorem toUnitHom_surjective {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    Function.Surjective (quadraticChar (ZMod p)).toUnitHom := by
  intro s
  rcases Int.units_eq_one_or s with rfl | rfl
  · exact ⟨1, map_one _⟩
  · obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
    exact ⟨a, Units.ext (by simpa using ha)⟩

/-- **The Artin map is onto**, by the Chinese remainder theorem for `N = QS·q·d`. -/
theorem artin_surjective : Function.Surjective S.artin := by
  rintro ⟨sd, sq, a⟩
  obtain ⟨xd, rfl⟩ := toUnitHom_surjective S.d_ne_two sd
  obtain ⟨xq, rfl⟩ := toUnitHom_surjective S.q_ne_two sq
  obtain ⟨xA, rfl⟩ := S.mkA_surjective a
  have c1 : (S.QS * S.q).Coprime S.d := Nat.Coprime.mul_left
    ((Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 S.d_not_dvd)))
    ((Nat.coprime_primes Fact.out Fact.out).2 S.q_ne_d)
  let e : ZMod S.N ≃+* (ZMod S.QS × ZMod S.q) × ZMod S.d := (ZMod.chineseRemainder c1).trans
    (RingEquiv.prodCongr (ZMod.chineseRemainder S.q_coprime.symm) (RingEquiv.refl (ZMod S.d)))
  have hy : IsUnit (e.symm (((xA : ZMod S.QS), (xq : ZMod S.q)), (xd : ZMod S.d))) :=
    (isUnit_map_iff e.symm _).2 (Prod.isUnit_iff.2 ⟨Prod.isUnit_iff.2 ⟨xA.isUnit, xq.isUnit⟩, xd.isUnit⟩)
  have hc : ∀ {m : ℕ} (hm : m ∣ S.N) (x : (ZMod m)ˣ) (f : (ZMod S.QS × ZMod S.q) × ZMod S.d →+* ZMod m),
      f ((xA, xq), xd) = x → ZMod.unitsMap hm hy.unit = x := fun hm x f hf => Units.ext (by
    rw [ZMod.unitsMap_val, IsUnit.unit_spec, ← hf]
    simpa using congr($(Subsingleton.elim (ZMod.castHom hm _) (f.comp (e : ZMod S.N →+* _))) (e.symm ((xA, xq), xd))))
  refine ⟨hy.unit, ?_⟩
  simp only [artin, MonoidHom.prod_apply, MonoidHom.comp_apply, hc S.d_dvd_N xd (RingHom.snd _ _) rfl,
    hc S.q_dvd_N xq ((RingHom.snd _ _).comp (RingHom.fst _ _)) rfl,
    hc S.QS_dvd_N xA ((RingHom.fst _ _).comp (RingHom.fst _ _)) rfl]

/-- `ℚ(ζ_N)`. -/
abbrev M : Type := CyclotomicField S.N ℚ

/-- `ℚ(ζ_N)` is the `N`-th cyclotomic extension of `ℚ`. -/
instance : IsCyclotomicExtension {S.N} ℚ S.M := CyclotomicField.isCyclotomicExtension _ _

/-- `Gal(ℚ(ζ_N)/ℚ) ≃ (ℤ/N)ˣ`, `σ ↦ a` with `σ ζ = ζ^a`. -/
noncomputable def autEquiv : Gal(S.M/ℚ) ≃* (ZMod S.N)ˣ :=
  IsCyclotomicExtension.autEquivPow S.M (Polynomial.cyclotomic.irreducible_rat (NeZero.pos _))

/-- The automorphisms of `ℚ(ζ_N)` whose exponent lies in the kernel of the Artin map. -/
noncomputable def H : Subgroup Gal(S.M/ℚ) := S.artin.ker.comap S.autEquiv.toMonoidHom

/-- **The CM field** `E`, the fixed field of `H` in `ℚ(ζ_N)`. -/
noncomputable abbrev E : IntermediateField ℚ S.M := IntermediateField.fixedField S.H

/-- `ℚ(ζ_N)` is abelian over `ℚ`; so is `E`, by Mathlib's instance. -/
instance : IsAbelianGalois ℚ S.M := IsCyclotomicExtension.isAbelianGalois {S.N} ℚ S.M

open ComplexConjugate in
/-- An automorphism that is complex conjugation under some `ψ : ℚ(ζ_N) → ℂ` is `σ_{−1}`: from
`ψ(ζ)^a = conj ψ(ζ) = ψ(ζ)⁻¹`, `N ∣ a + 1`. -/
theorem autEquiv_eq_neg_one {σ : Gal(S.M/ℚ)} (ψ : S.M →+* ℂ) (h : ∀ x, ψ (σ x) = conj (ψ x)) :
    S.autEquiv σ = -1 := by
  have hζ := IsCyclotomicExtension.zeta_spec S.N ℚ S.M
  have hψ := hζ.map_of_injective ψ.injective
  set ζ := IsCyclotomicExtension.zeta S.N ℚ S.M
  have h1 : ζ ^ (S.autEquiv σ : ZMod S.N).val = σ ζ := hζ.autToPow_spec ℚ σ
  have h2 : ψ ζ ^ ((S.autEquiv σ : ZMod S.N).val + 1) = 1 := by
    rw [pow_succ, ← map_pow, h1, h, Complex.conj_mul', hψ.norm'_eq_one (NeZero.ne _)]
    norm_num
  have h3 := (ZMod.natCast_eq_zero_iff _ _).2 (hψ.pow_eq_one_iff_dvd _ |>.1 h2)
  push_cast [ZMod.natCast_zmod_val] at h3
  exact Units.ext (by simpa using eq_neg_of_add_eq_zero_left h3)

/-- `[−1] ≠ 1`: its `q`-coordinate is `(−1/q) = −1`, as `q ≡ 3 (mod 4)`. -/
theorem artin_neg_one : S.artin (-1) ≠ 1 := fun h => by
  have h' := congrArg (fun g : G S.A => ((g.2.1 : ℤˣ) : ℤ)) h
  have hq : quadraticChar (ZMod S.q) (-1) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.2 fun hsq => ZMod.exists_sq_eq_neg_one_iff.1 hsq S.q_mod_four
  have hu : ((ZMod.unitsMap S.q_dvd_N (-1) : (ZMod S.q)ˣ) : ZMod S.q) = -1 := by
    simp only [ZMod.unitsMap, Units.coe_map, Units.val_neg, Units.val_one, MonoidHom.coe_ofClass]
    rw [map_neg, map_one]
  simp only [artin, MonoidHom.prod_apply, MonoidHom.comp_apply, MulChar.coe_toUnitHom, hu, hq] at h'
  simp at h'

open ComplexConjugate in
/-- `E` is totally complex: a real embedding `φ` of `E` extends to `ψ` on `ℚ(ζ_N)`, complex conjugation there is
`σ_{−1}`, which then fixes `E`, so `σ_{−1} ∈ H`, against `artin_neg_one`. -/
instance : IsTotallyComplex S.E := by
  refine ⟨fun w => InfinitePlace.isComplex_iff.2 fun hw => ?_⟩
  let : Algebra S.E ℂ := w.embedding.toAlgebra
  let ψ : S.M →ₐ[S.E] ℂ := IsAlgClosed.lift
  obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) ψ.toRingHom
    (ComplexEmbedding.conjugate ψ.toRingHom) (by ext; simp)
  have hσ' : ∀ x, ψ (σ.symm x) = conj (ψ x) := fun x => congr($hσ x)
  have hmem : σ.symm ∈ S.H := by
    rw [← IntermediateField.fixingSubgroup_fixedField S.H, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    apply ψ.toRingHom.injective
    have hc : conj (w.embedding ⟨x, hx⟩) = w.embedding ⟨x, hx⟩ := congr($hw ⟨x, hx⟩)
    have hx' := ψ.commutes ⟨x, hx⟩
    simp only [IntermediateField.algebraMap_apply] at hx'
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hσ', hx']
    exact hc
  exact S.artin_neg_one (by simpa [H, S.autEquiv_eq_neg_one ψ.toRingHom hσ'] using hmem)

/-- `E` is CM, as a totally complex abelian field (`IsCMField.of_isAbelianGalois`). -/
instance : IsCMField S.E := inferInstance

/-! ## The CM type -/

/-- A fixed embedding `ψ₀ : ℚ(ζ_N) → ℂ`; its restriction to `E` is the `φ₀` of the CM type. -/
noncomputable def ψ₀ : S.M →+* ℂ := Classical.choice inferInstance

/-- `σ_g ∈ Gal(ℚ(ζ_N)/ℚ)`, a lift of `g ∈ G` through the Artin map. -/
noncomputable def galLift (g : G S.A) : Gal(S.M/ℚ) := S.autEquiv.symm (Function.surjInv S.artin_surjective g)

/-- **The CM type** `τ(s, t) = φ₀ ∘ σ_{(1, s, t)}` on `E`, in Lemma B's coordinates `Φ = {1} × Φ ⊂ G`. -/
noncomputable def τ (ρ : Φ S.A) : S.E →+* ℂ :=
  S.ψ₀.comp (((S.galLift (1, ρ) : S.M ≃ₐ[ℚ] S.M) : S.M →+* S.M).comp (algebraMap S.E S.M))

/-- `v_E = |d_E|^{1/[E:ℚ]}/2`, the height normalisation of the main terms (L7.3). -/
noncomputable def vE : ℝ := |(discr S.E : ℝ)| ^ (Module.finrank ℚ S.E : ℝ)⁻¹ / 2

/-! ## Sanity checks -/

/-- `f = |Φ| = 2|A|`. -/
theorem f_eq : S.f = 2 * Fintype.card S.A := by simp [f]

/-- `|Gal(E/ℚ)| = [E : ℚ] = |G| = 4|A|`: the index of `H` is `|G|`, as the Artin map is onto. -/
theorem card_gal : Nat.card Gal(S.E/ℚ) = 4 * Fintype.card S.A := by
  have h1 := Module.finrank_mul_finrank ℚ S.E S.M
  rw [IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank ℚ S.M, ← S.H.card_mul_index,
    H, Subgroup.index_comap_of_surjective (f := S.autEquiv.toMonoidHom) _ S.autEquiv.surjective, Subgroup.index_ker,
    MonoidHom.range_eq_top_of_surjective _ S.artin_surjective, Subgroup.card_top] at h1
  rw [IsGalois.card_aut_eq_finrank, Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans (mul_comm _ _))]
  simp [Nat.card_eq_fintype_card]
  ring

/-- `τ` does not depend on the lift: `τ(ρ) = φ₀ ∘ σ` for every `σ` over `(1, ρ)`, as `H` fixes `E`. -/
theorem τ_eq {ρ : Φ S.A} {σ : Gal(S.M/ℚ)} (hσ : S.artin (S.autEquiv σ) = (1, ρ)) (x : S.E) :
    S.τ ρ x = S.ψ₀ (σ x) := by
  have hmem : (S.galLift (1, ρ))⁻¹ * σ ∈ S.H := by
    simp [H, galLift, hσ, Function.surjInv_eq]
  rw [← IntermediateField.fixingSubgroup_fixedField S.H, IntermediateField.mem_fixingSubgroup_iff] at hmem
  have := congrArg (S.galLift (1, ρ)) (hmem x x.2)
  simp only [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] at this
  simp [τ, this]

end ZetaBalance.Setting
