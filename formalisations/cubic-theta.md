# Kubota's cubic theta function and Patterson's coefficients

**Lean:** `Eis.kubotaTheta` (`lib/core/KubotaThetaProof.lean`) proves the display `Eis.KubotaTheta`
(`lib/core/KubotaTheta.lean`):

```lean
def KubotaTheta : Prop :=
  ∃ (θ : ℂ → ℝ → ℂ) (Kc : ℝ) (C c₀ cP cM : ℂ) (τ tP tM : 𝓞 K → ℂ), C ≠ 0 ∧
    ThetaSupp Kc τ ∧ ThetaSupp Kc tP ∧ ThetaSupp Kc tM ∧ (∀ m, τ m ≠ 0 → δ3 ∣ m) ∧
    (∀ z v, 0 < v → θ z v = thSer c₀ τ z v) ∧
    (∀ z v, 0 < v → atG θ (gamPlus.map σO) z v = thSer cP tP z v) ∧
    (∀ z v, 0 < v → atG θ (gamMinus.map σO) z v = thSer cM tM z v) ∧
    (∀ γ : Matrix (Fin 2) (Fin 2) ℤ, γ.det = 1 → ∀ z v, 0 < v →
      atG θ (γ.map (Int.castRingHom ℂ)) z v = θ z v) ∧
    (∀ γ : Matrix (Fin 2) (Fin 2) (𝓞 K), γ.det = 1 → ModThree γ → ∀ z v, 0 < v →
      atG θ (γ.map σO) z v = kub γ * θ z v) ∧
    (∀ n b : 𝓞 K, Primary n → Primary b → Squarefree (span {n}) →
      (absNorm (span {n * b})).Coprime 6 →
      τ (δ3 * n * b ^ 3) = C * (Real.sqrt (absNorm (span {b})) : ℂ) *
          sym6 δ3 (span {n}) ^ 2 * conj (gamI 2 (span {n})) ∧
      τ (-(δ3 * n * b ^ 3)) = C * (Real.sqrt (absNorm (span {b})) : ℂ) *
          sym6 δ3 (span {n}) ^ 2 * conj (gamI 2 (span {n})))
```

Here `K = ℚ(ω)`, `𝓞 K = ℤ[ω]`, `δ₃ = 1 + 2ω` is a square root of `−3`, and a point `z + vj` of upper half-space
`ℍ³` is written `(z, v)` with `z ∈ ℂ`, `v > 0`. In words, there is a function `θ` on `ℍ³` such that:

- **at `∞`** it is a theta-type series (`thSer`),
  `θ(z, v) = c₀v^{2/3} + Σ_{m∈ℤ[ω]} τ(m)·v·K_{1/3}(4π|m|v/9)·ĕ(mz/9)` with `ĕ(z) = exp(2πi(z + z̄))`, and its
  coefficients `τ(m)` vanish unless `δ₃ ∣ m`;
- **at the cusps** `γ_± = (1, 0; ω^{±1}, 1)` (`gamPlus`, `gamMinus`) its expansions are theta-type series too;
- **all three coefficient families** satisfy the support and size condition `ThetaSupp`: a coefficient `d(m)` is `0`
  unless `m = uλ^k n b³` with `u` a unit, `λ` the prime above `3`, `n` squarefree and `N(n)`, `N(b)` prime to `3`,
  and then `|d(m)| ≤ K·3^{k/6}N(b)^{1/2}`;
- **it is invariant under `SL_2(ℤ)`**, and automorphic on `Γ_1(3) = {γ ∈ SL_2(ℤ[ω]) : γ ≡ I (mod 3)}` with Kubota's
  character `κ(γ) = (c/a)₃` (`kub`);
- **Patterson's coefficients**: for primary `n, b` with `n` squarefree and `N(nb)` prime to `6`,
  `τ(±δ₃nb³) = C·N(b)^{1/2}·(δ₃/n)₆²·conj γ₂(n)` for one constant `C ≠ 0`. Here `(·/n)₆` is the sextic residue symbol,
  and `γ₂(n) = Σ_{x mod n} (x/n)₆²ψ_n(x)/|n|` is the normalised cubic Gauss sum (`gamI 2`).

The constant terms `c₀`, `cP` and `cM` are left free. The theorem is in the proof of `Linnik22000E.linnik_22000e`,
whose axioms are `propext`, `Classical.choice` and `Quot.sound` (`lib/check/Check.lean`), so it depends on those only.

## Source

- T. Kubota, *On Automorphic Functions and the Reciprocity Law in a Number Field*, Lectures in Mathematics, Kyoto
  University, No. 2 (Kinokuniya, Tokyo, 1969). Kubota's cubic theta function is the residue of a cubic metaplectic
  Eisenstein series on `ℍ³`, and `κ` is his character.
- S. J. Patterson, "A cubic analogue of the theta series", J. Reine Angew. Math. 296 (1977), 125–161, and its part
  II, ibid. 217–220. Patterson computed the theta function's Fourier coefficients and extended `κ` to
  `Γ_2 = SL_2(ℤ)Γ_1(3)`.
- A. Dunn and M. Radziwiłł, "Bias in cubic Gauss sums: Patterson's conjecture", Ann. of Math. (2) 200 (2024),
  967–1057 (arXiv:2109.07463). Their §5 states the theory in the form the display follows: the groups, Kubota's
  character (their (5.4) and (5.5)), the cusps, `θ` at the cusps and Patterson's coefficients (their (5.7) and (5.8)).
  Their Appendix gives the coefficients `d_j` of Patterson's Table III, with the action of the generators.

Dunn and Radziwiłł's paper was read from its LaTeX source: §5.1–5.3 and the Appendix. The OpenAI companion preprint
([openai-half-plane.md](openai-half-plane.md)), whose Appendix A.2 uses the theorem in this form, was read too. Its
words: "Let θ(z,v) be Kubota's cubic theta function on hyperbolic three-space (z ∈ ℂ, v ∈ ℝ_{>0}), obtained as a
residue of a cubic metaplectic Eisenstein series [Kub69, Pat77]", and "The proof adapts the theta-transformation
method of Dunn and Radziwiłł [§5 and Appendix A], which extends Patterson [Pat77] and Yoshimoto [Yos87]."

Kubota's lectures and Patterson's papers were not read. The library's proof was not transcribed from any source: it
constructs `θ` itself, by the steps below. Nothing in this library claims the theta function, its coefficients or
the theorem as its own.

## What the formalisation here is

- **The space and the groups.** Upper half-space and the action of `SL_2(ℂ)` (`UpperHalfSpace`; Dunn and Radziwiłł's
  §5.1, after Elstrodt, Grunewald and Mennicke), the invariant measure `dz dv/v³` (`KubotaMeasure`), reduction theory
  for `SL_2(ℤ[ω])` with a Siegel set and finite volume (`KubotaSiegel`), and unfolding (`KubotaUnfold`).
- **Kubota's character** (`KubotaCharacter`). `κ` is a homomorphism on `Γ_1(3)` (`Eis.kub_mul`), trivial on
  `SL_2(ℤ) ∩ Γ_1(3)` (`Eis.kub_int`), and extends to a homomorphism on `Γ_2` (`Eis.kub2_mul`). The proofs use cubic
  reciprocity and its supplementary laws.
- **The Eisenstein series** (`KubotaEisenstein`, `KubotaGrowth`, `KubotaConstTerm`, `KubotaCuspSums`, `KubotaPhi`,
  `KubotaPhiPole`). The Eisenstein series of `Γ_1(3)` with the character `κ` converges for `Re s > 2`
  (`Eis.summable_eisTerm`) and is automorphic (`Eis.eis1_slAct`). The coefficient `φ(s)` of `v^{2−s}` in its constant
  term at `∞` is found in closed form, with a pole at `s = 4/3` and residue
  `π/(6√3)·L(1, χ₋₃)/(ζ(2)L(2, χ₋₃)) ≠ 0` (`Eis.tendsto_phiC_residue`, `Eis.phiRes_ne_zero`).
- **The residue `θ`** (`KubotaBall`, `HilbertResolvent`, `KubotaBallOp`, `KubotaEisTrunc`, `KubotaGHolo`,
  `KubotaResidue`, `KubotaThetaPair`). A self-adjoint operator of averages over hyperbolic balls has `v^s` among its
  eigenfunctions. From a truncated Eisenstein series `g_s` and the operator's resolvent the library builds an `L²`
  function `ũ_s` attached to the Eisenstein series. `θ` is the limit of `(s − 4/3)ũ_s` along `s = 4/3 + iε`
  (`Eis.tendsto_uL_thetaL`), and `θ ≠ 0` (`Eis.thetaL_ne_zero`, `KubotaThetaPair`).
- **The Fourier coefficients and the constant term** (`KubotaEisFourier`, `KubotaPoincare`, `KubotaPmPair`,
  `KubotaPmTheta`, `KubotaThetaCoef`, `KubotaThetaConst`, `KubotaThetaSeries`, `KubotaThetaEq`). They are identified by
  pairing `θ` with Poincaré series, and `θ` equals its Fourier series almost everywhere. The integral of `θ` over a
  period parallelogram is `(9√3/2)·Res φ·v^{2/3}` for almost every `v` (`KubotaThetaConst`).
- **Invariance under `SL_2(ℤ)`** (`KubotaCTPrinciple`, `KubotaCTCover`, `KubotaCuspZero`, `KubotaCuspZeroPhi`,
  `KubotaThetaZero`, `KubotaThetaInv`): by a constant-term principle, `θ ∘ S = θ` and `θ ∘ T = θ` almost everywhere
  (`Eis.thetaF_sS_ae`), and `θ`'s Fourier series is automorphic on `Γ_2` with the extension of Kubota's character
  (`Eis.isAut_thS_Gam2`).
- **Patterson's coefficients** (`KubotaCubeSum`, `KubotaCubeDecomp`, `KubotaCubeCover`, `KubotaCubeEigen`,
  `KubotaCubeCoef`, `KubotaCoefResidue`, `KubotaSmFactor`, `KubotaLocTable`, `KubotaDirSplit`, `KubotaCoefPrime`,
  `KubotaCoefSqfree`, `KubotaCoefUnit`, `KubotaCoefScalar`, `KubotaCoefSupp`, `KubotaLamCube`). A cube eigenrelation
  at each primary prime, `N(p)^{−3}Σ_{q mod p³} θ ∘ M_q = N(p)^{−1}θ` (`Eis.cubeDiff_ae_eq_zero`), and the
  coefficients as residues of Dirichlet series of Kubota sums give the coefficients at `δ₃nb³`
  (`Eis.exists_display_coef`, with `C = τ(δ₃)`) and the support and size condition (`Eis.thetaSupp_tauTh`).
- **The cusps `γ_±`** (`KubotaCuspTrans`, `KubotaCuspPoincare`, `KubotaCuspCoef`, `KubotaCuspIdent`,
  `KubotaCuspTheta`, `KubotaCuspSeries`): `θ`'s expansions there, with constant terms `0` (`Eis.cusp_clauses`).

## Differences from the source

- **The form used, not the whole theory.** The display has what the companion preprint's Appendix A.2 needs.
  Patterson's coefficients are given only at `±δ₃nb³` with `n` squarefree and `N(nb)` prime to `6`. Elsewhere only
  the support and size condition is stated. The constant `C` is shown to be nonzero, not computed, and the constant
  terms are left free.
- **An existence statement.** The display asserts a function with these properties, not an identity with Kubota's or
  Patterson's normalisation of `θ`. The library's `θ` is, like Kubota's, a residue at `s = 4/3` of the Eisenstein
  series of `Γ_1(3)` with `κ`. The library reaches it by its own spectral argument (above), not by Kubota's or
  Patterson's proofs, which were not read.
- **The indexing.** The Fourier index is `m = λ⁴μ = 9μ` for Dunn and Radziwiłł's index `μ ∈ λ^{−4}𝒪`, and the cusps
  `γ_±` are their `γ_10` and `γ_19`.

## Where the Linnik paper uses it

Through the zero-free half-plane ([openai-half-plane.md](openai-half-plane.md)). `Eis.thetaRows_of_kubota`
(`lib/core/KubotaRows.lean`) derives from the display the companion preprint's theta transformation for the rows
(`Eis.ThetaRows`; its Section 6 and Appendix A.2). That transformation is the companion preprint's own, adapting Dunn
and Radziwiłł's method. `Eis.ne_zero_of_kubotaTheta` turns it into the half-plane for `ζ` and `L(s, χ₋₃)`.
