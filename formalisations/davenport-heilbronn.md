# The Davenport–Heilbronn function and its zeros off the critical line

**Lean:** the layer `lib/dh`, whose final theorems `lib/check/CheckDH.lean` prints (`scripts/check_axioms.py --dh`):

```lean
def PsiOmega.dh : ℂ → ℂ := dhL chi5

theorem PsiOmega.dh_offline_zero : ∃ s : ℂ, dh s = 0 ∧ 0 < s.re ∧ s.re ≠ 1 / 2

theorem PsiOmega.Locate.dh_zeros_located_four_box :
    (∃ ρ : ℂ, dh ρ = 0 ∧ 1597 / 2000 < ρ.re ∧ ρ.re < 1637 / 2000 ∧
      856893 / 10000 < ρ.im ∧ ρ.im < 857093 / 10000) ∧
    (∃ ρ : ℂ, dh ρ = 0 ∧ 64583 / 100000 < ρ.re ∧ ρ.re < 65583 / 100000 ∧
      5707917 / 50000 < ρ.im ∧ ρ.im < 5708417 / 50000) ∧
    (∃ ρ : ℂ, dh ρ = 0 ∧ 14309 / 25000 < ρ.re ∧ ρ.re < 14409 / 25000 ∧
      16647731 / 100000 < ρ.im ∧ ρ.im < 16648131 / 100000) ∧
    (∃ ρ : ℂ, dh ρ = 0 ∧ 107639 / 150000 < ρ.re ∧ ρ.re < 109639 / 150000 ∧
      26504369 / 150000 < ρ.im ∧ ρ.im < 26506369 / 150000)

theorem PsiOmega.Locate.Z5.dh_zero_located_five :
    ∃ ρ : ℂ, dh ρ = 0 ∧ 916801 / 1000000 < ρ.re ∧ ρ.re < 920401 / 1000000 ∧
      2441547685 / 100000 < ρ.im ∧ ρ.im < 2441548045 / 100000

theorem PsiOmega.Locate.Z5.dh_zero_re_gt : ∃ ρ : ℂ, dh ρ = 0 ∧ 11 / 12 < ρ.re

def PsiOmega.dh2 : ℂ → ℂ := dh2L chi5

theorem PsiOmega.Locate.Sec.dh2_zero_located :
    ∃ ρ : ℂ, dh2 ρ = 0 ∧ 23746444 / 10000000 < ρ.re ∧ ρ.re < 23748444 / 10000000 ∧
      16498707285 / 10000000 < ρ.im ∧ ρ.im < 16498709285 / 10000000

theorem PsiOmega.Locate.Sec.dh2_zero_re_gt_one : ∃ ρ : ℂ, dh2 ρ = 0 ∧ dh2Lam chi5 ρ = 0 ∧ 1 < ρ.re
```

`chi5` is the Dirichlet character mod 5 with `χ(2) = i`, and `dhL χ = (1 + ε_{χ⁻¹})L(s, χ) + (1 + ε_χ)L(s, χ⁻¹)`, with
`ε_χ` the root number of `χ` (`lib/dh/DavenportHeilbronn.lean`). In words: `dh` is not identically zero
(`PsiOmega.dh_ne_zero`), its completion satisfies `Λ(1 − s) = Λ(s)` (`PsiOmega.dh_functional_equation`), as `ζ`'s does,
and yet it has a zero off the critical line, and four in the boxes above, with real parts near `0.808`, `0.651`, `0.574`
and `0.724` and ordinates near `85.70`, `114.16`, `166.48` and `176.70`. A fifth, near `0.9186 + 24415.4787i`, has
real part above `11/12`: the half-plane `Re s > 11/12`, where no Dirichlet `L`-function has a zero
([openai-half-plane.md](openai-half-plane.md)), holds a zero of `dh`. So that theorem cannot follow from what `dh`
shares with the `L`-functions, the functional equation among them; it has to use what `dh` lacks.

`dh2L χ = (1 − ε_{χ⁻¹})L(s, χ) + (1 − ε_χ)L(s, χ⁻¹)` is the combination with the other sign, and `dh2` the second
Davenport–Heilbronn function (`lib/dh/DHSecond.lean`). Its completion satisfies `Λ₂(1 − s) = −Λ₂(s)`
(`PsiOmega.dh2_functional_equation`), and it has a zero near `2.3747 + 1649.8708i`: in the half-plane `Re s > 1`,
where its Dirichlet series converges absolutely and no Dirichlet `L`-function has a zero.

## Source

H. Davenport and H. Heilbronn, *On the zeros of certain Dirichlet series*, J. London Math. Soc. 11 (1936), 181–185 and
307–312; the function as E. C. Titchmarsh gives it, *The Theory of the Riemann Zeta-Function*, 2nd ed., revised by D. R.
Heath-Brown (1986), §10.25. R. Spira computed zeros of the function on and off the line, *Some zeros of the Titchmarsh
counterexample*, Math. Comp. 63 (1994), 747–748.

## How the Lean statement differs

`dh` is the function of §10.25 up to a positive real factor: with `ε_χ = e^{iθ}`,
`dh = 4cos²(θ/2)·[((1 − iκ)/2)L(s, χ) + ((1 + iκ)/2)L(s, χ̄)]`, `κ = tan(θ/2)`. The Lean does not identify `κ` with the
closed form of §10.25, which is a numerical identity and is not needed. The zeros are proved, not computed: each box
comes with a certificate that the kernel checks, so the theorem settles that the function has zeros there.

## How it was done

**The function** (`DavenportHeilbronn.lean`): Mathlib's functional equation for Dirichlet `L`-functions, applied twice,
gives `ε_χ ε_{χ⁻¹} = 1`, and with it the functional equation of `dhL χ` for every primitive `χ ≠ 1`. The coefficients of
`−dh′/dh` are those of `−L′/L(s, χ₅)` except at the integers whose prime factors are all `≡ ±2 (mod 5)`
(`PsiOmega.cDH_chi5_eq_of_dvd`, `DHInert.lean`). The zeros of `dh` are symmetric under conjugation
(`PsiOmega.dh_conj_zero`); the logarithmic derivative of its `Ξ` is the sum over its zeros
(`PsiOmega.hasSum_logDeriv_dh`, `DHZeros.lean`, from `L(½, χ₅) ≠ 0`, proved without numerics); `dh` is close to its
Euler–Maclaurin approximant (`PsiOmega.norm_dh_sub_EM_le`, `DHHurwitzEM.lean`); and `dh(σ)/a(1) ≥ 1 − 2^{−σ}` for
`σ > 0` (`PsiOmega.dh_div_a1_real_ge`).

**A zero off the line** (`DHExplicit.lean`, `DHCertificate.lean`): Weil's explicit formula for `dh` makes its Weil form
`Q_dh(g)` nonnegative for every admissible test function `g` if all the zeros with `Re s > 0` lie on the line, so a
negative value certifies an off-line zero (`PsiOmega.exists_offline_dh_of_neg`). The certificate is
`Q_dh(packet 12/5 169/2) < 0`: its prime side, a sum over `2 ≤ n ≤ 121`, is bounded term by term (`DHTerms.lean`), and
its archimedean term in closed form (`DHArch.lean`), which gives `PsiOmega.dh_offline_zero`. The zero is not real
(`PsiOmega.dh_offline_nonreal_zero`, `PsiOmega.dh_offcross_zero`), and by the functional equation it may be taken in
`½ < Re s ≤ 2` (`PsiOmega.dh_offline_zero_right`). So GRH fails for `dh` (`PsiOmega.not_GRH_dh`); RH for `dh` and its
cross form, which also allows real zeros, are equivalent (`PsiOmega.dhRH_iff_cross`), and both fail.

**Four zeros located** (`DHLocateSkeleton.lean`, `DHLocate*.lean`, `DHLocateFour.lean`): for each box, the minimum
modulus principle against the Euler–Maclaurin approximant `dhEM 20 12`, linearised at the box's centre with a bound for
its second derivative, gives a zero within `1/100`, `1/200`, `1/500` and `1/150` of the four centres, with the numerical
inputs proved in rationals, a lemma for each term. The first gives a zero pair `ρ`, `1 − ρ` whose Bohr vectors lie strictly inside and outside
the unit sphere in every dimension (`PsiOmega.dh_zero_pair_off_sphere`, `DHBohrSphere.lean`): a frame in which the
critical line is the sphere cannot place the zeros on it by an argument that `dh` also satisfies.

**A fifth zero, right of `11/12`** (`DHBallDefs.lean`, `DHBall.lean`, `DHLocate5States.lean`, `DHLocate5Cert0.lean`,
…, `DHLocate5Cert5.lean`, `DHLocate5.lean`): the same certificate (`PsiOmega.Locate.dh_zero_near_of_fEMG`, which is
stated for any centre) at `c = 918601/1000000 + (2441547865/100000)i`, with radius `18/10000` and the approximant
`dhEM 6000 12`. At height `24415` the approximant's Dirichlet polynomial runs over `n < 30000`, `24000` terms, too
many to bound one lemma at a time, so the kernel computes them:

- `DHBall.run` is integer arithmetic on balls (a centre and a radius over `2^80`), at a centre `c` that it takes as
  an argument (`DHBall.Ctr`; here `DHBall.ctr5`): `log (n + 1) − log n` from the series of `−log(1 − 1/(n + 1))`;
  `t·log n` reduced modulo `2π` with Mathlib's twenty decimals of `π`; `n^{-c}` as the Taylor polynomial of `exp` of
  degree `13` at the exponent over `16`, squared four times; and the running sums of `n^{-c}` and `log n · n^{-c}` by
  residue class mod 5, with an upper bound for `Σ log² n · |n^{-c}|`.
- `DHBall.inv_run` proves that the balls hold the sums (`Complex.exp_bound`, `Real.abs_log_sub_add_sum_range_le`).
- `DHBall.run_0`, …, `DHBall.run_5` are the computation, a thousand blocks of five integers each, fifty blocks to a
  kernel check (`decide +kernel`); `scripts/gen_dh_ball_cert.py` writes the intermediate states, and the kernel
  recomputes every one. Each of the six files took about `105` seconds of one core here, and `1.6` GB.
- `DHLocate5.lean` reads off the three numbers at the centre: `‖fEM(c)‖ ≤ 42/100000` (the Dirichlet polynomial is
  below `11/100000` there and the tail below `31/100000`), `‖fEM′(c)‖ ≥ 196/100`, and `‖fEM″‖ ≤ 4642/10` on the
  ball; the Euler–Maclaurin error is below `1/100000`. The margin `2(p₀ + e₀) < a₀r − m₂r²` is `0.00086 < 0.00202`.

The zero was found by `scripts/dh_right_scan.py`: the argument of `f` along `Re s = 11/12`, by the approximate
functional equation, then Newton's method on the exact function. It gives `0.9186013197 + 24415.4786514i`, the first
of five zeros with `Re s > 11/12` below height `200000` (the others near `49688.34`, `74189.64`, `107847.40` and
`196872.11`, with real parts `0.9371`, `0.9183`, `0.9358` and `0.9248`); those four are numerical, not certified.
Zeros with `Re s > 1`, in the half-plane of absolute convergence, are located numerically and not certified:
`scripts/dh_abs_zero.py` finds fifteen by lattice reduction, the lowest `1.0085585829 + 2528618752780.585033i`
([research-opportunities.md](../docs/research-opportunities.md), §8.5, with what a certificate would need).

**The second function, and a zero of it right of `1`** (`DHSecond.lean`, `DHSecondStates.lean`,
`DHSecondCert0.lean`, `DHSecondZero.lean`). For the same character, `dh2 = (1 − ε')L(s, χ₅) + (1 − ε)L(s, χ₅⁻¹)`.

- **The function.** Its completion has the functional equation with the sign `−`, for every primitive `χ ≠ 1`
  (`PsiOmega.dh2Lam_one_sub`), and its zeros in `Re s > 0` are those of the completion
  (`PsiOmega.dh2_eq_zero_iff`). Its Dirichlet coefficients are `a(1)·κ·(0, κ, −1, 1, −κ)` on the residues
  `0, …, 4` mod `5` (`PsiOmega.bDH_chi5_eq_mul`), where those of `dh` are `a(1)·(0, 1, κ, −κ, −1)`: the identity
  behind it is `κ·Im ε = 1 − Re ε` (`PsiOmega.kappa_mul_im_eps`), which is `|ε| = 1`. Divided by `a(1)κ²` the
  coefficients are `1, τ₋, −τ₋, −1` with `τ₋ = −1/κ`: Bombieri and Ghosh's `f(s, τ₋)`. The Lean does not state that
  normalisation.
- **The certificate.** The minimum-modulus instrument of the located zeros (`PsiOmega.Locate.exists_zero_of_bounds`),
  at `c = 23747444/10000000 + (16498708285/10000000)i` with radius `1/10000`. At real part `2.37` no
  Euler–Maclaurin tail is needed: the approximant is the Dirichlet polynomial over `n ≤ 5000`
  (`PsiOmega.Locate.secD`), and the rest of the series is at most `‖a(1)‖κ·5000^{−37/100}/5000` on `Re s ≥ 237/100`
  (`PsiOmega.Locate.norm_dh2_sub_le`, from `Σ_{n > N} n⁻² ≤ 1/N`).
- **The kernel's part.** `DHBall.run` at the centre `DHBall.Sec.ctr`, with five squarings where the fifth zero has
  four, since `Re c·log n` is larger: a thousand blocks, one file, about `120` seconds.
- **The numbers**, in units of `‖a(1)‖κ`: the polynomial at `c` is below `10⁻⁷`, its derivative there is at least
  `24/100`, its second derivative on the ball at most `1`, and the tail at most `43/5000000`. The margin
  `2(p₀ + e₀) < a₀r − m₂r²` is `1.74·10⁻⁵ < 2.399·10⁻⁵`.

The zero is the one of largest real part below height `10000` in Bombieri and Ghosh's computations (their §9),
`2.37474435 + 1649.8708285i`; refined here to `2.3747443578 + 1649.8708285004i` before it was certified. The
kernel's part is one file, where the fifth zero has six. For `dh` itself the zeros right of `1` start near height
`2.5·10¹²` and are not certified.

**On the critical line** (`DHChannels.lean`): `L(s, χ₅)L(1 − s, χ₅) = ε²L(s, χ₅⁻¹)L(1 − s, χ₅⁻¹)`
(`PsiOmega.chi5_channel_fe`), the phase lock (`PsiOmega.chi5_phase_lock`), the reality of the channel ratio on the line
(`PsiOmega.chi5_channel_ratio_real`) and its reflection (`PsiOmega.chi5_channel_ratio`), and the zero condition on the
line as one real equation (`PsiOmega.dh_line_zero_iff`).

**The Weil form of `dh`** (`DHForm.lean`, `DHNegIndex.lean`, `DHJoins.lean`, `DHTwin.lean`, `ChiFirstFailure.lean`): its
ground energy `λ_dh` is negative (`PsiOmega.exists_lamDH_neg`), and from `12/5` on; `Q_dh` is negative definite on a
plane of the two packet certificates (`PsiOmega.QDHu_packet_plane_neg`), on a space of dimension `4` from the four
located zeros (`DHNegIndex.negIndex_ge_four`) and on one of dimension `5` with probes of either parity
(`DHNegIndex.negIndex_ge_five`); the dimension of such a space is at most the number of quadruples of off-line zeros
(`PsiOmega.finrank_le_quadruples_dh`); `λ_dh` fails at an exponential rate (`PsiOmega.lamDH_fails_exponentially`,
`PsiOmega.not_lamDH_subexp`), is continuous (`PsiOmega.continuousOn_lamDH`), and has a first failure at some `a₁ ≤ 12/5`
(`PsiOmega.first_failureDH`).

## The columns

The library proves criteria for RH, statements that some hypothesis on `ζ` implies RH. The layer restates each with `dh`
in place of `ζ`, its **dh column**. RH fails for `dh`, so the hypotheses must fail for `dh` too, and the column proves
that they do: a proof of any of them for `ζ` must use what `dh` lacks, such as the Euler product. The dh columns: Weil's
criterion (`PsiOmega.weil_criterion_dh`, `PsiOmega.QDHu_nonneg_of_DHRHcross`), Hypothesis D (`PsiOmega.not_D_dh`), the
twin form (`PsiOmega.not_twins_nonneg_dh`, `PsiOmega.not_twins_subexp_dh`), the kernel on the positive rationals
(`PsiOmega.not_posDef_dh`), its realizations by similitudes (`PsiOmega.not_realization_dh`) and the kernel with
Hadamard's weights (`PsiOmega.not_posDefH_dh`), the odd probes (`PsiOmega.not_odd_lower_dh`,
`PsiOmega.not_lamODH_lower`), the ground states, with Theorem D, the polarisation and Euler–Lagrange
(`PsiOmega.theoremDDH`, `PsiOmega.bilDH_polar`, `PsiOmega.euler_lagrangeDH`, `PsiOmega.dhRHcross_of_eventually_simple`,
`PsiOmega.dhRHcross_of_hypConv_top`, `PsiOmega.not_simple_hypConvDH`, `PsiOmega.not_hypConvDH_top`), and the rest of the
roadmap (`DHColumnRest.lean`: `PsiOmega.not_ground_states_dh`, `PsiOmega.not_groundStates_dodging_dh`,
`PsiOmega.not_D_and_realRooted_hadamard`, `PsiOmega.not_hypConvStripDH_top`, `PsiOmega.not_XiDH_params`,
`PsiOmega.not_dodging_hadamard`, `PsiOmega.not_pairing_and_realRooted`).

The **χ column** restates the same criteria for the `L`-function of a Dirichlet character `χ` (`ChiGround.lean`,
`ChiFirstFailure.lean`, `DHJoins.lean`): the ground states and Theorem D (`PsiOmega.exists_groundStateC`,
`PsiOmega.euler_lagrangeC_mem`, `PsiOmega.theoremDC`), GRH for `χ` from eventually simple ground states
(`PsiOmega.grh_of_eventually_simpleC`) and for `χ₋₃`, `χ₋₄`, `χ₋₇` and `χ₋₈` from the top-of-chain ground states
(`PsiOmega.grh_chi3_of_hypConvC_top`, `PsiOmega.grh_chi4_of_hypConvC_top`, `PsiOmega.grh_chi7_of_hypConvC_top`,
`PsiOmega.grh_chi8_of_hypConvC_top`); the ground energy `λ_χ`, continuous (`PsiOmega.continuousOn_lamC`), at least
`log 2 − ¼` at small support (`PsiOmega.lamC_pos_small`), with a first failure if GRH fails for `χ`, for a primitive
quadratic `χ ≠ 1` with `L(½, χ) ≠ 0` and no real zero in `(0, 1)` (`PsiOmega.first_failureC`); and GRH for `χ` if and
only if `λ_χ ≥ 0` (`PsiOmega.lamC_nonneg_of_GRH`, `PsiOmega.grh_iff_lamC_eventually_nonneg`,
`PsiOmega.grh_iff_lamC_nonneg_chi3`, `PsiOmega.grh_iff_lamC_nonneg_chi4`, `PsiOmega.grh_iff_lamC_nonneg_chi7`,
`PsiOmega.grh_iff_lamC_nonneg_chi8`).
