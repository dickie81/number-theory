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
```

`chi5` is the Dirichlet character mod 5 with `χ(2) = i`, and `dhL χ = (1 + ε_{χ⁻¹})L(s, χ) + (1 + ε_χ)L(s, χ⁻¹)`, with
`ε_χ` the root number of `χ` (`lib/dh/DavenportHeilbronn.lean`). In words: `dh` is not identically zero
(`PsiOmega.dh_ne_zero`), its completion satisfies `Λ(1 − s) = Λ(s)` (`PsiOmega.dh_functional_equation`), as `ζ`'s does,
and yet it has a zero off the critical line, and four in the boxes above, with real parts near `0.808`, `0.651`, `0.574`
and `0.724` and ordinates near `85.70`, `114.16`, `166.48` and `176.70`.

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
inputs proved in rationals. The first gives a zero pair `ρ`, `1 − ρ` whose Bohr vectors lie strictly inside and outside
the unit sphere in every dimension (`PsiOmega.dh_zero_pair_off_sphere`, `DHBohrSphere.lean`): a frame in which the
critical line is the sphere cannot place the zeros on it by an argument that `dh` also satisfies.

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
