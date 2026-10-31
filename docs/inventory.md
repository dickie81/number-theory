# Inventory of the library's results

Written by `scripts/inventory.py` from the sources; do not edit it by hand. `python3 scripts/inventory.py`
rewrites it, and CI checks that it is current (`--check`).

`lib/check/CheckAll.lean`, `lib/check/CheckZeta23.lean`, `lib/check/CheckDH.lean` and
`lib/check/Check.lean` print the axioms of 967 theorems: the library's final results (those of the
zeta23 layer in `CheckZeta23`, which `CheckAll` cannot import, and those of `lib/dh` in `CheckDH`) and the
papers' theorems, of which there are 146, marked *paper*. Each line gives a theorem's name and the
headline of its docstring, and links the note of `formalisations/` that names it, if one does.

| Layer | Modules with results | Results |
|---|---|---|
| `lib/core` | 85 | 199 |
| `lib/pnt` | 210 | 666 |
| `lib/dh` | 20 | 68 |
| `lib/zeta23` | 8 | 34 |

## The results of `CheckAll`, `CheckZeta23`, `CheckDH` and `Check`

### `lib/core`

#### `AngularFamily`: RH is the radial member of the ball's angular grinding family

- `AngularFamily.member_zero_eq`: The radial member is `ζ · L(χ₄)` ([note](../formalisations/weil-positivity.md))
- `AngularFamily.rh_of_member_zero`: RH is in the family ([note](../formalisations/weil-positivity.md))

#### `AngularResidue`: The residue of the radial member and `L(1, χ₋₄) = π/4`

- `AngularResidue.residue_angular`: The residue of the radial member
- `AngularResidue.LFunction_chi4_one`: `L(1, χ₋₄) = π/4`

#### `BallTower`: The ball tower from integers and primes (formalised)

- `BallTower.ballVol_lt_five`: The ball volume is largest in dimension 5
- `BallTower.sphereArea_lt_seven`: The sphere area is largest in dimension 7 (the sphere `S⁶`)
- `BallTower.completing_factor_unique`: Uniqueness of the completing factor

#### `BohrJoins`: The geometric picture joined to the library

- `BohrJoins.shell_unconditional`: Unconditionally
- `BohrJoins.shell_radii_tendsto`: In the limit no shell short of the sphere constrains the radius
- `BohrJoins.zero_pair_of_not_RH`: If RH fails, some zero pair straddles the sphere
- `BohrJoins.completed_eq_sphereArea_bohr`: The ball tower and the Bohr lift in one identity

#### `BohrLandauCore`: For every w > 0, almost every zero lies within w of the critical line

- `BohrLandauCore.tendsto_NX_div_of_lower`: For every `w > 0`, almost every zero lies within `w` of the critical line

#### `BohrSphere`: The critical line is the unit sphere of the Bohr lift

- `BohrSphere.riemannHypothesis_iff_mem_sphere`: For every nonempty finite set of primes, RH says that every nontrivial zero lies on the unit sphere. ([note](../formalisations/weil-positivity.md))
- `BohrSphere.riemannHypothesis_iff_tendsto`: The same in the limit. ([note](../formalisations/weil-positivity.md))

#### `BohrTorus`: The Bohr torus: Vinogradov's orthogonality on the lift of a vertical line

- `BohrTorus.eq_zero_of_sum_log`: The logarithms of distinct primes are linearly independent over `ℤ`
- `BohrTorus.tendsto_mean_character`: The character means along the Bohr line
- `BohrTorus.sum_norm_sq_torus`: Every point of the torus has the same norm
- `BohrTorus.prod_eq_iff_map_eq`: The multiplicative system is rigid at every `ℓ`
- `BohrTorus.agree_not_rigid`: The additive system is not rigid beyond its dimension
- `BohrTorus.tendsto_mean_moment_rearrangements`: The limiting means of `|Σ_{p∈F} p^{−it}|^{2ℓ}` count the pairs of rearrangements

#### `CertInstances`: The certificate theorems as instances of the weighted certificate

- `CertInstances.weilQ_ge_of_cert'`: `PoleRelax.weilQ_ge_of_cert`, verbatim statement, as the `(K, N, T) = (2, 6, 3.033953)` instance.
- `CertInstances.weilQ_ge_of_certP'`: `PrimeRelax.weilQ_ge_of_certP`, verbatim statement, as the `(K, N, T) = (3, 60, 5.098076)` instance.

#### `Concave`: Pólya's theorem for even concave probes, with no representation hypothesis

- `WeilForm.realRooted_of_ae_concaveOn`: For probes ([note](../formalisations/weil-positivity.md))

#### `CrossCriteria`: GRH modulo real zeros, and the missing Props stated

- `CrossCriteria.rh_of_liouville_theta`: RH from one-sided Liouville bounds at every exponent `θ > ½` ([note](../formalisations/weil-positivity.md))

#### `CubeBall`: The infinite cube and the infinite ball are different objects

- `CubeBall.no_isometry_cube`: For every `n ≥ 2` the cube `[−1, 1]ⁿ` has no isometric copy in an inner product space
- `CubeBall.cube_distortion`: The cube against any ball, in dimension `n`
- `CubeBall.tendsto_ball_div_cube`: The Euclidean ball's share of the cube tends to `0`
- `CubeBall.norm_zCube_eq_one_iff`: The cube's surface is the line `Re s = 0`
- `CubeBall.line_inside_cube_not_in_ell2`: The critical line lies strictly inside the infinite cube, and outside `ℓ²`
- `CubeBall.vLp_mem_sphere_iff`: For every `ℓ^r` norm, `1 ≤ r ≤ ∞`, the cube's included, the normalised Bohr vector lies on the unit sphere if and only if `Re s = ½`
- `CubeBall.exists_unit_seq_tendsto_inner`: In infinite dimension every point of the closed unit ball is a weak limit of points of the unit sphere
- `CubeBall.tendsto_inner_ellUnit`: The norm is not weakly continuous
- `CubeBall.isEmpty_homeomorph_ball_hilbertCube`: So, with the norm topology, the infinite ball is not homeomorphic to the Hilbert cube

#### `Curvature`: Dodging D, and the curvature sum rule

- `WeilForm.rh_of_Xi_params`: RH from real parameters ([note](../formalisations/weil-positivity.md))
- `WeilForm.rh_of_dodging`: Dodging D and real-rootedness alone give RH ([note](../formalisations/weil-positivity.md))
- `WeilForm.ghat_curvature`: The curvature sum rule, real-rooted ([note](../formalisations/weil-positivity.md))
- `WeilForm.rh_of_dodging_final`: Roadmap item 1 ⇒ `RiemannHypothesis`, with dodging D alone ([note](../formalisations/weil-positivity.md))

#### `DegenerateFlat`: Degenerate ⇒ edge-flat (the converse direction, formal)

- `WeilForm.degenerate_flat_fourier`: The edge-flat structure, in Fourier form ([note](../formalisations/weil-positivity.md))
- `WeilForm.simple_iff_no_green_pair`: Formal equivalence (both directions) ([note](../formalisations/weil-positivity.md))

#### `DirichletCharHalfPlane`: Every Dirichlet character, `L(s, χ) ≠ 0` on `Re s > 11/12`

- `Eis.LFunction_ne_zero_of_re_gt`: The half-plane `Re s > 11/12` for every Dirichlet character *paper* ([note](../formalisations/openai-half-plane.md))

#### `EisensteinCubicRecip`: S1, part 3b: cubic reciprocity on `ℤ[ω]`

- `Eis.cub_recip`: Cubic reciprocity *paper*

#### `EisensteinIdealCount`: The ideals of `ℤ[ω]` of bounded norm

- `Eis.card_ofNorm_split`: Split
- `Eis.card_ofNorm_inert`: Inert
- `Eis.card_ofNorm_three`: Ramified

#### `EisensteinQuadRecip`: Quadratic and sextic reciprocity in `ℤ[ω]`

- `Eis.quad_recip`: Quadratic reciprocity in `ℤ[ω]`
- `Eis.quadR_neg_one`: The first supplementary law

#### `EisensteinQuadSieveFinal`: The quadratic large sieve, part 8: Theorem 2, `(E_1)` and Lemma 6.5

- `Eis.quadLargeSieve`: The companion paper's Lemma 6.5 is proved *paper* ([note](../formalisations/quadratic-large-sieve.md))

#### `EisensteinQuadSieveSep`: The quadratic large sieve, part 3: Heath-Brown's Lemmas 2 and 10

- `Eis.fBound_gcd`: Heath-Brown's Lemma 2
- `Eis.fBound_sep`: Heath-Brown's Lemma 10

#### `EulerGammaBinet`: Euler's constant to seven digits, from Binet's formula

- `Electron.eulerMascheroni_bounds`: Euler's constant to seven digits

#### `ExplicitBridge`: The explicit-formula bridge: `weilQ` is the zero side of Weil's explicit formula

- `WeilForm.weilQ_symbol`: The symbol form ([note](../formalisations/weil-positivity.md))

#### `FirstFailure`: The first positivity failure

- `WeilForm.first_failure`: The first positivity failure ([note](../formalisations/weil-positivity.md))

#### `FourierGap`: A certified lower bound on `Q₀` orthogonally to `w`, for every `0 < a ≤ 0.35`

- `WeilForm.groundState_unique_below_log2`: The ground state of `Q` is unique up to sign for every `a > 0` with `2a < log 2` ([note](../formalisations/weil-positivity.md))
- `WeilForm.groundState_unique_035`: The ground state of `Q` is unique up to sign for every `0 < a ≤ 0.35` ([note](../formalisations/weil-positivity.md))

#### `GapBound`: The pole-overlap gap bound

- `WeilForm.simple_of_pole_overlap`: Simplicity from a nonzero pole overlap ([note](../formalisations/weil-positivity.md))

#### `GapCriterion`: The energy-gap criterion and the pole-overlap identity (formal)

- `WeilForm.pole_overlap_identity`: The pole-overlap identity ([note](../formalisations/weil-positivity.md))
- `WeilForm.simpleGround_of_gap`: Energy gap ⇒ simplicity ([note](../formalisations/weil-positivity.md))

#### `GroundState`: Ground states of Weil's form: the structural facts

- `WeilForm.groundState_energy_ge`: The ground energy is bounded below ([note](../formalisations/weil-positivity.md))
- `WeilForm.rh_of_groundStates_dodging`: Roadmap item 1 ⇒ `RiemannHypothesis`, for the ground states of Weil's form ([note](../formalisations/weil-positivity.md))

#### `GroundStateExists`: Existence of the ground state, stage 3: the minimiser

- `WeilForm.exists_groundStates`: Ground states at every support of a sequence `a_n > 0` ([note](../formalisations/weil-positivity.md))

#### `HadamardApply`: Hadamard's factorisation for even functions, applied to `ĝ` and `Ξ`

- `WeilForm.rh_of_D_and_realRooted_proved`: §11 item 1 ⇒ RH with Hadamard's factorisation proved ([note](../formalisations/weil-positivity.md))

#### `HalfPlaneJoinsChar`: The band for every `L(s, χ)` and the twin-form rates at `11/12`

- `HalfPlaneJoins.LFunction_band_eleven_twelfths`: The band `|2 Re ρ − 1| ≤ 5/6` for every `L(s, χ)`, `χ ≠ 1`
- `HalfPlaneJoins.chi4_rate_eleven_twelfths`: `L(s, χ₋₄)`'s twin form
- `HalfPlaneJoins.chi8_rate_eleven_twelfths`: `L(s, χ₋₈)`'s twin form
- `HalfPlaneJoins.QK4_rate_eleven_twelfths`: The twin form `2Q_ζ + Q_{χ₋₄}` of `ζ·ζ_{ℚ(i)}`
- `HalfPlaneJoins.QC_rate_eleven_twelfths`: Every good character
- `HalfPlaneJoins.QKχ_rate_eleven_twelfths`: The twin form `2Q_ζ + Q_χ` of `ζ·L(χ)`, every good character
- `HalfPlaneJoins.realRooted_rate_eleven_twelfths`: Every real-rooted monotone base probe

#### `HalfPlaneJoinsFinal`: The half-plane's joins with no hypothesis

- `HalfPlaneJoins.zeta_band_eleven_twelfths`: Every nontrivial zero of `ζ` has `|2 Re ρ − 1| ≤ 5/6`.
- `HalfPlaneJoins.weil_rate_eleven_twelfths`: `ζ`'s twin form ([note](../formalisations/weil-positivity.md))
- `HalfPlaneJoins.chi3_rate_eleven_twelfths`: `L(s, χ₋₃)`'s twin form
- `HalfPlaneJoins.QK3_rate_eleven_twelfths`: The twin form `2Q_ζ + Q_{χ₋₃}` of `ζ·ζ_{ℚ(√−3)}`
- `HalfPlaneJoins.lam_prefactor_eleven_twelfths`: The prefactor ([note](../formalisations/weil-positivity.md))
- `BohrJoins.shell_eleven_twelfths`: The Bohr shell at `11/12`

#### `HurwitzCross`: The chain with zeros on `ℝ ∪ iℝ`

- `WeilForm.rh_of_prime_side_cross`: The chain with zeros on the cross ([note](../formalisations/weil-positivity.md))
- `WeilForm.rh_of_prime_side`: §11 item 1 ⇒ RH, with prime-side hypotheses only ([note](../formalisations/weil-positivity.md))
- `WeilForm.rh_of_simple_ground_states`: The chain with the zero-swap lemma plugged in ([note](../formalisations/weil-positivity.md))
- `WeilForm.rh_of_simple_ground_states'`: The chain, with `ζ ≠ 0` on `(0, 1)` discharged ([note](../formalisations/weil-positivity.md))

#### `KaiserBulk`: The bulk of the Kaiser probe and the doubled rate

- `Kaiser.lam_kaiser`: Rung 0, doubled rate ([note](../formalisations/weil-positivity.md))

#### `KubotaCharacter`: Kubota's character

- `Eis.kub_int`: `κ` is trivial on `SL_2(ℤ) ∩ Γ_1(3)` ([note](../formalisations/cubic-theta.md))
- `Eis.kub2_mul`: `κ` is a homomorphism on `Γ_2` ([note](../formalisations/cubic-theta.md))

#### `KubotaEisenstein`: The cubic Eisenstein series on `Γ_1(3)`: convergence and automorphy

- `Eis.summable_eisTerm`: Absolute convergence ([note](../formalisations/cubic-theta.md))
- `Eis.eis1_slAct`: Automorphy ([note](../formalisations/cubic-theta.md))

#### `KubotaEnergy`: The conformality of the action, and the invariant energy

- `Eis.lintegral_energy_actP`: The energy `∫ v²·edens(F′) dz dv/v³` is invariant under `SL_2(ℂ)`
- `Eis.edens_automorphic`: The energy density of an automorphic function is invariant

#### `KubotaThetaInv`: θ is invariant under `SL_2(ℤ)`

- `Eis.isAut_thS_Gam2`: θ's Fourier series is automorphic on `Γ_2 = SL_2(ℤ)Γ_1(3)` ([note](../formalisations/cubic-theta.md))

#### `KubotaThetaPair`: The pairing with pseudo-Eisenstein series, and θ ≠ 0

- `Eis.thetaL_ne_zero`: θ ≠ 0 ([note](../formalisations/cubic-theta.md))

#### `KubotaThetaProof`: The Kubota–Patterson display, proved

- `Eis.kubotaTheta`: The display `KubotaTheta`, proved *paper* ([note](../formalisations/cubic-theta.md))
- `Eis.ne_zero_of_re_gt_eleven_twelfths`: The half-plane ([note](../formalisations/openai-half-plane.md))

#### `LSeriesLandau`: Landau's theorem for Dirichlet series with nonnegative coefficients

- `LandauLaplace.LSeries_landau`: Landau's theorem for L-series with nonnegative coefficients
- `LandauLaplace.LSeries_not_holomorphic_at_abscissa`: An L-series with nonnegative coefficients is singular at the real point of its abscissa

#### `LatticeCount`: The ball tower from counting integer points

- `BallTower.count_div_pow_tendsto_ballVol`: Same statement by radius
- `BallTower.counted_volume_max_five`: The counted volume (the limit of `latticeCount n R / Rⁿ`) is largest in dimension 5.

#### `Limit`: Step (iii): Theorem 1bu(ii)'s limit shape, and the chain to `RiemannHypothesis`

- `WeilForm.rh_of_pairing_and_realRooted`: 1bu(ii) + item 6, assembled ([note](../formalisations/weil-positivity.md))
- `WeilForm.rh_of_D_and_realRooted`: Theorem 1bu(ii) + item 6 in the paper's own terms ([note](../formalisations/weil-positivity.md))

#### `LocalTeeth`: The teeth, one prime at a time

- `LocalTeeth.card_two_sq`: 2D teeth mod `p`, nonzero shell
- `LocalTeeth.card_four_sq`: 4D teeth mod `p`, nonzero shell
- `LocalTeeth.teeth_mod_prime`: At a prime `p`

#### `Madelung`: The Madelung constant of the square lattice

- `Madelung.lseries_coeff`: The alternating lattice sum of the square lattice
- `Madelung.differentiableOn_rhs`: The continuation

#### `MertensOmega`: Mertens and Liouville: one-sided bounds give zero-free half-planes

- `PsiOmega.mertens_omega_half`: `M(x) = Ω±(x^θ)` for every `0 < θ < ½`, unconditionally
- `PsiOmega.rh_of_liouville_bound`: A one-sided bound `εL(x) ≤ c√x` gives RH ([note](../formalisations/weil-positivity.md))
- `PsiOmega.rh_of_polya`: Pólya's conjecture implies RH ([note](../formalisations/weil-positivity.md))

#### `Orthogonality`: Orthogonality forces the Euclidean structure

- `Orthogonality.tendsto_mean_sq_norm_primeSum`: The radius is the root mean square of the prime sum
- `Orthogonality.pythagoras_lpGauge_iff`: Orthogonality forces `p = 2`

#### `ParityCert`: Weil positivity in both parity sectors, as far as the relaxation reaches

- `WeilForm.log_three_le`
- `WeilForm.weilQg_ge_both`: Weil positivity for every real `g`

#### `ParityCont`: The parity gap by continuation in the support

- `WeilForm.rh_of_no_crossing`: RH from no crossing ([note](../formalisations/weil-positivity.md))

#### `ParityGap`: Real zeros from the parity gap

- `WeilForm.rh_of_parity_gap`: RH from the parity gap ([note](../formalisations/weil-positivity.md))

#### `ParityRelax`: The relaxation for both parities and every prime power below the support

- `WeilForm.wP_zero`

#### `ParitySplit`: Weil's form splits by parity: positivity for every real `g`

- `WeilForm.weilQg_ge_twentieth_all`: Weil positivity for every real `g`, pure Lean ([note](../formalisations/weil-positivity.md))

#### `PhiDExp`: Double-exponential upper bounds on the first three rungs

- `WeilForm.lam_dexp`: Rung 0, double-exponential ([note](../formalisations/weil-positivity.md))
- `WeilForm.lamO_dexp`: Rung 1, double-exponential ([note](../formalisations/weil-positivity.md))
- `WeilForm.lam2_dexp`: Rung 2, double-exponential ([note](../formalisations/weil-positivity.md))

#### `PhiNull`: The bilinear Weil form is the bilinear zero sum

- `WeilForm.bil_zero_sum`: The bilinear Weil form is the bilinear zero sum ([note](../formalisations/weil-positivity.md))

#### `PoleRelax`: Past `λ₀ = 0`: the pole term through a finite relaxation

- `WeilForm.memLp_ind`
- `WeilForm.ind_mul_ind`
- `WeilForm.weilQ_ge_pole`: Weil positivity with the pole term, for every support `0 < a ≤ 1/4`

#### `Positivity`: The pole-free form `Q₀`: existence, one sign, uniqueness

- `WeilForm.weilQ0_abs_le`: Beurling–Deny for `Q₀` ([note](../formalisations/weil-positivity.md))

#### `PrimeRaces`: Prime races mod 3, 4 and 8, unconditionally

- `PsiOmega.race_four_half`: The race mod 4
- `PsiOmega.hadamard_chi4`: The Hadamard product for `L(s, χ₄)`
- `PsiOmega.race_three_half`: The race mod 3
- `PsiOmega.race_eight_half`: The race mod 8

#### `PrimeRelax`: Weil positivity past the first prime: every support `2a ≤ 0.8`

- `WeilForm.weilQ_ge_prime`: Weil positivity through the first prime

#### `PrimeRelax3`: Weil positivity up to the second prime: every support `2a ≤ 1.0986 < log 3`

- `WeilForm.weilQ_ge_prime3`: Weil positivity up to the second prime

#### `PrimeSide`: §11 item 1, restated with prime-side hypotheses only

- `WeilForm.hypConv_of_D`: The D-route is a special case of (a) ([note](../formalisations/weil-positivity.md))

#### `PsiOmega`: Zeros of `ζ` from one-sided bounds on summatory functions

- `PsiOmega.psi_omega_half`: `ψ(x) − x = Ω±(x^θ)` for every `0 < θ < ½`, unconditionally

#### `QuadIdeals`: The ideals of a quadratic field of each norm, and its Dedekind zeta function

- `QuadIdeals.trichotomy`: Every prime splits, is inert or ramifies

#### `Roadmap`: §11 roadmap, item 1: the objects stated, and the reduction to RH proved

- `WeilForm.rh_of_realRooted_limit`: Item 6's step, proved ([note](../formalisations/weil-positivity.md))
- `WeilForm.rh_of_ground_states`: The roadmap's endpoint, as a theorem ([note](../formalisations/weil-positivity.md))

#### `SimpleCont`: Continuation for simplicity

- `WeilForm.first_degeneracy_036`: Simplicity route, with its start discharged ([note](../formalisations/weil-positivity.md))
- `WeilForm.not_simple_iff_secular`: The exact secular characterisation ([note](../formalisations/weil-positivity.md))

#### `StripConv`: (a) on the critical strip, and an `L²` route to it

- `WeilForm.rh_of_relgap`: RH from a relative spectral gap

#### `StructureD`: Theorem D, formal

- `WeilForm.chain_top_zeros`: Theorem D, zeros on the cross ([note](../formalisations/weil-positivity.md))
- `WeilForm.theoremD`: Theorem D, formal ([note](../formalisations/weil-positivity.md))
- `WeilForm.rh_of_hypConv_top`: The RH chain with simplicity removed ([note](../formalisations/weil-positivity.md))

#### `SwapRealize`: The swap realisation, proved

- `WeilForm.zeros_real_or_imag'`: Zeros of a simple ground state lie on `ℝ ∪ iℝ` ([note](../formalisations/weil-positivity.md))
- `WeilForm.rh_of_eventually_simple`: RH from (a) and eventual simplicity ([note](../formalisations/weil-positivity.md))

#### `TheoremC`: Theorem C, formal, in `H²` generality

- `WeilForm.simple_iff_no_flat`: The corollary, formal in `H²` form: the ground state is simple iff no nonzero ground-space element is `H²`-flat at the edges ([note](../formalisations/weil-positivity.md))
- `WeilForm.simple_not_flat`: A simple ground state is never edge-flat ([note](../formalisations/weil-positivity.md))

#### `TwinLandau`: The Landau argument for twin forms, for any zero family

- `TwinLandau.Q_ge_of_rates`: The converse bound with a rate per pole

#### `Unconditional`: Saturation without RH: verified zeros, a zero-counting bound, and monotonicity

- `WeilForm.pinned_unconditional_zero`: Pinning without RH, as a zero of `ĝ` ([note](../formalisations/weil-positivity.md))

#### `Uniqueness`: The ground-state space, and when the ground state is unique

- `WeilForm.groundState_unique_of_gap`: Uniqueness up to sign, gap form ([note](../formalisations/weil-positivity.md))

#### `VinoRec`: Vinogradov's mean value theorem, step I.3b: bad count and the one-step inequality

- `VinoRec.vmvt_weak`: Vinogradov's mean value theorem (weak classical form)

#### `WeilChiCriterion`: Weil's criterion for Dirichlet L-functions

- `PsiOmega.grh_iff_QC_subexp`: GRH for `χ` ⟺ `Q_χ/‖g‖²` has no negative part of exponential rate ([note](../formalisations/weil-positivity.md))
- `PsiOmega.QC_fails_rate`: An off-line zero makes `Q_χ` fail at an exponential rate ([note](../formalisations/weil-positivity.md))
- `PsiOmega.grh_iff_twins_chi4`: Weil's criterion for `L(s, χ₋₄)` ([note](../formalisations/weil-positivity.md))
- `PsiOmega.grh_iff_twins_chi3` ([note](../formalisations/weil-positivity.md))
- `PsiOmega.grh_iff_twins_chi8` ([note](../formalisations/weil-positivity.md))
- `PsiOmega.twins_rate_chi4`: The graded criterion for `χ₋₄` ([note](../formalisations/weil-positivity.md))
- `PsiOmega.grh_iff_QC_subexp_chi4`: GRH for `χ₋₄` ⟺ `Q_{χ₋₄}/‖g‖²` has no negative part of exponential rate ([note](../formalisations/weil-positivity.md))

#### `WeilChiDensity`: GRH(χ) gives `Q_χ ≥ 0` on every probe

- `PsiOmega.grh_iff_QC_subexp_all`: The rate form over every probe ([note](../formalisations/weil-positivity.md))

#### `WeilConverse`: The converse: an off-line zero makes Weil's form negative somewhere

- `WeilForm.weil_criterion_finite`: Weil's criterion, both directions, for a family with finitely many off-line zeros ([note](../formalisations/weil-positivity.md))

#### `WeilDedekind`: A twin form for `ζ_{ℚ(i)} = ζ · L(s, χ₋₄)`, with the `ζ` zeros doubled

- `Dedekind4.rh_grh_iff_QK_twins`: Weil's criterion for `ζ_{ℚ(i)}`, twin boxes ([note](../formalisations/weil-positivity.md))
- `Dedekind4.rh_grh_iff_QK_subexp`: `RH ∧ GRH(χ₋₄)` ⟺ the Dedekind twin form's defect is subexponential ([note](../formalisations/weil-positivity.md))
- `Dedekind4.rh_grh_of_member_zero`: `GRHMemberZero` gives both RH and GRH(χ₋₄) ([note](../formalisations/weil-positivity.md))
- `Dedekind4.QK_nonneg_of_member_zero`: `GRHMemberZero` forces the Dedekind twin form to be nonnegative ([note](../formalisations/weil-positivity.md))
- `Dedekind4.QC_chi4_littleO`: `Q_{χ₋₄}(twin (box 1) λ) ≥ −ε e^λ` eventually ([note](../formalisations/weil-positivity.md))
- `Dedekind4.QK_littleO`: The Dedekind twin form is `≥ −o(e^λ)` ([note](../formalisations/weil-positivity.md))

#### `WeilDischarge`: Discharging `WeilExplicit` for the library's test functions

- `WeilForm.lam_decay_uncond`: The decay of the ground energy, unconditional ([note](../formalisations/weil-positivity.md))
- `WeilForm.lamO_decay_uncond`: Rung 1, unconditional ([note](../formalisations/weil-positivity.md))
- `WeilForm.lam2_decay_uncond`: Rung 2, unconditional ([note](../formalisations/weil-positivity.md))

#### `WeilIndexConverse`: Off-line zero quadruples force negative directions of `Q`

- `WeilForm.negIndex_eq_quadruples`: The negative index of Weil's form counts the off-line quadruples ([note](../formalisations/weil-positivity.md))

#### `WeilIndexInfinite`: Every off-line quadruple gives a negative direction of `Q`

- `WeilForm.negDirections_unbounded`: Infinitely many off-line quadruples make the negative index unbounded ([note](../formalisations/weil-positivity.md))

#### `WeilIndexZeta`: Negative directions of `Q` count off-line zeros of ζ, with no named input

- `WeilForm.finrank_le_offline_zeta`: The crude count ([note](../formalisations/weil-positivity.md))
- `WeilForm.finrank_le_quadruples_C2`: The same for a space of `C²` probes vanishing near `±a` ([note](../formalisations/weil-positivity.md))
- `WeilForm.exists_offline_of_neg_C2`: One `C²` probe with `Q < 0` exhibits an off-line zero of ζ ([note](../formalisations/weil-positivity.md))

#### `WeilLandau`: Weil's criterion for `ζ` with no finiteness hypothesis

- `WeilForm.line_of_weil_twins`: Weil's criterion, twin boxes only ([note](../formalisations/weil-positivity.md))
- `WeilForm.rh_of_weil_twins`: Weil's criterion for `ζ`, twin boxes only, no finiteness hypothesis ([note](../formalisations/weil-positivity.md))
- `WeilForm.rh_of_weil`: Weil's criterion for `ζ`, no finiteness hypothesis ([note](../formalisations/weil-positivity.md))
- `WeilForm.rh_iff_twins_subexp`: RH ⟺ the twin form's defect is subexponential ([note](../formalisations/weil-positivity.md))

#### `WeilRH`: RH gives `Q ≥ 0` on every probe, and Weil's criterion for `ζ`

- `WeilForm.line_of_RH` ([note](../formalisations/weil-positivity.md))
- `WeilForm.weil_criterion_zeta`: Weil's criterion for `ζ`, both directions, no named input, no finiteness hypothesis ([note](../formalisations/weil-positivity.md))

#### `WeilRate`: The ground energy's rate of failure measures the zeros

- `WeilForm.rh_iff_lam_subexp`: RH ⟺ `λ₁` has no negative part of exponential rate ([note](../formalisations/weil-positivity.md))
- `WeilForm.lam_fails_exponentially`: If RH fails, `λ₁` fails exponentially ([note](../formalisations/weil-positivity.md))

#### `WeilTwinGeneral`: The twin criterion for every real-rooted base and every good character

- `WeilTwinGeneral.line_of_twins_g` ([note](../formalisations/weil-positivity.md))
- `WeilTwinGeneral.rh_iff_twins_realRooted`: Weil's twin criterion with any real-rooted monotone base probe ([note](../formalisations/weil-positivity.md))
- `WeilTwinGeneral.twins_rate_realRooted`: The graded form ([note](../formalisations/weil-positivity.md))
- `WeilTwinGeneral.rh_iff_twins_concave`: Weil's twin criterion with any concave base probe ([note](../formalisations/weil-positivity.md))
- `WeilTwinGeneral.rh_iff_twins_box`: `rh_of_weil_twins` (both directions), as the box instance. ([note](../formalisations/weil-positivity.md))
- `WeilTwinGeneral.grh_iff_twins_chi7` ([note](../formalisations/weil-positivity.md))
- `WeilTwinGeneral.race_seven_half`: The race mod 7 (quadratic residues against non-residues), unconditional `Ω±(x^θ)`, `θ < ½`.
- `WeilTwinGeneral.rh_grh_iff_QKχ_twins`: The twin-box criterion for every good character ([note](../formalisations/weil-positivity.md))
- `WeilTwinGeneral.rh_grh_iff_twins_Q3`: `ζ_{ℚ(√−3)}`. ([note](../formalisations/weil-positivity.md))
- `WeilTwinGeneral.rh_grh_iff_twins_Q8`: `ζ_{ℚ(√−2)}`. ([note](../formalisations/weil-positivity.md))
- `WeilTwinGeneral.rh_grh_iff_twins_Q7`: `ζ_{ℚ(√−7)}`. ([note](../formalisations/weil-positivity.md))
- `WeilTwinGeneral.rh_grh_iff_twins_Q4`: The theorem recovered as an instance. ([note](../formalisations/weil-positivity.md))

#### `WindowForm`: The prime-side window form: its algebra, its certification logic, and the counterexample mechanism

- `WindowForm.ghat_cos`: The window basis transform
- `WindowForm.ghat_pole`: The pole value
- `WindowForm.product_dd`: Products of transforms are divided differences
- `WindowForm.hasDerivAt_uA`: On the diagonal, the divided difference becomes the `A`-derivative of `u_A = A c/(s − A)`, which is `c s/(s − A)²`.
- `WindowForm.phi_u_trig`: The prime term's trigonometric reduction
- `WindowForm.basis_trig`: At the basis frequencies `ω_k = kπ/a`
- `WindowForm.posDef_of_cholesky`: A Cholesky certificate
- `WindowForm.gram_pos`: A positive-definite Gram matrix makes the form strictly positive on every nonzero combination of the basis
- `WindowForm.quadruple_sum`: The off-line quadruple.
- `WindowForm.offline_negative`: The mechanism of positivity loss

#### `XiBounds`: The order of `Ξ`, from Riemann's theta kernel

- `WeilForm.rh_of_D_and_realRooted_final`: Roadmap item 1, final form ([note](../formalisations/weil-positivity.md))

#### `ZetaInputs`: Discharging the remaining classical inputs over the zeros of `ζ`

- `WeilForm.pinned_zeta`: The pinning theorem over the zeros of `ζ` ([note](../formalisations/weil-positivity.md))

### `lib/pnt`

#### `AlmostAllArch`: Primes in almost all short intervals, part 1: the explicit formula at one point

- `AlmostAll.arch_far`: The archimedean term far from `0`

#### `AlmostAllMean`: Primes in almost all short intervals, part 2: the zero sum in mean square

- `AlmostAll.head_mean_square`: The head in mean square

#### `AlmostAllPrimes`: Primes in almost all short intervals, part 3: the exceptional set

- `AlmostAll.almost_all_of_density`: Primes in almost all short intervals, from a density estimate ([note](../formalisations/zeta-density.md))
- `AlmostAll.almost_all_short_primes`: Primes in almost all short intervals for every `θ > 1/6` ([note](../formalisations/zeta-density.md))

#### `BohrKV`: The Korobov–Vinogradov region as a shell around the Bohr sphere

- `BohrKV.shell_of_KV`: The Korobov–Vinogradov region is a shell at each height

#### `ChiPNT`: `ψ(x, χ) = O(x^{11/12+η})` for every Dirichlet character `χ ≠ 1`

- `ChiPNT.sum_le_uniform_of`: Sums of the coefficients of `−F′/F`, with explicit constants
- `ChiPNT.sum_le_uniform`: Sums of the coefficients of `−F′/F`, with their constants
- `ChiPNT.sum_isBigO_of_zeroFree`: Sums of the coefficients of `−F′/F` in a zero-free half-plane
- `ChiPNT.psiChi_isBigO_of_zeroFree`: `ψ(x, χ)` in a zero-free half-plane
- `ChiPNT.psiChi_isBigO_eleven_twelfths`: `ψ(x, χ) = O(x^{11/12+η})`

#### `ChiUniform`: Bounds for the real Dirichlet L-functions, uniform in the modulus

- `ChiUniform.LFunction_ctr_inv_le`: `‖L(3/2 + it, χ)‖⁻¹ ≤ ζ(3/2)`, from `1/L(s, χ) = Σ χ(n)μ(n)n^{−s}` (a step of `psiChi_le_uniform_of`).
- `ChiUniform.logDeriv_LFunction_right`: `‖L′/L(s, χ)‖ ≤ −ζ′/ζ(3/2)` on `Re s ≥ 3/2` (a step of `psiChi_le_uniform_of`).
- `ChiUniform.psiChi_le_uniform_of`: `ψ(x, χ)` uniformly in the modulus, from the constants of `sum_le_uniform`
- `ChiUniform.psiChi_le_uniform`: `ψ(x, χ)` uniformly in the modulus

#### `ClassNumberBound`: Gauss's class number problem, with an explicit bound

- `ClassNumberBound.abs_discr_le`: Gauss's class number problem, with an explicit bound

#### `CyclotomicFrobenius`: Small Frobenius elements generate the cyclotomic Galois groups

- `CyclotomicFrobenius.closure_frob_eq_top`: The Frobenius elements of the small primes generate the cyclotomic Galois group
- `CyclotomicFrobenius.exists_frob_generator`: A single small Frobenius element generates the cyclotomic Galois group

#### `DetectEM`: Zero detection by Euler–Maclaurin

- `DetectEM.density_unconditional`: Zero density

#### `DivisorExponent`: The divisor problems in a zero-free half-plane

- `DivisorExponent.integral_pow_mul_cexp`: `∫_0^∞ u^m e^{−cu} du = m!/c^{m+1}`
- `DivisorExponent.inv_sub_one_pow_eq_integral`: `(s − 1)^{−m} = ∫_0^∞ (u^{m−1}/(m−1)!) e^{−(s−1)u} du` for `Re s > 1`, `m ≥ 1`.
- `DivisorExponent.LSeries_dk`: `L(d_k, s) = ζ(s)^k` on `Re s > 1`, with absolute convergence.
- `DivisorExponent.verticalIntegral_inv_sub_one_pow`: The principal parts against the smoothing
- `DivisorExponent.zeta_pow_eq`: `ζ(s)^k = Σ_{j<k} c_j (s − 1)^{j−k} + g_k(s)`
- `DivisorExponent.smoothedSum_dk_eq`: The smoothed divisor sum
- `DivisorExponent.norm_remainder_le`: The remainder
- `DivisorExponent.coeff_Pk`: The leading coefficient
- `DivisorExponent.natDegree_Pk_eq`: `P_k` has degree exactly `k − 1`.
- `DivisorExponent.divisor_isBigO_of_zeroFree`: The divisor problems in a zero-free half-plane
- `DivisorExponent.divisor_isBigO_eleven_twelfths`: The divisor problems at `11/12`
- `DivisorExponent.divisor_isBigO_Theta`: The divisor problems at `Θ`

#### `ExplicitConstants`: Explicit constants for Littlewood's bounds and the least quadratic nonresidue

- `ExplicitConstants.psiChi_le_explicit`: `ψ(x, χ)` uniformly in the modulus, with an explicit constant
- `ExplicitConstants.logDeriv_le_explicit`: `|L′/L(σ, χ)| ≤ 10²¹ log log(N + 16)` on `(1, 2]`
- `ExplicitConstants.norm_LFunction_one_le_explicit`: `|L(1, χ)| ≤ e^{2·10²¹} log log(N + 16)`
- `ExplicitConstants.norm_LFunction_one_ge_explicit`: `|L(1, χ)| ≥ e^{−2·10²¹}/log log(N + 16)`
- `ExplicitConstants.norm_logDeriv_one_le_explicit`: `|L′/L(1, χ)| ≤ 10²¹ log log(N + 16)`
- `ExplicitConstants.exists_prime_eq_explicit`: The least primes with `χ(p) = ±1`, with an explicit constant, for every `A > 12`
- `ExplicitConstants.exists_prime_eq_13`: The least primes with `χ(p) = ±1`, at `A = 13`
- `ExplicitConstants.exists_nonsquare_le_explicit`: The least quadratic nonresidue, with an explicit constant, for every `A > 12`
- `ExplicitConstants.exists_nonsquare_le_13`: `n(p) ≤ 10³⁰⁴ (log p)¹³`
- `ExplicitConstants.exists_nonsquare_le_rpow_explicit`: `n(p) ≤ 10³⁰⁴(13/δ)¹³p^δ`

#### `ExplicitSmooth`: An explicit smoothing and its Mellin constants

- `ExplicitSmooth.contDiff_ν₀`
- `ExplicitSmooth.mass_ν₀`
- `ExplicitSmooth.mellin_ν₀_le_geom`: The Mellin transform of `Smooth1 ν₀ ε` on a line, with its constant

#### `HalfPlaneFinal`: The half-plane `Re s > 11/12` in the prime number theorem

- `HalfPlanePNT.psi_isBigO_eleven_twelfths`: The prime number theorem with error `O(x^{11/12+ε})` *paper* ([note](../formalisations/harman-sieve.md))

#### `HalfPlaneJoinsPNT`: Joins from the exponent `Θ` into older sockets

- `HalfPlaneJoinsPNT.weil_twins_rate_Theta`: The exponential rate of the negative part of `ζ`'s twin form is exactly `2Θ − 1`
- `HalfPlaneJoinsPNT.psiOmegaSqrt_of_not_RH`: If RH fails, `ψ(x) − x = Ω±(√x)`

#### `HalfPlaneLindelof`: A Lindelöf bound in a zero-free half-plane

- `HalfPlaneLindelof.norm_le_interp`: Interpolation on a rectangle
- `HalfPlaneLindelof.hasDerivAt_log_norm`: The derivative of `log |f|`
- `HalfPlaneLindelof.logDeriv_le_interp`: The interpolated bound on `ζ′/ζ`
- `HalfPlaneLindelof.zeta_bound_of_zeroFree`: A Lindelöf bound in a zero-free half-plane
- `HalfPlaneLindelof.zeta_bound_eleven_twelfths`: The Lindelöf bound on `Re s > 11/12`
- `HalfPlaneLindelof.zeta_bound_Theta`: The Lindelöf bound on `Re s > Θ`

#### `HalfPlanePNT`: A zero-free half-plane gives a power saving in the prime number theorem

- `HalfPlanePNT.logDeriv_le_of_zeroFree`: The log-derivative under a zero-free half-plane
- `HalfPlanePNT.psi_isBigO_of_zeroFree`: A zero-free half-plane gives a power saving in the prime number theorem

#### `InghamDensity`: Ingham's zero-density exponent `2 + 4c` from `|ζ(1/2 + it)| ≪ |t|^c`

- `InghamDensity.densityXi_of_zetaCrit`: Ingham's exponent from a pointwise bound on the critical line
- `InghamDensity.inghamFromC`: `CrossCriteria.InghamFromC c` for every `c ≥ 0`
- `InghamDensity.densityXi_17_6`: Zero density at the exponent
- `InghamDensity.densityXi_Theta`: Zero density at `Θ`
- `InghamDensity.densityHypothesis_of_lindelof`: Lindelöf implies the density hypothesis
- `InghamDensity.short_primes_Theta`: Primes in short intervals at `Θ`

#### `InghamDetect`: A zero detector with the line moved to `Re s = 1/2`

- `InghamDensity.norm_Gamma_exp_le`: `|Γ(x + it)| ≤ KE e^{−|t|}` on `½ ≤ x ≤ 3`
- `InghamDensity.detect_identity`: The identity at a zero
- `InghamDensity.trichotomy`: The trichotomy at a zero

#### `KVBridge`: Rung 3, closed: the growth bound for ζ and the zero-free region it gives

- `KVBridge.polylogGrowth_kv`: The growth hypothesis holds for every `4/5 ≤ a ≤ 1`
- `KVBridge.polylogGrowth_sharp`: The growth hypothesis holds for every `2/3 < a ≤ 1`
- `KVBridge.zeroFree_kv`: Zero-free region
- `KVBridge.rung3_kv`: Rung 3

#### `KaiserKV`: The Korobov–Vinogradov region in the Kaiser prefactor

- `KaiserKV.lam_prefactor_KV`: The Kaiser prefactor with the Korobov–Vinogradov saving

#### `Landau`: Landau's lemma, general form: layer III of rung 3

- `Landau.zeroFree_of_growth`: L3 (Landau's theorem, general form)
- `Landau.logDerivBnd_of_growth`: L4
- `Landau.rung3_of_growth`: Layer III, assembled: polylog growth ⇒ rung 3

#### `LandauKV`: The last bit, step R3: the Korobov–Vinogradov zero-free region

- `LandauKV.zeroFree_KV`: The Korobov–Vinogradov zero-free region

#### `LeastNonresidue`: The least quadratic nonresidue, and the least primes with `χ(p) = ±1`

- `LeastNonresidue.re_psiChi_ge`: If `χ(p) = ε`, `ε = ±1`, at every prime `p ≤ x` that does not divide `q`, then `ε·Re ψ(x, χ) ≥ ψ(x) − 4√x log x − log q`.
- `LeastNonresidue.rpow_le_of_forall_eq`: If `χ(p) = ε` at every prime `p ≤ x` not dividing `q`, then `x^{1/A} ≤ K log(q + 2)`, for every `A > 12`, with `K` depending on `A` only…
- `LeastNonresidue.exists_prime_eq`: The least primes with `χ(p) = ±1`
- `LeastNonresidue.exists_prime_ne_one`: A prime with `χ(p) ≠ 1`, for every Dirichlet character `χ ≠ 1`
- `LeastNonresidue.exists_nonsquare_le_of`: The least quadratic nonresidue, with the constant
- `LeastNonresidue.exists_nonsquare_le`: Vinogradov's least quadratic nonresidue conjecture, in Ankeny's form
- `LeastNonresidue.exists_nonsquare_le_rpow_of`: `n(p) ≤ C₀(13/δ)^{13}p^δ` from `n(p) ≤ C₀(log p)^{13}`
- `LeastNonresidue.exists_nonsquare_le_rpow`: `n(p) ≪_δ p^δ`

#### `LeastPrimitiveRoot`: The least primitive root

- `LeastPrimitiveRoot.norm_sum_primRoot_sub_le`: The prime powers that are primitive roots
- `LeastPrimitiveRoot.exists_prime_primRoot_le`: The least prime primitive root
- `LeastPrimitiveRoot.exists_prime_primRoot_le_rpow`: The least prime primitive root is at most `q^ε`
- `LeastPrimitiveRoot.exists_prime_primRoot_le_rpow_prime`: The least prime primitive root mod a prime
- `LeastPrimitiveRoot.exists_prime_primRoot_le_rpow_pow`: The least prime primitive root mod a prime power
- `LeastPrimitiveRoot.exists_prime_primRoot_le_safe`: Safe primes

#### `Linnik22000E`: Linnik's theorem with exponent `11 / 5`, by the decomposition to depth 8 and its certificate at `n = 272`

- `Linnik22000E.routeOK22000D`: `route22000D` is a route *paper*
- `Linnik22000E.fits22000E`: `grid22000E` fits `route22000D` *paper*
- `Linnik22000E.ibFits22000E`: `ibPar22000E`'s exponent `Lnum/Lden` is the route's `L = 11 / 5`. *paper*
- `Linnik22000E.deepGrid22000E`: `grid22000E` holds the decomposition to depth 8 *paper*
- `Linnik22000E.linnik_22000e`: Linnik's theorem with exponent `11 / 5`, by the decomposition to depth 8 at `n = 272` *paper* ([note](../formalisations/chen-gupta-li-density.md))

#### `LinnikAFE`: The approximate functional equation for `L(s, χ)²`

- `LinnikGamma.norm_gammaFactor_ratio_le`: The ratio of two values of the Archimedean factor
- `LinnikGamma.verticalIntegral_sub_eq`: Moving the line of integration across a simple pole at `0`
- `LinnikGamma.afe`: The approximate functional equation for `L(s, χ)²` ([note](../formalisations/hybrid-fourth-moment.md))

#### `LinnikBuckets`: The off-diagonal pairs in dyadic buckets of the analytic conductor

- `LinnikReflect.pair_sum_pointwise`: Pointwise in `v`, all characters `χ ≠ χ′` at once

#### `LinnikCGL112`: Their (11.2), the blocks of their Proposition 7.2 summed

- `LinnikCGL112.S3_le_blocks`: The blocks summed
- `LinnikCGL112.S3_le_112`: Their (11.2), in explicit form

#### `LinnikCGLAsum`: The sum over `a` in their Lemma 8.2, by the Ramanujan sum

- `LinnikCGLAsum.sum_a_finite_le`: The sum over `a`, finite form

#### `LinnikCGLBlock`: `S₃,₃`, `S₃,₄` and the block sums of `Ĩ`, by their Proposition 8.1 and Lemmas 9.1 and 9.2

- `LinnikCGLBlock.S34_le_P81`: `S₃,₄` on the block `k`, by their Proposition 8.1
- `LinnikCGLBlock.block_le`: The block `k`, by their Proposition 8.1 and Lemmas 9.1 and 9.2

#### `LinnikCGLCS`: The two Cauchy–Schwarz steps of their §11 (the `S₃` side)

- `LinnikCGLCS.sum_It_sq_le`: Their first Cauchy–Schwarz step
- `LinnikCGLCS.S32_le`: Their second Cauchy–Schwarz step, (11.1)

#### `LinnikCGLCase`: Their Lemma 10.10 with its case analysis, and their Remark 10.3 (the `S₃` side)

- `LinnikCGLCase.case_le`: Their case analysis (10.4)–(10.5)
- `LinnikCGLCase.remark103`: Their Remark 10.3, in the library's form ([note](../formalisations/chen-gupta-li-density.md))
- `LinnikCGLCase.lemma1010_case`: Their Lemma 10.10 (large gcd terms)

#### `LinnikCGLConst`: The constants of their Lemma 8.2

- `LinnikCGLConst.sum_gw_le`: For `q ≥ 1`, `Σ_{h mod q}(h, q) ≤ q·d(q)`, for `gw`.
- `LinnikCGLConst.KX_le`: For `q ≥ 1`, `L > 0`, `0 ≤ M₁ ≤ L`, `X ≥ 0` and `0 < δ ≤ 1`, `K_X ≤ 40πC_δB₄d(q)⁴L²q(1 + qX)^δ(1 + 2q)^δ`.

#### `LinnikCGLCount`: The count of the pairs `(m₁′, n′)` in their Lemma 8.2

- `LinnikCGLCount.count_le`: Their count

#### `LinnikCGLCov`: The terms `n ≠ 0` of `ĝ_a` over `|ξ| ≤ X`, by the change of variables to their `Σ_II`

- `LinnikCGLCov.integral_r_eq`: Their change of variables
- `LinnikCGLCov.integral_gstar_le`: The terms `n ≠ 0` over `|ξ| ≤ X`

#### `LinnikCGLDecay`: The Fourier decay of their `f_b`, in the form of their Proposition 8.1 (the `S₃` side)

- `LinnikCGLDecay.fb_decay`: The decay for `j ≥ 1`
- `LinnikCGLDecay.fb_decay_all`: The decay premise of `CGLP81` for their `f_b`

#### `LinnikCGLDensity`: Chen–Gupta–Li's density estimate on `[5/7, 16/21]` for every `ε` (`LinnikCGL.CGLDensity`)

- `LinnikCGLDensity.cglDensity`: Chen–Gupta–Li's density estimate on `[5/7, 16/21]` ([note](../formalisations/chen-gupta-li-density.md))

#### `LinnikCGLDiag`: The Gram matrix's diagonal against its main term

- `LinnikCGLDiag.muP_sub_mu0_le`: The diagonal against its main term
- `LinnikCGLDiag.muP_sub_mu0_le_rpow`: For `q ≥ 1` and `N > 0`, `|μ − μ₀| ≤ C_δBq^δ` for `0 < δ ≤ 1` (the divisor bound).
- `LinnikCGLDiag.S3_eq_all`: The condition "not all equal" removed

#### `LinnikCGLEps`: Their Lemmas 10.9 and 10.10 with their `⪅`, and their Proposition 10.2

- `LinnikCGLEps.lemma109_eps`: Their Lemma 10.9 with their `⪅`
- `LinnikCGLEps.lemma1010_eps`: Their Lemma 10.10 with their `⪅`
- `LinnikCGLEps.prop102`: Their Proposition 10.2

#### `LinnikCGLFb`: Their `f_b = ψR̃(·, −b)²` for §11, with a `ψ` that is `1` on the centres (the `S₃` side)

- `LinnikCGLFb.contDiff_fb`
- `LinnikCGLFb.fb_one_ge`: The lower bound of `f`
- `LinnikCGLFb.S34_le_fb`: `S₃,₄` against their `J` for this `f`

#### `LinnikCGLForm`: Their Lemma 8.2 in their form, with the parameters chosen

- `LinnikCGLForm.term2_parts`: Their `II`, the parts
- `LinnikCGLForm.lemma82_form`: Their Lemma 8.2, in their form

#### `LinnikCGLFourier`: Chen–Gupta–Li's Lemma 4.3 (1), the decay of `ĥ_t` (the `S₃` side)

- `LinnikCGLFourier.hasDerivAt_F`: `F_k′ = F_{k+1}`
- `LinnikCGLFourier.fourier_F`
- `LinnikCGLFourier.lemma43`: Chen–Gupta–Li's Lemma 4.3 (1)

#### `LinnikCGLFrob`: The off-diagonal mass of the Gram matrix, explicitly

- `LinnikCGLFrob.ls_points`: The large sieve at the points
- `LinnikCGLFrob.prod_trick_points`: The product trick at the points, squared
- `LinnikCGLFrob.sum_Dp_sq_le`: The mass of the dual sums over all pairs, at one height
- `LinnikCGLFrob.gram_sq_le`: A Gram entry, squared
- `LinnikCGLFrob.frobOff_le`: The off-diagonal mass of the Gram matrix, explicitly

#### `LinnikCGLFtil`: Their smoothing `f̃_b`, and the inner integral of their `Σ_II`

- `LinnikCGLFtil.integral_S2_le`: The inner integral
- `LinnikCGLFtil.sum_psi_norm_Phi_sq_le_ftil`: Their `Σ_II` with the majorant

#### `LinnikCGLFtilP`: Their smoothing `f̃_b` in their induction, and `Λ` against `F`

- `LinnikCGLFtilP.integral_ftil_sq_le`: `L²` against `f̃_b`
- `LinnikCGLFtilP.Lam_le`: `Λ` against `F`

#### `LinnikCGLG`: The majorant of their `J(f⃗)`, Plancherel, and its Fourier transform

- `LinnikCGLG.Jint_le_ga`: `J(f⃗) ≤ Σ_a∫g_a²`
- `LinnikCGLG.integral_sq_ga`: Plancherel for `g_a`
- `LinnikCGLG.fourier_ga`: The Fourier transform of `g_a`

#### `LinnikCGLHB101`: Heath-Brown's Theorem 10.1 with characters, and Chen–Gupta–Li's Propositions 11.1 and 3.1

- `LinnikCGLHB101.cglt101`: Heath-Brown's Theorem 10.1 with characters *paper* ([note](../formalisations/chen-gupta-li-density.md))
- `LinnikCGLHB101.cgls3`: Their Proposition 11.1, at one point per character, with no hypothesis *paper* ([note](../formalisations/chen-gupta-li-density.md))
- `LinnikCGLHB101.prop31`: Their Proposition 3.1, at one point per character, with no hypothesis *paper* ([note](../formalisations/chen-gupta-li-density.md))

#### `LinnikCGLHBIter`: Kerr's iteration with characters

- `LinnikCGLHBIter.caseB`: Case B
- `LinnikCGLHBIter.sig_bound`: Kerr's iteration with characters

#### `LinnikCGLHBLen`: The lengthening of Heath-Brown's double sums

- `LinnikCGLHBLen.cqU_mul_sig_le`: The lengthening
- `LinnikCGLHBLen.sig_le_lengthen`: The lengthening with its constant

#### `LinnikCGLHBPos`: Positivity, and the double sums of Heath-Brown's bound

- `LinnikCGLHBPos.dsum_le`: Positivity
- `LinnikCGLHBPos.shat_sq_le`: Squaring

#### `LinnikCGLHBRefl`: The reflection of Heath-Brown's double sums

- `LinnikCGLHBRefl.sum_gram_sq_le`: The Gram matrices summed
- `LinnikCGLHBRefl.sig_le_refl`: The reflection of the double sum

#### `LinnikCGLJ`: Their `J(f⃗)`, their Proposition 8.1 as a displayed hypothesis, and `S₃,₃`, `S₃,₄` in its form (the `S₃` side)

- `LinnikCGLJ.S34_le_Jint`: `S₃,₄` against their `J` ([note](../formalisations/chen-gupta-li-density.md))
- `LinnikCGLJ.S33_le_S34`: `S₃,₃ ≤ 4S₃,₄` ([note](../formalisations/chen-gupta-li-density.md))

#### `LinnikCGLJtil`: Their Cauchy–Schwarz back to `J(f̃⃗)`, for the terms `|n| ≤ N₀` of their `Σ_II`

- `LinnikCGLJtil.sum_psi_norm_Phi_sq_le_J`: Their `Σ_II` against `J(f̃⃗)`
- `LinnikCGLJtil.sum_integral_Phi_le`: The terms `|n| ≤ N₀` of `B_II`

#### `LinnikCGLL1010`: Their Lemma 10.10, the large-gcd terms, before their case analysis (the `S₃` side)

- `LinnikCGLL1010.lemma106'`: Their Lemma 10.6 without a lower bound on `qT`
- `LinnikCGLL1010.lemma1010`: Their Lemma 10.10 (large gcd terms), before their case analysis

#### `LinnikCGLL105`: Their Lemma 10.5, the energy by the third moment of `R` (the `S₃` side)

- `LinnikCGLL105.sum_triple_le`: The triples bounded
- `LinnikCGLL105.lemma105`: Their Lemma 10.5

#### `LinnikCGLL107`: Their Lemma 10.7, the fourth moment of `R` (the `S₃` side)

- `LinnikCGLL107.group_le`: Their Theorem 10.1 on one group of keys
- `LinnikCGLL107.lemma107`: Their Lemma 10.7, from `CGLT101`

#### `LinnikCGLL109`: Their Lemma 10.9, the small-gcd terms

- `LinnikCGLL109.sum_cube_moment_le`: The weighted third moment over the units
- `LinnikCGLL109.lemma109`: Their Lemma 10.9 (small gcd terms)

#### `LinnikCGLL82`: Their Lemma 8.2 with explicit constants

- `LinnikCGLL82.lemma82_explicit`: Their Lemma 8.2, with explicit constants

#### `LinnikCGLLV`: Chen–Gupta–Li's Proposition 3.1 as a hypothesis, and the large-values counts it gives

- `LinnikCGLLV.lv_range`: The large values of `D_N` on Proposition 3.1's range ([note](../formalisations/chen-gupta-li-density.md))
- `LinnikCGLLV.cgl_all`: Proposition 3.1's count over all characters mod `q`
- `LinnikCGLLV.taylor_pick`: One character off the line
- `LinnikCGLLV.cgl_shift`: Proposition 3.1's count off the line

#### `LinnikCGLLoc`: Local averages of finite exponential sums, toward their Lemmas 10.4 and 10.8 (the

- `LinnikCGLLoc.norm_esum_le_integral`: The local average
- `LinnikCGLLoc.norm_sq_esum_le`: The local average of `|F|²`
- `LinnikCGLLoc.norm_cube_esum_le`: The local average of `|F|³`

#### `LinnikCGLMat`: Chen–Gupta–Li's Proposition 3.1 from a bound on the cubic trace

- `LinnikCGLMat.refined_moment_points`: The moment inequality for the points
- `LinnikCGLMat.prop46`: Their Proposition 4.6 for the points *paper* ([note](../formalisations/chen-gupta-li-density.md))
- `LinnikCGLMat.mvt_case`: The mean value theorem at the points
- `LinnikCGLMat.alg112`: Their §11.2's algebra
- `LinnikCGLMat.prop31_of_third`: Proposition 3.1 from the bound on the cubic trace

#### `LinnikCGLMellin`: The Mellin transform of `w²`, and the Gram entries as vertical integrals

- `LinnikCGLMellin.exists_H_bound`: The decay of `H` on vertical strips
- `LinnikCGLMellin.differentiable_H`: `H` is entire
- `LinnikCGLMellin.perron_Wt`: Perron's formula for `W_τ`
- `LinnikCGLMellin.perron_gram`: Perron's formula for the Gram entries

#### `LinnikCGLMom`: Their Lemma 9.1, the second moments of `R` and `R̃`

- `LinnikCGLMom.lemma91`: Their Lemma 9.1 for `R`
- `LinnikCGLMom.lemma91_Rt`: Their Lemma 9.1 for `R̃`, exact at one point per character

#### `LinnikCGLMom4`: Their Lemma 9.2, the fourth moments of `R` and `R̃`

- `LinnikCGLMom4.lemma92`: Their Lemma 9.2 for `R`, at one point per character ([note](../formalisations/chen-gupta-li-density.md))
- `LinnikCGLMom4.lemma92_Rt`: Their Lemma 9.2 for `R̃`, at one point per character

#### `LinnikCGLN0`: The term `n = 0` of `ĝ_a`, their `I`

- `LinnikCGLN0.sum_integral_g0_le`: Their `I`, the term `n = 0`

#### `LinnikCGLNsum`: `ĝ_a` as a sum over `m₁` and `n`, and the sum over `a` for every `n ≠ 0`

- `LinnikCGLNsum.fourier_ga_split`: The term `n = 0` split off
- `LinnikCGLNsum.sum_a_fourier_ga_le`: `ĝ_a` without its term `n = 0`

#### `LinnikCGLP71`: Their Proposition 7.1 (the `S₃` side)

- `LinnikCGLP71.norm_Psi_le`: The integrand of their (7.3), bounded
- `LinnikCGLP71.prop71`: Their Proposition 7.1 ([note](../formalisations/chen-gupta-li-density.md))

#### `LinnikCGLP72`: Their Proposition 7.2 (the `S₃` side)

- `LinnikCGLP72.Ip_le_It`: Their bound for `|I′(m⃗)|`
- `LinnikCGLP72.sum_Ak_regroup`: Regrouping the bounds by the dyadic scale of `m₂`, with `−m₂` replaced by `m₂` in each block.
- `LinnikCGLP72.prop72`: Their Proposition 7.2 at one point per character

#### `LinnikCGLP81`: Their Proposition 8.1, by their downward induction

- `LinnikCGLP81.cglp81`: Their Proposition 8.1 *paper* ([note](../formalisations/chen-gupta-li-density.md))

#### `LinnikCGLPair`: The bounds of the reflected Gram entries

- `LinnikCGLPair.norm_Eu_mul_le`: The Euler factor against the conductor
- `LinnikCGLPair.norm_dualT_le`: The dual tail far left
- `LinnikCGLPair.norm_integral_Mn_le`: The main part, bounded by its dual sum
- `LinnikCGLPair.norm_integral_Tl_le`: The tail far left
- `LinnikCGLPair.norm_gram_le`: A Gram entry, bounded through its reflection

#### `LinnikCGLPhi`: The Fourier decay of `ψ·K(· − u′)`, the pieces of their `f_b`

- `LinnikCGLPhi.integral_abs_iteratedDeriv_phi_le`: `∫|φ_{u′}^{(j)}| ≤ B_j(L, X)` for `L, X > 0`.
- `LinnikCGLPhi.fourier_phi_le`: The Fourier decay of `φ_{u′}`

#### `LinnikCGLPois8`: The Poisson expansion of `ĝ_a` in residue classes

- `LinnikCGLPois8.poisson_S`: Poisson in residue classes
- `LinnikCGLPois8.fourier_ga_poisson`: `ĝ_a` by Poisson in residue classes

#### `LinnikCGLPoisson`: The Poisson expansion of the Gram entries in residue classes

- `LinnikCGLPoisson.poisson_scaled`: Poisson summation, scaled
- `LinnikCGLPoisson.sum_colsP_residue`: A finite sum over `colsP N` by residue classes
- `LinnikCGLPoisson.gram_poisson`: The Poisson expansion of a Gram entry in residue classes

#### `LinnikCGLProd`: A product of three `ĥ`s as an integral over `(v₁, v₂)`

- `LinnikCGLProd.prod_eq_iter`: The substitution
- `LinnikCGLProd.iter_swap`: Fubini
- `LinnikCGLProd.hhat_prod`: A product of three `ĥ`s

#### `LinnikCGLRFact`: Their `I′_{m⃗}` as an integral over `(v₁, v₂)`

- `LinnikCGLRFact.S2_triple`: The residue sums of a triple
- `LinnikCGLRFact.sum_Qk`: The sum over the triples of points, at one `(v₁, v₂)`
- `LinnikCGLRFact.Ip_eq`: Their `I′_{m⃗}` as an integral over `(v₁, v₂)`

#### `LinnikCGLRam`: The Ramanujan sum's bound and the decay of `J` (the `S₃` side)

- `LinnikCGLRam.norm_Cq_le`: The Ramanujan sum's bound
- `LinnikCGLRam.Jk_decay`: The decay of `J`
- `LinnikCGLRam.Jk_eq_zero_of`: `J(v₁, v₂, λ) = 0` unless `v₁, v₂ ∈ (1/2, 2)`.

#### `LinnikCGLRefl0`: The reflection of the principal Gram entries

- `LinnikCGLRefl0.reflect_gram0`: The principal reflection
- `LinnikCGLRefl0.norm_gram_le0`: A principal Gram entry, bounded through its reflection

#### `LinnikCGLReflect`: The reflection of the Gram entries

- `LinnikCGLReflect.norm_Phi_le_far`: The reflection factor far left
- `LinnikCGLReflect.LFunction_reflected`: The reflected `L`-function
- `LinnikCGLReflect.shift_of_bound`: A contour shift
- `LinnikCGLReflect.reflect_gram`: The reflection of the Perron integral
- `LinnikCGLReflect.gram_reflect`: The Gram entries reflected

#### `LinnikCGLRt`: Their `R̃` and the inner integral of Proposition 7.2

- `LinnikCGLRt.local_le_Rt_sq`: `R̃` controls the local second moment
- `LinnikCGLRt.inner_le`: The inner `v₂` integral by Cauchy–Schwarz
- `LinnikCGLRt.Vr_inner_le`: The inner integral of their Proposition 7.2

#### `LinnikCGLS2`: `CGLS2`

- `LinnikCGLS2.LSX_le`: The large-sieve factor as a power
- `LinnikCGLS2.Bmax_le`: The tail bound as a power of `P`
- `LinnikCGLS2.s2_main`: The main case of `CGLS2`
- `LinnikCGLS2.cgls2`: `CGLS2` holds *paper* ([note](../formalisations/chen-gupta-li-density.md))

#### `LinnikCGLS23`: The off-diagonal of the cubic trace as Chen–Gupta–Li's `S₂ + S₃`

- `LinnikCGLS23.third_of_s23`: `CGLThird` from the two hypotheses

#### `LinnikCGLS3`: Their Proposition 11.1, `CGLS3` from `CGLP81` and `CGLT101`

- `LinnikCGLS3.cgls3`: Their Proposition 11.1 at one point per character
- `LinnikCGLS3.prop31_pt`: Their Proposition 3.1 at one point per character, from their Proposition 8.1 and Heath-Brown's Theorem 10.1

#### `LinnikCGLSep`: Separated points, and the fractions of their Lemma 10.9

- `LinnikCGLSep.log_sep`: The separation in `log`
- `LinnikCGLSep.sum_cube_le`: A finite exponential sum at separated points ([note](../formalisations/chen-gupta-li-density.md))

#### `LinnikCGLSig2`: Their `Σ_II` expanded, and their `Σ₂` by Poisson summation

- `LinnikCGLSig2.sum_psi_norm_Phi_sq_le`: Their `Σ_II`, expanded
- `LinnikCGLSig2.norm_S2_le`: For `q ≥ 1` and `N₀ > 0`, `|S₂(k₀, x)| ≤ N₀Σ_k|ψ̂₀(N₀(k − x + k₀/q))|`, a convergent series.

#### `LinnikCGLStep`: The density step from Chen–Gupta–Li's Proposition 3.1, with parameters

- `LinnikCGLStep.block_bin_cgl`: One dyadic block and one bin, by Chen–Gupta–Li's estimate
- `LinnikCGLStep.class1_cgl`: The polynomial class with Chen–Gupta–Li's estimate on `[lo, hi]`
- `LinnikCGLStep.count_cgl`: The range `[lo, hi]`

#### `LinnikCGLSteps`: Chen–Gupta–Li's Proposition 3.1 at every point of `[5/7, 131/168]`: 30 density steps with the exponent

- `LinnikCGLSteps.charDensity_s0`: Chen–Gupta–Li's Proposition 3.1 on `[5 / 7, 1201 / 1680]`, density step 0 *paper* ([note](../formalisations/chen-gupta-li-density.md))
- `LinnikCGLSteps.charDensity_s29`: Chen–Gupta–Li's Proposition 3.1 on `[163 / 210, 131 / 168]`, density step 29 *paper*
- `LinnikCGLSteps.charDensity_inT`: Ingham's last step at `ε = 1/400000` *paper* ([note](../formalisations/chen-gupta-li-density.md))

#### `LinnikCGLSym`: The support of `J` in `v₂/v₁`, and the cyclic symmetry of `I′` (the `S₃` side)

- `LinnikCGLSym.prop71r`: Their Proposition 7.1 with the support of `J` in `v₂/v₁` kept ([note](../formalisations/chen-gupta-li-density.md))
- `LinnikCGLSym.Ip_cyc`: The cyclic symmetry
- `LinnikCGLSym.sum_le_three_mul`: The reduction to `|m₂|` largest

#### `LinnikCGLT101`: Their Theorem 10.1 (Heath-Brown) displayed, and their Lemma 10.6 (the `S₃` side)

- `LinnikCGLT101.sum_sq_R2_eq`: The square of `R₂`, expanded
- `LinnikCGLT101.lemma106`: Their Lemma 10.6

#### `LinnikCGLTail`: The terms `|n| > N₀` of their `Σ_II` and the range `|ξ| > X` of `ĝ_a`, by the decay premise

- `LinnikCGLTail.sum_integral_Phi_tail_le`: The terms `|n| > N₀`
- `LinnikCGLTail.setIntegral_ga_tail_le`: The range `|ξ| > X`

#### `LinnikCGLTrace`: Chen–Gupta–Li's `S₃` at one point per character (the `S₃` side)

- `LinnikCGLTrace.S3_eq_cube`: `S₃` as a cubic trace
- `LinnikCGLTrace.Em_eq`: A Gram entry less its main term
- `LinnikCGLTrace.S3_eq_Fm`: Chen–Gupta–Li's `S₃` at one point per character

#### `LinnikCGLTrunc`: The truncation in `m` and their `I′_{m⃗}` (the `S₃` side)

- `LinnikCGLTrunc.sum_FmT_cube`: The truncated cubic trace as a sum of their `I′`
- `LinnikCGLTrunc.norm_Fm_sub_FmT_le`: The tail beyond `M`
- `LinnikCGLTrunc.S3_trunc`: Their (7.1) at one point per character, before the triangle inequality

#### `LinnikChar`: The bound for one character with the weight `e^{−n/x}`

- `Linnik.perron_exp`: Perron's formula for `e^{−n/x}`
- `Linnik.logDeriv_LFunction_le`: `L′/L(·, χ)` where `L(·, χ)` has no zero in one disc
- `Linnik.norm_Sx_le`: The bound for one character

#### `LinnikDeduction`: Linnik's theorem from a density estimate over the characters mod `q`

- `Linnik.totient_mul_SAP`: Orthogonality
- `Linnik.re_Sx_one_ge`: The trivial character
- `Linnik.SAP_le_of_noPrime`: A class with no prime up to `Y`
- `Linnik.error_le`: The characters other than the trivial one
- `Linnik.total_le`: The sizes
- `Linnik.prime_in_class`: A prime in the class up to `10x log x`
- `Linnik.linnik_of_charDensity`: Linnik's theorem from a density estimate over the characters mod `q` *paper*
- `Linnik.charDensity_twelve`: The trivial density from the half-plane
- `Linnik.linnik_twelve`: Linnik's theorem with exponent `12 + η`, from the half-plane alone *paper*

#### `LinnikDensity`: Density over the characters mod `q` from a bound on the critical line

- `LinnikDensity.class1_count`: The polynomial class ([note](../formalisations/ingham-density.md))
- `LinnikDensity.class2_count`: The integral class
- `LinnikDensity.count_nontrivial`: The two classes at one modulus
- `LinnikDensity.charDensity_of_LBound`: Density over the characters from a uniform critical-line bound
- `LinnikDensity.charDensity_of_critBound`
- `LinnikDensity.linnik_of_critBound`: Linnik's theorem from a uniform critical-line bound

#### `LinnikDetect`: Zero detection for `L(s, χ)`, `χ ≠ 1`

- `LinnikDetect.LSeries_aXχ`: `Σ χ(n)a_n n^{−s} = M_X(s, χ)L(s, χ)` on `Re s > 1`.
- `LinnikDetect.detect_identityχ`: The identity at a zero
- `LinnikDetect.dichotomy`: The dichotomy at a zero ([note](../formalisations/ingham-density.md))

#### `LinnikDual`: The dual sums as polynomials at the points of the first character, and the kernel of a pair

- `LinnikReflect.pair_kernel_one`: The kernel on the first line
- `LinnikReflect.pair_kernel_two`: The kernel on the second line

#### `LinnikFE`: The functional equation of `L(s, χ)` on vertical lines

- `LinnikFE.rootNumber_inv`: `ε(χ⁻¹) = conj ε(χ)`.
- `LinnikFE.rootNumber_mul_inv`: For primitive `χ`, `ε(χ)ε(χ⁻¹) = 1`
- `LinnikFE.norm_rootNumber`: `|ε(χ)| = 1` for primitive `χ`
- `LinnikFE.norm_Gamma_mul_sin_le`: `|Γ(σ + it)sin(π(σ + it)/2)| ≤ 3(e⁴|σ + it|)^{σ − 1/2}` for `σ ≥ 1/2` ( `Subconvexity.norm_Gamma_mul_le_of`, as its `norm_Gamma_mul_cos_le`).
- `LinnikFE.norm_LFunction_one_sub_le`: The left line from the right one, for `L(s, χ)`

#### `LinnikFourth`: The hybrid fourth moment of `L(½ + it, χ)` over the characters mod `q`

- `LinnikFourth.norm_LFunction_four_le`: `|L(1/2 + it, χ)|⁴ ≤ 2|D(1/2 + it, χ)|² + 2|D(1/2 − it, χ⁻¹)|²` ([note](../formalisations/hybrid-fourth-moment.md))
- `LinnikFourth.sum_norm_Pd_sq_le`: Large values of `P` at one point per character ([note](../formalisations/hybrid-fourth-moment.md))
- `LinnikFourth.afeJ_split`: The split of `J` ([note](../formalisations/hybrid-fourth-moment.md))
- `LinnikFourth.sum_norm_afeD_sq_le`: The second moment of `D` at one modulus ([note](../formalisations/hybrid-fourth-moment.md))
- `LinnikFourth.fourth_moment_primitive`: The hybrid fourth moment at one modulus, for primitive characters ([note](../formalisations/hybrid-fourth-moment.md))
- `LinnikFourth.fourth_moment`: The hybrid fourth moment over the characters mod `q` *paper* ([note](../formalisations/hybrid-fourth-moment.md))

#### `LinnikG7`: Linnik's theorem with exponent `2.3334 + ε` from the curve `g7d`, by the classical deduction

- `LinnikG7.charDensity_g7d`: The density estimate of the curve `g7d` *paper*
- `LinnikG7.linnik_g7d`: Linnik's theorem with exponent `11667/5000 + η` *paper* ([note](../formalisations/chen-gupta-li-density.md))

#### `LinnikGRH`: GRH for every Dirichlet L-function gives the density hypothesis `CharDensity 2 0 1`, and so Linnik's exponent `2 + η`

- `LinnikGRH.charDensity_two_of_GRH`: GRH for every Dirichlet character gives `Linnik.CharDensity 2 0 1`
- `LinnikGRH.linnik_two_of_GRH`: The consequence

#### `LinnikGammaRatio`: Ratios of `Γ` on vertical lines, and the functional equation reflected to the modulus `q`

- `LinnikReflect.LFunction_eq_reflect`: The functional equation, reflected to the modulus `q`

#### `LinnikHalf`: The partial-summation bound for `L(½ + it, χ)` and Linnik's exponent `4 + η`

- `LinnikDensity.LFunction_split`: The split at `M`
- `LinnikDensity.norm_LFunction_half_le`: The partial-summation bound
- `LinnikDensity.critBoundχ_half`: `CritBoundχ (1/2)`, with constant `11`.
- `LinnikDensity.linnik_four`: Linnik's theorem with exponent `4 + η`

#### `LinnikHuxStep`: A step of Huxley's bound with parameters

- `LinnikHuxStep.class1_gen`: The polynomial class with Huxley's estimate on `[lo, hi]`
- `LinnikHuxStep.count_gen`: The range `[lo, hi]`
- `LinnikHuxStep.charDensity_gen`: A density estimate over the characters mod `q` with exponent `A` on `[lo, hi]` *paper* ([note](../formalisations/huxley-density.md))
- `LinnikHuxStep.charDensity_step'`: The step from the parameters ([note](../formalisations/huxley-density.md))

#### `LinnikHuxStepY`: The step of Huxley's bound with the detector's height as a parameter, class II empty under the Weyl bound

- `LinnikHuxStepY.charDensity_genY`: A density estimate over the characters mod `q` with exponent `A` on `[lo, hi]`, class II empty under the Weyl bound

#### `LinnikHuxley`: The power trick on `23/29 ≤ σ ≤ 11/12`, and Linnik's exponent `87/35 + η`

- `LinnikHuxley.power_count`: Large values of a power, one point per character
- `LinnikHuxley.class2_count_small`: The integral class with a short mollifier
- `LinnikHuxley.class1_huxley`: The polynomial class with powers
- `LinnikHuxley.count_huxley`: The range `23/29 ≤ σ ≤ 11/12`
- `LinnikHuxley.charDensity_huxley`: A density estimate over the characters mod `q` with exponent `87/35`
- `LinnikHuxley.linnik_eighty_seven_thirty_fifths`: Linnik's theorem with exponent `87/35 + η`, with no hypothesis

#### `LinnikHybrid`: The hybrid mean value over the characters mod `q`

- `LinnikHybrid.mean_value_row`: The mean value theorem with a row bound ([note](../formalisations/mean-values.md))
- `LinnikHybrid.sum_chars_norm_sq_le`: Orthogonality ([note](../formalisations/mean-values.md))
- `LinnikHybrid.mean_value_chars`: The hybrid mean value *paper* ([note](../formalisations/mean-values.md))
- `LinnikHybrid.large_values_chars`: Large values at one point per character *paper* ([note](../formalisations/mean-values.md))
- `LinnikHybrid.large_values_chars_off`: Large values off the line at one point per character ([note](../formalisations/hybrid-fourth-moment.md))

#### `LinnikIngham`: Ingham's density estimate over the characters mod `q`, and Linnik's exponent `36/13 + η`

- `LinnikIngham.class2_count_ingham`: The integral class, Ingham's way ([note](../formalisations/ingham-density.md))
- `LinnikIngham.count_nontrivial_ingham`: The two classes at one modulus, Ingham's way
- `LinnikIngham.charDensity_ingham`: Ingham's density estimate over the characters mod `q`
- `LinnikIngham.linnik_thirtysix_thirteenths`: Linnik's theorem with exponent `36/13 + η`, with no hypothesis *paper*

#### `LinnikInghamC`: Ingham's density estimate with the detector's `c` as a parameter (a staircase below `3/4`)

- `LinnikInghamC.charDensity_ingham_c`: Ingham's density estimate with exponent `2 + 4c + 4ε` on `[1/2 + δ₀, σ₂]` *paper* ([note](../formalisations/ingham-density.md))

#### `LinnikLargeValues`: A large-values estimate of Huxley's shape over the characters mod `q`

- `LinnikReflect.kernel_sum_le`: The kernel sum of the Halász–Montgomery inequality
- `LinnikReflect.huxley_large_values`: Huxley's large-values estimate over the characters mod `q` ([note](../formalisations/huxley-density.md))

#### `LinnikLindelof`: A Lindelöf bound for `L(s, χ)` on `Re s > 11/12`, uniformly in the modulus

- `LinnikLindelof.norm_LFunction_le_zeta32`: `‖L(s, χ)‖ ≤ ζ(3/2)` on `Re s ≥ 3/2`.
- `LinnikLindelof.inv_norm_LFunction_le_zeta32`: `‖L(s, χ)‖⁻¹ ≤ ζ(3/2)` on `Re s ≥ 3/2`, from `1/L(s, χ) = Σ χ(n)μ(n)n^{−s}`.
- `LinnikLindelof.logDeriv_le_interp`: The interpolated bound on `L′/L`
- `LinnikLindelof.lindelof`: A Lindelöf bound for `L(s, χ)`, uniformly in the modulus *paper* ([note](../formalisations/halasz-montgomery.md))

#### `LinnikMoment`: Third-moment bounds for the largest singular value

- `LinnikMoment.moment_three`: The simple bound at `r = 3`
- `LinnikMoment.moment_three_chars`: The simple bound at `r = 3` over the characters mod `q`
- `LinnikMoment.refined_moment`: Chen–Gupta–Li's Lemma 4.2
- `LinnikMoment.refined_moment_cube`: Lemma 4.2 cubed
- `LinnikMoment.refined_moment_chars`: Chen–Gupta–Li's Lemma 4.2 over the characters mod `q`

#### `LinnikOffDiag`: `L(s, χ)` on the line `Re s = 1/12 − δ` and the off-diagonal sums

- `LinnikOffDiag.left_line`: The left line for every character `χ ≠ 1`, uniformly in the modulus
- `LinnikOffDiag.norm_offK_le`: The off-diagonal bound *paper* ([note](../formalisations/halasz-montgomery.md))

#### `LinnikPoints`: Large values at several points per character

- `LinnikPoints.large_values_points`: Large values at several points per character

#### `LinnikPower`: The divisor bound, powers of Dirichlet polynomials and the Halász–Montgomery inequality

- `LinnikPower.card_divisors_le`: The divisor bound
- `LinnikPower.pv_pow`: The power of a Dirichlet polynomial ([note](../formalisations/huxley-density.md))
- `LinnikPower.hm_duality`: The Halász–Montgomery duality inequality over the characters mod `q` *paper* ([note](../formalisations/halasz-montgomery.md))

#### `LinnikStairs7`: The staircase of the Weyl-conditional route (Ingham steps on `[4/7, 5/7]`, Huxley's on `[16/21, 11/12]`)

- `LinnikStairs7.charDensity_in7_0`: Ingham's step `0` *paper* ([note](../formalisations/ingham-density.md))
- `LinnikStairs7.charDensity_in7_18`: Ingham's step `18` *paper* ([note](../formalisations/ingham-density.md))
- `LinnikStairs7.charDensity_hx7_5`: Huxley's step `5` *paper* ([note](../formalisations/huxley-density.md))
- `LinnikStairs7.charDensity_hx7_19`: Huxley's step `19` *paper*
- `LinnikStairs7.charDensity_hy_0`: The step `0` above `5/6`, under `PYWeyl`
- `LinnikStairs7.charDensity_hy_top`: The last step, extended to `σ ≤ 1`, under `PYWeyl`

#### `LinnikStep`: A step of Huxley's bound, exponent `101/50` on `5/6 ≤ σ ≤ 11/12`

- `LinnikStep.class1_step`: The polynomial class with Huxley's estimate on `5/6 ≤ σ ≤ 11/12`
- `LinnikStep.count_step`: The range `5/6 ≤ σ ≤ 11/12`
- `LinnikStep.charDensity_step`: A density estimate over the characters mod `q` with exponent `101/50` on `5/6 ≤ σ ≤ 1` *paper* ([note](../formalisations/huxley-density.md))

#### `LinnikSubconvex`: `|L(1/2 + it, χ)| ≪ (q(|t| + 2))^{5/24+ε}` uniformly in `q`, and Linnik's exponent `17/6 + η`

- `LinnikSubconvex.primitive_bound`: Subconvexity for primitive characters, uniformly in the modulus
- `LinnikSubconvex.prod_primeFactors_le`: `∏_{p | q}(1 + p^{−1/2}) ≤ 2^{⌈e^{1/ε}⌉}q^ε` for `q ≥ 1` and `ε > 0`
- `LinnikSubconvex.critBoundχ`: The bound on the critical line for every character `χ ≠ 1`, uniformly in the modulus
- `LinnikSubconvex.linnik_seventeen_sixths`: Linnik's theorem with exponent `17/6 + η`, with no hypothesis

#### `LinnikTwelve`: The power trick on `3/4 ≤ σ ≤ 11/12` with the estimate, and Linnik's exponent `12/5 + η`

- `LinnikTwelve.class1_twelve`: The polynomial class with Huxley's estimate
- `LinnikTwelve.count_twelve_fifths`: The range `3/4 ≤ σ ≤ 11/12`
- `LinnikTwelve.charDensity_twelve_fifths`: A density estimate over the characters mod `q` with exponent `12/5`
- `LinnikTwelve.linnik_twelve_fifths`: Linnik's theorem with exponent `12/5 + η`, with no hypothesis *paper*

#### `LinnikTwelveBins`: One block and one bin by the large-values estimate, and Ingham's method at `c = 1/10`

- `LinnikTwelve.block_bin_hux`: One dyadic block and one bin, by Huxley's estimate
- `LinnikTwelve.count_middle_c10`: The range `7/12 ≤ σ ≤ 3/4` at `Q = q(T + 6)`

#### `LinnikTwelveSizes`: One block and one bin as a power of `Q` on `3/4 ≤ σ ≤ 11/12`

- `LinnikTwelve.term1_le`: The first term
- `LinnikTwelve.term2_le`: The second term

#### `LinnikWeighted`: The Halász–Montgomery inequality with a smooth weight, its kernel through the primitive

- `LinnikReflect.hm_duality_W`: The Halász–Montgomery inequality with the weight `W(n) = e^{−n/U} − e^{−2n/U}` ([note](../formalisations/halasz-montgomery.md))
- `LinnikReflect.norm_hTerm_le_reflect`: The reflected kernel bound for one pair ([note](../formalisations/halasz-montgomery.md))
- `LinnikReflect.huxley_core`: The product trick against the large values

#### `LinnikWeyl`: The integral class is empty under a pointwise bound on the critical line

- `LinnikWeyl.class2_empty`: The integral class is empty under a pointwise bound

#### `LinnikWeylBridge`: `PYWeyl` contains `WeylBound`: the Weyl bound for every character gives the Weyl bound for ζ

- `LinnikWeylBridge.weylBound_of_PYWeyl`: `LinnikWeyl.PYWeyl` (all moduli, jointly in `q` and `t`) gives `CrossCriteria.WeylBound` (ζ alone), by its case `q = 1`.

#### `Littlewood`: Littlewood's bounds for `L(1, χ)` at the real characters

- `Littlewood.norm_LSeries_le_of_sum_le`: Partial summation for an L-series
- `Littlewood.logDeriv_le_loglog_of`: The log-derivative on `(1, 2]`, uniformly in the modulus, from a bound on `ψ(x, χ)`
- `Littlewood.logDeriv_le_loglog`: `L′/L(σ, χ) ≪ log log q` on `(1, 2]`
- `Littlewood.norm_LFunction_le_real`: `|L(σ, χ)| ≤ σ/(σ − 1)` and `1/|L(σ, χ)| ≤ σ/(σ − 1)` for `σ > 1`, from the partial sums of `χ` and of `χμ`, each at most `t` in absolute value.
- `Littlewood.abs_log_norm_LFunction_one_le_of`: Littlewood's argument
- `Littlewood.abs_log_norm_LFunction_one_le`: Littlewood's bounds for `L(1, χ)`
- `Littlewood.norm_LFunction_one_le`: `L(1, χ) ≪ log log q`
- `Littlewood.norm_LFunction_one_ge`: `L(1, χ) ≫ 1/log log q`
- `Littlewood.norm_logDeriv_one_le`: `L′/L(1, χ) ≪ log log q`

#### `LogDerivDisc`: The log-derivative of a function with no zero in a half-plane, by the disc step

- `LogDerivDisc.disc_point_ball`: The disc step
- `LogDerivDisc.logDeriv_le_ball`: The log-derivative of an entire function with no zero in one disc
- `LogDerivDisc.logDeriv_le_uniform_of`: The log-derivative of an entire function in a zero-free half-plane, with its constants

#### `LogDerivKV`: R4a: the log-derivative bound on the Korobov–Vinogradov region

- `LogDerivKV.logDerivBnd_KV`: R4a: `ζ'/ζ = O((log|t|)³)` on the Korobov–Vinogradov region

#### `LucasWitness`: Lucas's primality test with small witnesses

- `LucasWitness.prime_iff_exists_lucas_le_rpow`: Lucas's test with small witnesses
- `LucasWitness.prime_iff_exists_lucas_le_safe`: Lucas's test for `2r + 1` in polynomial time

#### `MediumPNTW`: PNT+'s contour bounds for a zero-free region of general width

- `MediumPNTW.GenPNTW'`: Generic PNT from a width-`D` region, with the small-height abscissa given
- `MediumPNTW.GenPNTWNoEps`: Generic PNT from a width-`D` region, without `1/ε` on the left
- `MediumPNTW.GenPNTW`: Generic PNT from a width-`D` region

#### `MertensChi`: Mertens' function twisted by a character, uniformly in the modulus

- `MertensChi.LSeries_fχμ`: `L(χμ, s) = 1/L(s, χ)` on `Re s > 1` (Mathlib's `LSeries.mul_mu_eq_one`).
- `MertensChi.norm_sum_le_of`: Perron's formula with a Lindelöf bound
- `MertensChi.norm_sum_le`: Mertens' function twisted by a character, uniformly in the modulus
- `MertensChi.isBigO`: For one character `χ ≠ 1`

#### `MertensExponent`: Mertens' function in a zero-free half-plane, and `Θ` as its exponent

- `MertensExponent.mertens_isBigO_of_zeroFree`: Mertens' function in a zero-free half-plane
- `MertensExponent.mertens_isBigO_eleven_twelfths`: `M(x) = O(x^{11/12+η})`
- `MertensExponent.mertens_isBigO_Theta`: `M(x) = O(x^{Θ+η})`
- `MertensExponent.mertens_omega_Theta`: `M(x) = Ω±(x^{Θ−η})`
- `MertensExponent.rh_iff_Theta_eq_half`: `RH ⟺ Θ = ½`
- `MertensExponent.rh_iff_mertens`: Littlewood's criterion
- `MertensExponent.limsup_mexpo`: The exponent of Mertens' function is `Θ`
- `MertensExponent.moebius_tendsto_of_Theta_lt`: `Σ μ(n) n^{−s}` converges for `Re s > Θ`
- `MertensExponent.moebius_not_tendsto_of_lt_Theta`: `Σ μ(n) n^{−s}` diverges for `Re s < Θ`
- `MertensExponent.moebiusAbscissa_eq_Theta`: The abscissa of convergence of `Σ μ(n) n^{−s}` is `Θ`

#### `MillerTest`: Miller's primality test with small bases

- `MillerTest.strongProbablePrime_of_prime`: Every odd prime passes
- `MillerTest.exists_witness_le`: Miller's test with small bases
- `MillerTest.prime_iff_forall_strongProbablePrime`: Miller's test, deterministic

#### `PNTKV`: The prime number theorem with the Korobov–Vinogradov error term

- `PNTKV.PNT_KV`: The prime number theorem with the Korobov–Vinogradov error term

#### `PNTProgressions`: The prime number theorem modulo the divisors of `24`

- `PNTProgressions.sum_dvd_le_log`: `Σ_{n ≤ N, p ∣ n} Λ(n) ≤ log N` for a prime `p`
- `PNTProgressions.sum_not_coprime_le`: `Σ_{n ≤ N, (n, q) > 1} Λ(n) ≤ ω(q) log N` for `q ≠ 0`.
- `PNTProgressions.psiChi_one`: `ψ(x, χ)` for the trivial character mod `q`
- `PNTProgressions.psiAP_eq_sum`: Orthogonality
- `PNTProgressions.psiAP_isBigO`: The prime number theorem in progressions modulo every `q`

#### `PsiExponent`: The exponent of the error in the prime number theorem

- `PsiExponent.Theta_le`: `Θ ≤ 11/12`
- `PsiExponent.half_le_Theta`: `½ ≤ Θ`
- `PsiExponent.zeta_ne_zero_of_Theta_lt`: `ζ(s) ≠ 0` for `Re s > Θ`.
- `PsiExponent.psi_isBigO_Theta`: The upper half
- `PsiExponent.psi_omega_Theta`: The lower half
- `PsiExponent.limsup_expo`: The exponent of the error in the prime number theorem is `Θ`

#### `QuadClassNumber`: Class numbers, the least inert and split primes and the Euler–Kronecker constant of a quadratic field

- `QuadClassNumber.classNumber_ge`: The class number of an imaginary quadratic field, from below
- `QuadClassNumber.classNumber_le`: The class number of an imaginary quadratic field, from above
- `QuadClassNumber.classNumber_ge_sqrt`: Door 4(b)'s bound for imaginary quadratic fields
- `QuadClassNumber.regulator_mul_classNumber_ge`: The class number and regulator of a real quadratic field, from below
- `QuadClassNumber.regulator_mul_classNumber_le`: The class number and regulator of a real quadratic field, from above
- `QuadClassNumber.regulator_mul_classNumber_ge_sqrt`: Door 4(b)'s bound for real quadratic fields
- `QuadClassNumber.classNumber_ge_loglog`: Door 4(b)'s bound for imaginary quadratic fields, in the form `c√|D_K|/log log |D_K|`
- `QuadClassNumber.regulator_mul_classNumber_ge_loglog`: Door 4(b)'s bound for real quadratic fields, in the form `c√D_K/log log D_K`
- `QuadClassNumber.exists_inert_le`: An inert prime below `C_A(log(|D_K| + 2))^A`
- `QuadClassNumber.exists_split_le`: A split prime below `C_A(log(|D_K| + 2))^A`
- `QuadClassNumber.exists_inert_le_13`: An inert prime below `10²⁹⁸(log(|D_K| + 2))¹³`
- `QuadClassNumber.exists_split_le_13`: A split prime below `10²⁹⁸(log(|D_K| + 2))¹³`
- `QuadClassNumber.eulerKronecker`: The Euler–Kronecker constant of a quadratic field

#### `QuadKronecker`: The Kronecker character of a quadratic field

- `QuadKronecker.jacBot_natCast`
- `QuadKronecker.jacTop_natCast`
- `QuadKronecker.jacobiSym_natAbs`: For `d ≡ 1 (mod 4)` and an odd prime `p`, `J(p | |d|) = J(d | p)`.
- `QuadKronecker.jacobiSym_two_natAbs`: For `d ≡ 1 (mod 4)`, `J(2 | |d|)` is `1` if `d ≡ 1 (mod 8)` and `−1` if `d ≡ 5 (mod 8)`.
- `QuadKronecker.dedekindZeta_eq`: `ζ_K = ζ·L(·, χ)`
- `QuadKronecker.ne_one_of_eq`: A character in a factorization `ζ_K = ζ·L(·, χ)` is not trivial
- `QuadKronecker.type_one`: The splitting law, `d ≡ 1 (mod 4)`
- `QuadKronecker.type_two_three`: The splitting law, `d ≡ 2, 3 (mod 4)`
- `QuadKronecker.exists_kronecker`: The Kronecker character of a quadratic field
- `QuadKronecker.classNumber_formula`: The class number formula for every imaginary quadratic field, with its Kronecker character

#### `QuadRing`: The ring of integers of a quadratic field

- `QuadRing.int_of_mul_sq`: If `d` is squarefree and `d r² ∈ ℤ`, then `r ∈ ℤ`.
- `QuadRing.exists_eq`: Every element of `K` is `a + bs`
- `QuadRing.minpoly_eq`: The minimal polynomial of `a + bs`, `b ≠ 0`, is `X² − 2aX + (a² − db²)`
- `QuadRing.isIntegral_iff`: Integrality of `a + bs`
- `QuadRing.discr_eq_of_basis`: If `(1, θ)` is a `ℤ`-basis of `𝓞 K` with `θ² = c + eθ`, then `D_K = 4c + e²`
- `QuadRing.span_θ₁`: Every integer of `K` is `u + vθ`
- `QuadRing.adjoin_θ₁`: `𝓞 K = ℤ[θ]`
- `QuadRing.discr_θ₁`: The discriminant is `d`
- `QuadRing.minpoly_θ₁`: The minimal polynomial of `θ = (1 + s)/2` over `ℤ` is `X² − X − (d − 1)/4`
- `QuadRing.span_θ₂`
- `QuadRing.adjoin_θ₂`: `𝓞 K = ℤ[s]`
- `QuadRing.discr_θ₂`: The discriminant is `4d`
- `QuadRing.minpoly_θ₂`: The minimal polynomial of `s` over `ℤ` is `X² − d`
- `QuadRing.exists_sqrt`: Every quadratic field contains a square root `s` of a squarefree integer `d ≠ 1`

#### `QuadSplit`: The splitting law in a quadratic field

- `QuadSplit.split_of_factors`
- `QuadSplit.ramified_of_factors`
- `QuadSplit.inert_of_factors`
- `QuadSplit.split_of_root`: The splitting law from the roots mod `p`
- `QuadSplit.ramified_of_root`
- `QuadSplit.inert_of_no_root`
- `QuadSplit.ramified_of_dvd₂`: `p ∣ d`
- `QuadSplit.ramified_two₂`: `2` ramifies.
- `QuadSplit.split₂`: `p` odd, `p ∤ d`, `d` a square mod `p`
- `QuadSplit.inert₂`: `d` not a square mod `p`
- `QuadSplit.ramified_of_dvd₁`: `p` odd, `p ∣ d`
- `QuadSplit.split₁`: `p` odd, `p ∤ d`, `d` a square mod `p`
- `QuadSplit.inert₁`: `d` not a square mod `p`
- `QuadSplit.split_two₁`: `d ≡ 1 (mod 8)`
- `QuadSplit.inert_two₁`: `d ≡ 5 (mod 8)`

#### `ShortCharSums`: Short character sums

- `ShortCharSums.norm_sum_le`: Character sums, uniformly in the modulus
- `ShortCharSums.norm_sum_le_rpow`: Short character sums
- `ShortCharSums.norm_sum_le_mul`: Short character sums are `o(X)`
- `ShortCharSums.card_squares_sub_le`: Quadratic residues in short intervals

#### `ShortKV`: Primes in short intervals: the Korobov–Vinogradov input

- `ShortKV.zeroFreeXi_KV`: The Korobov–Vinogradov region as `ZeroFreeXi (3/4)` ([note](../formalisations/zeta-density.md))

#### `ShortPrimesHalfPlane`: The zero-free region `ZeroFreeXi α` from the zero-free half-plane instead of Korobov–Vinogradov

- `ShortPrimesHalfPlane.zeroFreeXi_of_halfplane`: The zero-free half-plane gives `ZeroFreeXi α` for every `α` (here `α < 1` is what `short_primes_of_density` takes), with no Korobov–Vinogradov input. ([note](../formalisations/zeta-density.md))

#### `SieveBox`: The share of a box of prime intervals

- `SieveRough.evLe_box_tr`: An interval's `Σ 1/p` is at most the trapezoid bound `trB(a, w)` of `log(1 + w/a)`, up to `o(1)`. *paper*
- `SieveRough.evLe_box_ex`: An interval's `log x · Σ 1/(p log p)` is at most `exB(a, w) = w·DEN/(a(a + w))`, up to `o(1)`. *paper*
- `SieveRough.shareBox`: The share of a box *paper*

#### `SieveBrun`: Brun's sieve in product form, abstractly

- `SieveBrun.bonferroni`: Bonferroni's inequalities
- `SieveBrun.fundamental`: The fundamental lemma in product form, abstractly *paper* ([note](../formalisations/harman-sieve.md))
- `SieveBrun.gap_le`: For even `k_j`, `0 ≤ g ≤ 1` on each `T_j`, `C₀ ≥ 0` with `Σ_{T_j} g ≤ C₀`, and `∏_{T_j} (1 − g) ≥ c₀ > 0` ([note](../formalisations/harman-sieve.md))

#### `SieveBuch`: The decomposition to depth 6, with the certificate's classification

- `SieveBuch.Par.T_eq`: Depth 0 *paper*
- `SieveBuch.Par.I_S1`: Depth 1 *paper*
- `SieveBuch.Par.I_S2`: Depth 2 *paper*
- `SieveBuch.Par.I_S3`: Depth 3 *paper*
- `SieveBuch.Par.I_S4`: Depth 4 *paper*
- `SieveBuch.Par.I_S5`: Depth 5 *paper*
- `SieveBuch.Par.I_S6`: Depth 6 *paper*
- `SieveBuch.Par.I_S3c_vanish`: Depth 3, outside `inKK` *paper*
- `SieveBuch.Par.I_S4c_vanish_lt`: Depth 4, `l > k` *paper*
- `SieveBuch.Par.I_S4c_vanish_reg`: Depth 4, outside the region *paper*
- `SieveBuch.Par.I_S5c_vanish_lt`: Depth 5, `eC b ≥ e_l + H` *paper*
- `SieveBuch.Par.I_S5c_vanish_reg`: Depth 5, outside the region *paper*
- `SieveBuch.Par.I_S6c_vanish_lt`: Depth 6, `c > b` *paper*
- `SieveBuch.Par.I_S6c_vanish_reg`: Depth 6, outside the region *paper*

#### `SieveBuch8`: The decomposition to depth 8

- `SieveBuch.Par.I_S6c`: Depth 6 *paper*
- `SieveBuch.Par.I_S6cle`: Depth 6 *paper*
- `SieveBuch.Par.I_S7`: Depth 7 *paper*
- `SieveBuch.Par.I_S7c`: Depth 7 *paper*
- `SieveBuch.Par.I_S7le`: Depth 7 *paper*
- `SieveBuch.Par.I_S8`: Depth 8 *paper*
- `SieveBuch.Par.I_S7c_vanish_lt`: Depth 7, `d > c` *paper*
- `SieveBuch.Par.I_S8c_vanish_lt`: Depth 8, `f > d` *paper*
- `SieveBuch.Par.I_S7c_vanish_reg`: Depth 7, outside the region *paper*
- `SieveBuch.Par.I_S8c_vanish_reg`: Depth 8, outside the region *paper*
- `SieveBuch.Par.decomp8`: The decomposition's inequality to depth 8 *paper*

#### `SieveCert`: The certificate of the sieve route's loss, checked by the kernel

- `SieveCert.omegaC_le_w`: `ω*` on a box *paper*
- `SieveCert.bound2_ge`: A cell of depth 2 with lower corner `(a, b)` costs at least `omK/K` times the first cell's trapezoid bound and the last cell's `DEN·H/(b(b + H))`. *paper*

#### `SieveCert22000E`: The certificate to depth 8 of the sieve route's loss at `L = 11/5` with `n = 272`: `totalD < K`

- `SieveDeep.totalD_lt_22000E`: The certificate to depth 8 on `grid22000E` *paper*

#### `SieveChain`: Type II for chains of primes

- `SieveChain.sum_rough_tuples`: For `z ≥ 2`, `Y ≥ 1` and `Y < z^{K+1}`, the `z`-rough `k ∈ [1, Y]` are the products of the non-increasing tuples of at most `K` primes at least `z`, the… *paper*
- `SieveChain.typeII_gcmp'`: `typeII_gcmp` (with `RouteOK` and `hII`) for any number `K ≥ 1` of primes.
- `SieveChain.chainTU_bound`: Chains times a rough cofactor in the window *paper*
- `SieveChain.chainTL_bound`: Chains with a product of some of their primes in the window *paper*

#### `SieveChainR`: Type II for chains with part of their product in the reflection of the window

- `SieveChainR.chainTR_bound`: Chains with part of their product in the reflection of the window *paper*

#### `SieveCount`: Type I counts in a residue class

- `SieveCount.card_A`: Type I for `A` *paper*
- `SieveCount.card_B`: Type I for `B` *paper*

#### `SieveCurve7D`: The curve `g7d` and its counts

- `SieveCurve7D.g7d_le_one`: `g7d ≤ 1` *paper*
- `SieveCurve7D.g7d_half` *paper*
- `SieveCurve7D.g7d_le_lin`: `g7d σ ≤ (11667 / 5000)(1 − σ)` for `σ ≤ 1` *paper* ([note](../formalisations/chen-gupta-li-density.md))
- `SieveCurve7D.counts_7d`: The counts of the curve *paper* ([note](../formalisations/chen-gupta-li-density.md))

#### `SieveDecomp`: Families of prime tuples, and Buchstab's identity on them

- `SieveDecomp.buchstab_fam`: Buchstab's identity on a family *paper* ([note](../formalisations/harman-sieve.md))
- `SieveDecomp.famI_cells`: The cells of the prime `t`
- `SieveDecomp.famI_vanish`: A family whose products are at most `N₁` and whose products times their last prime exceed `N₂` contributes `0`

#### `SieveDeep`: The certificate to depth 8: its rule and its decisions

- `SieveDeep.surelyEval4_of_lmask`: A bit of the mask of `l` makes the box `(i, j, k, l)` surely evaluable *paper*
- `SieveDeep.surelyEval5_of_emask`: A bit `b` of the coarse mask of one cell makes the box `(i, j, k, l, b)` surely evaluable *paper*
- `SieveDeep.surelyEval6_of_emask`: A bit `c` of the coarse mask of one cell, or `b + c` of that of two, makes the box `(i, j, k, l, b, c)` surely evaluable *paper*
- `SieveDeep.okIB_of_okD`: The block test is sound *paper*
- `SieveDeep.scheme`: The certificate's scheme of decisions *paper*

#### `SieveDeepCert`: The certificate to depth 8, by parts

- `SieveDeep.totalD_eq_rowsJD`: The certificate's total is `rowsJD 0 n 0 n`.

#### `SieveDeepCost`: The certificate to depth 8: its costs bound the dropped cells' charges

- `SieveDeep.Ch3_le`: The charges below a cell `(i, j)` are at most `SC⁸·refcost` *paper*

#### `SieveDrop`: The dropped terms' `B`-count

- `SieveDrop.drop2_le`: A dropped cell of depth 2 *paper*
- `SieveDrop.corner_le`: A corner cell *paper*
- `SieveDrop.corner_ev`: The corner is `o(x/log x)` *paper*

#### `SieveDrop8`: The dropped terms' `B`-count, to depth 8

- `SieveDrop8.drop4_le'`: A dropped cell of depth 4 *paper*
- `SieveDrop8.drop6_le'`: A dropped cell of depth 6 *paper*
- `SieveDrop8.drop8_le`: A dropped cell of depth 8 *paper*
- `SieveDrop8.trB_le_trapF`: `trB ≤ trapF/SC`. *paper*
- `SieveDrop8.exB_le_lastF`: `exB ≤ lastF/SC`. *paper*
- `SieveDrop8.share4D`: The share of a counted cell of depth 4 *paper*
- `SieveDrop8.share6D`: The share of a counted cell of depth 6 *paper*
- `SieveDrop8.share8D`: The share of a cell of depth 8 of the region *paper*
- `SieveDrop8.E1_le`: The dropped terms' `B`-count
- `SieveDrop8.dT_le_cost`: The dropped sums of a cell `(i, j)` against its cost *paper*
- `SieveDrop8.drop_ev8`: The dropped terms, for large `q`, with the loss as a parameter *paper*

#### `SieveDyadic`: A dyadic partition of unity

- `SieveDyadic.sum_bump`: The dyadic partition of unity

#### `SieveFamily`: Type II families

- `SieveFamily.family_bound`: The bound for a smooth family
- `SieveFamily.Dsum_sharp_le`: A sharp family, explicitly
- `SieveFamily.typeII_sharp_explicit`: A sharp family, with the Type II estimate
- `SieveFamily.typeII_sharp`: The Type II estimate for a sharp family (Lemmas 4′ and 4″), asymptotic form *paper*

#### `SieveGrid22000E`: The grid of the certificate to depth 8 at `L = 11/5` with `n = 272`

- `SieveCert.gridOK22000E` *paper*
- `SieveCert.gridOKC22000E`: The coarse grid `Gc` (`n / 4 = 68` cells) and the facts about it that the deepest levels use. *paper*

#### `SieveHMBin`: Halász–Montgomery for one bin of characters at one height

- `SieveTypeIIHM.dp_eq_pv`: The bridge
- `SieveTypeIIHM.sum_bin_hm`: Halász–Montgomery for one bin at one height *paper* ([note](../formalisations/halasz-montgomery.md))

#### `SieveHMBins`: Proposition 3′ pointwise, by bins, with the Halász–Montgomery bound per bin

- `SieveTypeIIHM.sum_typeII_bins_hm`: Proposition 3′ pointwise, by bins, with the better bound per bin *paper*
- `SieveTypeIIHM.offK_bound`: A uniform kernel bound at `z = 0` *paper*

#### `SieveHMWindow`: The window condition with the Halász–Montgomery branch

- `SieveCurveGlue.affine_corner_bound`: A function affine in each of `w`, `β`, `m` separately is at most its maximum over the corners of a box
- `SieveCurveGlue.windowPieceHM_affine_split`: An affine piece by the Halász–Montgomery branch below `m = 1` and by orthogonality above it
- `SieveCurveGlue.windowPieceHM_const_split`: The piece `g β = A(1 − β)` by `windowPieceHM_affine_split` at `p = A` (as `windowPiece_const`), for `lo ≤ hi` (`hlo`) and the corner inequalities `h1`, `h2`…

#### `SieveLeaf`: The leaves of Buchstab's tree, by the fundamental lemma

- `SieveLeaf.leaf_A`: A leaf, for `A` ([note](../formalisations/harman-sieve.md))
- `SieveLeaf.leaf_B`: A leaf, for `B/φ(q)` ([note](../formalisations/harman-sieve.md))
- `SieveLeaf.leaf_gap`: The relative error of a leaf *paper* ([note](../formalisations/harman-sieve.md))
- `SieveLeaf.prod_primesBelow_le`: Mertens' product bound, in its elementary form *paper* ([note](../formalisations/harman-sieve.md))
- `SieveLeaf.prod_T_le`: The main term of a leaf *paper* ([note](../formalisations/harman-sieve.md))

#### `SieveLeaves`: The leaves' estimates on families of atoms

- `SieveLeaves.TL_spec`: The lower window, on a family of atoms
- `SieveLeaves.TU_spec`: The upper window, on a family of atoms
- `SieveLeaves.TR_spec`: The reflected window, on a family of atoms
- `SieveLeaves.P6_spec`: Proposition 6, on a family of atoms ([note](../formalisations/harman-sieve.md))
- `SieveLeaves.P6IB_spec`: Proposition 6 with the bilinear estimate, on a family of atoms ([note](../formalisations/harman-sieve.md))

#### `SieveLemma1`: Weighted prime sums at a height inside a zero-free rectangle (Lemma 1 of the sieve route, `Λ` form)

- `SieveLemma1.perron_weight`: Perron's formula with a weight `w`
- `SieveLemma1.norm_Sw_le`: Lemma 1 in `Λ` form

#### `SieveMain`: The primes of `(x, 2x]` prime to `q`, for Linnik's theorem by the sieve route

- `SieveMain.TB_ev`: For a route with `RouteOK` and a grid with `GridOK` that fit (`Fits`), and `ε > 0`

#### `SieveMain8`: Linnik's theorem by the sieve route, under the certificate of depth 8

- `SieveMain8.linnik_large8`: Linnik's theorem at `x = q^L`, for large `q`, under the certificate of depth 8 *paper*
- `SieveMain8.linnik_route_lt8`: Linnik's theorem with exponent `L`, under a certificate of depth 8 whose total is below `K` *paper*

#### `SieveOmegaB`: Buchstab's `ω` on `[2, 3]`, and the logarithm's bounds of the certificate's cells

- `SieveOmegaB.log_le_half_sub_inv`: `log y ≤ (y − 1/y)/2` for `y ≥ 1` *paper*
- `SieveOmegaB.omB_le_w1`: The maximum of Buchstab's `ω` on `[2, 3]` *paper*
- `SieveOmegaB.omB_mono`: Buchstab's `ω` increases on `[2, 2.76]` *paper*
- `SieveOmegaB.omB_anti`: Buchstab's `ω` decreases from `2.77` on *paper*
- `SieveOmegaB.lnT_ge`: The table *paper*
- `SieveOmegaB.omF_ge`: `omF` bounds Buchstab's `ω` *paper*

#### `SieveP6Leaves`: Proposition 6 with the bilinear estimate: the large leaves

- `SieveP6Leaves.leaves_chain`: The large leaves of a family, with Brun's weights *paper*

#### `SieveP6Tree`: Proposition 6 with the bilinear estimate: Buchstab's tree on a family

- `SieveP6Tree.tree_chains`: Buchstab's tree on a family, as chains *paper*

#### `SieveP6TreeLeaves`: Proposition 6 with the bilinear estimate: the leaves of the tree

- `SieveP6TreeLeaves.tree_leaves_le`: The leaves of a tree *paper*

#### `SieveP6ib`: Proposition 6 with the bilinear estimate

- `SieveP6ib.prop6ib`: Proposition 6 with the bilinear estimate *paper* ([note](../formalisations/harman-sieve.md))

#### `SieveProp6`: Proposition 6, Harman's fundamental theorem in the form used

- `SieveProp6.leaf_bound`: A leaf *paper* ([note](../formalisations/harman-sieve.md))
- `SieveProp6.prop6`: Proposition 6 *paper* ([note](../formalisations/harman-sieve.md))

#### `SieveQ`: The decomposition at `x = q^L`, and its leaves for large `q`

- `SieveQ.good_of_large`: The decomposition's hypotheses hold for large `q`
- `SieveQ.P6IB_box`: Proposition 6-ib on a box the bilinear rule passes *paper*
- `SieveQ.P6IB_boxes`: Proposition 6-ib, uniformly over finitely many boxes ([note](../formalisations/harman-sieve.md))

#### `SieveQ8`: The leaves of the decomposition to depth 8, for large `q`

- `SieveQ8.leaves_ev8`: The leaves of the decomposition to depth 8, for large `q` *paper*

#### `SieveRanges`: The ranges of Brun's sieve

- `SieveRanges.rng_sum_le`: The prime sums of the ranges `rng A`, `A ≥ 1`, are uniformly bounded

#### `SieveRough`: Rough numbers from above, and the shares of the certificate's cells

- `SieveRough.Psi_le_buchstab`: Buchstab's inequality *paper*
- `SieveRough.super_M`: The supersolution property *paper*
- `SieveRough.psi_le`: Rough numbers from above *paper* ([note](../formalisations/harman-sieve.md))
- `SieveRough.evLe_cell_tr`: On a grid with `GridOK`, the cell's `Σ 1/p` is at most the trapezoid bound `trB(e_k, H) = H(2e_k + H)/(2e_k(e_k + H))` of `log(1 + H/e_k)`, up to `o(1)`. *paper*
- `SieveRough.evLe_cell_ex`: On a grid with `GridOK`, the cell's `log x · Σ 1/(p log p)` is at most `exB(e_k, H) = H·DEN/(e_k(e_k + H))`, the exact `DEN(1/e_k − 1/(e_k + H))`, up to `o(1)`. *paper*
- `SieveRough.share2`: The share of a cell of depth 2
- `SieveRough.share2_of_cand`: `share2` on a candidate cell, on a grid with `GridOK`. *paper* ([note](../formalisations/harman-sieve.md))

#### `SieveRoughTuple`: Rough numbers as tuples of primes

- `SieveRoughTuple.sum_rough_eq`: Rough numbers as tuples of primes

#### `SieveRule`: The certificate under a decomposition rule, over `Finset`

- `SieveCert.ibOK_sound`: The bilinear Type I rule's witnesses *paper* ([note](../formalisations/harman-sieve.md))
- `SieveCert.okIB_cases`: `okIB` passes a box only when `limOK` does, or `ibOK` and `nbOK` do. *paper*

#### `SieveSep`: Separation of smooth comparisons by Fourier inversion over `ℝ^J`

- `SieveSep.sum_sep`: Separation of a finite sum
- `SieveSep.sep_bound`: The bound after separation

#### `SieveSmooth`: The smooth cut-off and its Fourier transform

- `SieveSmooth.indicator_sub_G`: The cut-off against the indicator
- `SieveSmooth.pow_mul_norm_fourier_GC_le`: Decay of the cut-off's Fourier transform
- `SieveSmooth.integrable_fourier_GC`

#### `SieveSpline`: Weights for the bilinear Type I estimate: Parseval for the weight, intervals and splines

- `SieveSpline.what_spl`: The spline's transform
- `SieveSpline.norm_what_spl_tail`: The spline's tail
- `SieveSpline.norm_Ew_spl_le`: `E_w` for a spline
- `SieveSpline.typeIB_spline`: The bilinear Type I estimate with a spline weight *paper*

#### `SieveStops2`: The stops of Buchstab's tree above the threshold

- `SieveStops2.typeII_cmp`: Type II with a list of comparisons
- `SieveStops2.stops2_bound`: The stops above the threshold *paper* ([note](../formalisations/harman-sieve.md))

#### `SieveTree`: Buchstab's tree

- `SieveTree.tree_pt`: The Buchstab tree at one `n` *paper*

#### `SieveTreeStop`: Buchstab's tree with a stopping rule

- `SieveTreeStop.tree_pt_stop`: Buchstab's tree with a stopping rule, at one `n` *paper*

#### `SieveTypeIB`: A bilinear Type I estimate by Parseval's identity

- `SieveTypeIB.sum_bilinear`: The bilinear sum in Fourier form
- `SieveTypeIB.typeIB_bound`: The bilinear Type I estimate *paper*

#### `SieveTypeIBAsym`: The leaves by the bilinear estimate: the asymptotic form

- `SieveTypeIBAsym.leaves_ib`: The leaves by the bilinear estimate, asymptotically *paper*

#### `SieveTypeII`: Parts of the Type II estimate of the sieve route (Proposition 3′, pointwise in the heights)

- `SieveTypeII.sum_chars_dp_sq_le`: Orthogonality (T1) *paper* ([note](../formalisations/mean-values.md))

#### `SieveTypeIIGen`: Parts of the Type II estimate for a curve and a window (Proposition 3′ with parameters)

- `SieveTypeIIGen.card_bin_gen`: The count of a bin of the grid
- `SieveTypeIIGen.prod_MB_le_gen`: The product of Lemma 1's bounds

#### `SieveTypeIIHM`: The bin bound with the Halász–Montgomery branch, and Proposition 3′ for a curve on a window

- `SieveTypeIIHM.bin_bound_pt`: One bin by orthogonality, at one point
- `SieveTypeIIHM.bin_bound_gen_hm`: One bin, with the better bound *paper*
- `SieveTypeIIHM.typeII_gen_hm`: Proposition 3′ for a curve and a window with the Halász–Montgomery branch, pointwise in the heights *paper*

#### `SieveTypeIIU`: Type II families with sharp prime ranges

- `SieveTypeIIU.typeII_unw`: Type II for families with sharp prime ranges *paper*

#### `SieveTypeIIU22000D`: Proposition 3′ at `L = 11 / 5` on the window `[43457/100000, 46959/100000]·L`, for the curve `g7d`

- `SieveTypeIIU22000D.window_22000d`: The window's exponents *paper*
- `SieveTypeIIU22000D.typeII_22000d`: Proposition 3′ at `L = 11 / 5` on `[43457/100000, 46959/100000]·L`, for the curve `g7d` *paper*

#### `SieveWeight`: Lemma 1 of the sieve route for primes, with weights uniform in the scale

- `SieveWeight.exists_mellin_bound`: The Mellin transform of `ψ_P`, uniformly in `P ≥ 4`
- `SieveWeight.norm_Sw_wy_le`: Lemma 1 for the weights `ψ_P`, in `Λ` form, uniformly in `P ≥ 4`
- `SieveWeight.norm_Sp_le`: Lemma 1 for primes *paper*

#### `SmallPrimes`: The small primes generate the units mod `q`

- `SmallPrimes.exists_prime_not_mem`: The least prime outside a proper subgroup
- `SmallPrimes.closure_primes_eq_top`: The small primes generate `(ℤ/qℤ)ˣ`
- `SmallPrimes.exists_prime_not_pow`: The least `k`-th power non-residue

#### `SmoothPerron`: A smoothed Perron formula for a general Dirichlet series

- `SmoothPerron.verticalIntegral_eq_smoothedSum`: The smoothed Perron formula
- `SmoothPerron.verticalIntegral_shift`: Moving the line of integration
- `SmoothPerron.mellin_le_geom_of`: The Mellin transform of `Smooth1` on a line, from two Mellin bounds
- `SmoothPerron.mellin_le_geom`: The Mellin transform of `Smooth1` on a line
- `SmoothPerron.norm_smoothedSum_sub_le`: Unsmoothing
- `SmoothPerron.verticalIntegral_integrand_shift`: Moving the Perron integral from `Re s = 2` to `Re s = σ′`
- `SmoothPerron.smoothedSum_eq_verticalIntegral_left`: The smoothed sum as an integral on a line left of `1`

#### `SquarefreeCount`: Squarefree numbers in a zero-free half-plane

- `SquarefreeCount.sum_sqf_eq`: `Q(N) = Σ_{d ≤ N} μ(d)⌊N/d²⌋`
- `SquarefreeCount.hasSum_moebius_div_sq`: `Σ μ(d)/d² = 1/ζ(2) = 6/π²`.
- `SquarefreeCount.abs_sub_sum_le`: The tail of `Σ μ(d)/d²`
- `SquarefreeCount.abs_sum_sqf_sub_le`: The count at an integer
- `SquarefreeCount.squarefree_isBigO_of_zeroFree`: Squarefree numbers in a zero-free half-plane
- `SquarefreeCount.squarefree_isBigO_twelve_25ths`: `Q(x) = 6x/π² + O(x^{12/25+η})`
- `SquarefreeCount.squarefree_isBigO_Theta`: `Q(x) = 6x/π² + O(x^{1/(3−Θ)+η})`

#### `Subconvexity`: Subconvexity from a zero-free half-plane

- `Subconvexity.zeta_strip_of_zeroFree`: Subconvexity from a zero-free half-plane
- `Subconvexity.zeta_strip_eleven_twelfths`: On the strip `1/12 ≤ σ ≤ 11/12`, with no hypothesis ([note](../formalisations/zeta-density.md))
- `Subconvexity.zetaCritBound_of_zeroFree`: On the critical line
- `Subconvexity.zetaCritBound_five_24`: Subconvexity on the critical line, with no hypothesis
- `Subconvexity.convexityBound`: The convexity bound
- `Subconvexity.zetaCritBound_Theta`: At `Θ`, the supremum of the real parts of the nontrivial zeros
- `Subconvexity.lindelof_of_RH`: RH implies Lindelöf

#### `SubconvexityCrit`: The strip bound for `ζ` from a critical-line bound and a zero-free half-plane

- `Subconvexity.zeta_strip_of_crit`: The strip bound from a critical-line bound
- `Subconvexity.zeta_strip_eleven_twelfths_of_crit`: At `11/12`, from the half-plane
- `Subconvexity.zeta_strip_eleven_twelfths_of_weyl`: At `11/12`, under Weyl's bound

#### `TwinKV`: The Korobov–Vinogradov region as a lower bound on the twin form

- `TwinKV.twins_lower_KV`: The KV-graded lower bound for the twin form
- `TwinKV.twins_lower_KV'`: The KV-graded lower bound in explicit shape
- `TwinKV.twins_lower_cut`: The lower bound with a free cutoff `u`
- `TwinKV.twins_lower_KV_sharp`: The twin form with the PNT exponent

#### `ZetaAFE`: The approximate functional equation for `ξ(s)²`

- `ZetaFourth.afe_xi`: The approximate functional equation for `ξ(s)²`

#### `ZetaFourth`: The fourth moment of `ζ(½ + it)` at well-spaced points

- `ZetaFourth.zeta_fourth_moment`: The fourth moment of `ζ(½ + it)` at well-spaced points ([note](../formalisations/zeta-density.md))

#### `ZetaGMDensity`: The density exponent `30/13` for `ζ`, and primes in short intervals for `θ > 17/30`

- `ZetaGMDensity.densityXi_thirty_thirteenths`: Zero density at Guth and Maynard's exponent `30/13` ([note](../formalisations/zeta-density.md))
- `ZetaGMDensity.short_primes_seventeen_thirtieths`: Primes in short intervals for every `θ > 17/30` ([note](../formalisations/zeta-density.md))
- `ZetaGMDensity.almost_all_short_primes_two_fifteenths`: Primes in almost all short intervals for every `θ > 2/15` ([note](../formalisations/zeta-density.md))

#### `ZetaGMHux`: Huxley's count for `ζ` on `4/5 ≤ σ ≤ 11/12`, at the exponent `30/13`

- `ZetaGMHux.nx_gmh`: The density estimate at the exponent `30/13` on `4/5 ≤ σ ≤ 11/12` ([note](../formalisations/zeta-density.md))

#### `ZetaGMIngham`: Ingham's count for `ζ` up to `σ = 7/10 + η`, at the exponent `30/13`

- `ZetaGMIngham.nx_ingham13`: The count at the exponent `30/13` on `17/30 ≤ σ ≤ 7/10 + η` ([note](../formalisations/zeta-density.md))

#### `ZetaGMLV`: Guth–Maynard's large values estimate at `1`-separated points

- `ZetaGMLV.gm_prop31_one`: Guth and Maynard's key proposition at `q = 1` ([note](../formalisations/zeta-density.md))
- `ZetaGMLV.gm_large_values`: Guth and Maynard's large values estimate ([note](../formalisations/zeta-density.md))

#### `ZetaGMWin`: Guth and Maynard's exponent for `ζ` on `7/10 + η ≤ σ ≤ 4/5`

- `ZetaGMWin.nx_gm`: The density estimate with Guth and Maynard's exponent on `7/10 + η ≤ σ ≤ 4/5` ([note](../formalisations/zeta-density.md))

#### `ZetaHuxley`: The density exponent `12/5` for `ζ` on `3/4 ≤ σ ≤ 11/12`, and primes in short intervals for `θ > 7/12`

- `ZetaHuxley.nx_huxley`: The density estimate with Huxley's exponent on `3/4 ≤ σ ≤ 11/12` ([note](../formalisations/zeta-density.md))
- `ZetaHuxley.densityXi_twelve_fifths`: Zero density at the exponent `12/5` ([note](../formalisations/zeta-density.md))
- `ZetaHuxley.short_primes_seven_twelfths`: Primes in short intervals for every `θ > 7/12` ([note](../formalisations/zeta-density.md))

#### `ZetaIngham`: Ingham's density estimate for `ζ` on `7/12 ≤ σ ≤ 3/4`

- `ZetaIngham.nx_ingham`: Ingham's density estimate for `ζ` on `7/12 ≤ σ ≤ 3/4` ([note](../formalisations/zeta-density.md))

#### `ZetaKernel`: The Halász–Montgomery inequality at well-spaced heights, and the kernel of `ζ` past its pole

- `ZetaKernel.hm_duality_pts`: The Halász–Montgomery duality inequality at points
- `ZetaKernel.norm_kz_le`: The kernel bound ([note](../formalisations/zeta-density.md))
- `ZetaKernel.power_count_pts`: Large values of a power at well-spaced heights

### `lib/dh`

#### `ChiFirstFailure`: Continuity and the first positivity failure for every u-space form

- `PsiOmega.continuousOn_lamC`: `λ_χ` is continuous on `(0, ∞)` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.lamC_pos_small`: `λ_χ ≥ log 2 − ¼` at small support ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.first_failureC`: The first positivity failure for `L(s, χ)` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.first_failureDH`: The first positivity failure of `Q_dh`, unconditionally ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.continuousOn_lamDH`: `λ_dh` is continuous on `(0, ∞)` ([note](../formalisations/davenport-heilbronn.md))

#### `ChiGround`: The ground-state stack for `L(s, χ)`

- `PsiOmega.exists_groundStateC`: A ground state of `QCu χ` exists at every support `a > 0` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.euler_lagrangeC_mem`: Euler–Lagrange for `QCu χ` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.theoremDC`: Theorem D for `QCu χ` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.grh_of_eventually_simpleC`: GRH for `χ` from eventually simple ground states with `HypConvC χ` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.grh_chi3_of_hypConvC_top`: GRH for `χ₋₃` from `HypConvC` for its top-of-chain ground states ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.grh_chi4_of_hypConvC_top`: GRH for `χ₋₄` from `HypConvC` for its top-of-chain ground states ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.grh_chi8_of_hypConvC_top`: GRH for `χ₋₈` from `HypConvC` for its top-of-chain ground states ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.grh_chi7_of_hypConvC_top`: GRH for `χ₋₇` from `HypConvC` for its top-of-chain ground states ([note](../formalisations/davenport-heilbronn.md))

#### `DHBohrSphere`: A zero pair off the sphere

- `PsiOmega.dh_zero_pair_off_sphere`: A zero pair of the Davenport–Heilbronn function off the unit sphere ([note](../formalisations/davenport-heilbronn.md))

#### `DHCertificate`: The certificate — `Q_dh(packet 12/5 169/2) < 0`, hence an off-line zero of `dh` (stage 4)

- `PsiOmega.dh_offline_zero`: The Davenport–Heilbronn function has a zero off the critical line ([note](../formalisations/davenport-heilbronn.md))

#### `DHChannels`: The two channels of the Davenport–Heilbronn function

- `PsiOmega.chi5_channel_fe`: (1) for `χ₅` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.chi5_phase_lock`: (2) for `χ₅`, the phase lock ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.chi5_channel_ratio_real`: On the critical line, `L(½ + it, χ₅)/(ε L(½ + it, χ₅⁻¹))` is real. ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.chi5_channel_ratio`: (4) The channel ratio of `χ₅` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.dh_line_zero_iff`: On the critical line the zero condition is one real equation ([note](../formalisations/davenport-heilbronn.md))

#### `DHColumn`: The dh column of the substitution matrix, part 1

- `PsiOmega.not_D_dh`: The dh column of `rh_of_D_and_realRooted_proved` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.QDHu_nonneg_of_DHRHcross`: `DHRHcross ⟹ Q_dh ≥ 0` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.weil_criterion_dh`: The dh column of `weil_criterion_zeta` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.not_GRH_dh`: GRH fails for `dh` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.finrank_le_quadruples_dh`: The Davenport–Heilbronn instance ([note](../formalisations/davenport-heilbronn.md))

#### `DHColumnRest`: The dh column, part 4: the remaining G rows and the strip row of the P block

- `PsiOmega.not_ground_states_dh`: The dh column of `rh_of_ground_states` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.not_groundStates_dodging_dh`: The dh column of `rh_of_groundStates_dodging` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.not_D_and_realRooted_hadamard`: The dh column of `rh_of_D_and_realRooted` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.not_hypConvStripDH_top`: The dh column of `rh_of_hypConvStrip_top` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.not_XiDH_params`: The dh column of `rh_of_Xi_params` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.not_dodging_hadamard`: The dh column of `rh_of_dodging` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.not_pairing_and_realRooted`: The dh column of `rh_of_pairing_and_realRooted` ([note](../formalisations/davenport-heilbronn.md))

#### `DHExplicit`: The explicit formula for the Davenport–Heilbronn function

- `PsiOmega.exists_offline_dh_of_neg`: A negative Weil form certifies an off-line zero of `dh` ([note](../formalisations/davenport-heilbronn.md))

#### `DHForm`: Weil's u-space form for `dh` is a `ProbeForm`; the DH ground energy

- `PsiOmega.exists_lamDH_neg`: The `dh` column of `exists_lam_neg_of_not_RH`, unconditional ([note](../formalisations/davenport-heilbronn.md))

#### `DHGround`: The dh column, part 3: the ground-state stack of `QDHu`

- `PsiOmega.bilDH_polar`: `B_dh` is the polarisation of `QDHu` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.euler_lagrangeDH`: Euler–Lagrange at a ground state ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.dhRHcross_of_eventually_simple`: The chain for `dh` with eventual simplicity ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.not_simple_hypConvDH`: The refutation ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.theoremDDH`: Theorem D for `QDHu` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.dhRHcross_of_hypConv_top`: The chain for `dh` with simplicity removed ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.not_hypConvDH_top`: `HypConvDH` fails for the top-of-chain ground states of `QDHu` ([note](../formalisations/davenport-heilbronn.md))

#### `DHHurwitzEM`: The Euler–Maclaurin approximant of the Davenport–Heilbronn function `dh`

- `PsiOmega.norm_dh_sub_EM_le`: The Euler–Maclaurin bound for `dh` ([note](../formalisations/davenport-heilbronn.md))

#### `DHInert`: Coefficient localisation of the Davenport–Heilbronn prime side

- `PsiOmega.cDH_chi5_eq_of_dvd`: Coefficient localisation ([note](../formalisations/davenport-heilbronn.md))

#### `DHJoins`: Joins in the Davenport–Heilbronn layer

- `PsiOmega.dhRH_iff_cross`: `DHRH ↔ DHRHcross` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.dh_conj_zero`: The zeros of `dh` are symmetric under conjugation. ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.QDHu_packet_plane_neg`: A negative-definite plane of `Q_dh` from the two packet certificates ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.lamC_nonneg_of_GRH`: Under GRH(χ), `λ_χ ≥ 0` at every support ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.grh_iff_lamC_eventually_nonneg`: GRH(χ) iff `λ_χ ≥ 0` at all large supports ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.grh_iff_lamC_nonneg_chi3`: GRH for `χ₋₃` iff `λ_{χ₋₃} ≥ 0` at every support ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.grh_iff_lamC_nonneg_chi4`: GRH for `χ₋₄` iff `λ_{χ₋₄} ≥ 0` at every support ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.grh_iff_lamC_nonneg_chi8`: GRH for `χ₋₈` iff `λ_{χ₋₈} ≥ 0` at every support ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.grh_iff_lamC_nonneg_chi7`: GRH for `χ₋₇` iff `λ_{χ₋₇} ≥ 0` at every support ([note](../formalisations/davenport-heilbronn.md))
- `DHNegIndex.negIndex_ge_five`: The Weil index of `Q_dh` on probes of either parity is at least `5` ([note](../formalisations/davenport-heilbronn.md))

#### `DHLocateFour`: Four located off-line zeros of `dh`, and the Weil index of `Q_dh` is at least `4`

- `PsiOmega.Locate.dh_zeros_located_four_box`: The four located zeros in coordinates ([note](../formalisations/davenport-heilbronn.md))
- `DHNegIndex.negIndex_ge_four`: The Weil index of `Q_dh` is at least `4` ([note](../formalisations/davenport-heilbronn.md))

#### `DHOddPacket`: The sine packet: Weil's form of `dh` is negative on an odd probe

- `PsiOmega.not_odd_lower_dh`: The odd lower bound for `dh`, refuted ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.not_lamODH_lower`: The lower bound `λ_dh^odd(b) ≥ c·e^{(9+δ)b − 4πe^{2b}}`, refuted ([note](../formalisations/davenport-heilbronn.md))

#### `DHOffCross`: The certificate's zero is off the cross

- `PsiOmega.dh_offline_nonreal_zero`: The certificate's zero is non-real ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.dh_offline_zero_right`: The free strengthening ([note](../formalisations/davenport-heilbronn.md))

#### `DHRealAxis`: `dh` has no zero on the positive real axis

- `PsiOmega.dh_div_a1_real_ge`: `dh(σ)/a(1) ≥ 1 − 2^{−σ}` ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.dh_offcross_zero`: An off-line zero of `dh` off the real axis ([note](../formalisations/davenport-heilbronn.md))

#### `DHTwin`: The dh column of the substitution matrix, part 2: the twin form

- `PsiOmega.not_twins_nonneg_dh`: The twin form of `dh` is negative somewhere ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.not_twins_subexp_dh`: The twin form of `dh` has a negative part of exponential rate ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.lamDH_fails_exponentially`: `λ_dh` fails exponentially, unconditionally ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.not_lamDH_subexp`: `λ_dh` has a negative part of exponential rate ([note](../formalisations/davenport-heilbronn.md))

#### `DHZeros`: `L(½, χ₅) ≠ 0` and the zero side for `Ξ_{DH}`

- `PsiOmega.hasSum_logDeriv_dh`: The zero side for the Davenport–Heilbronn `Ξ` ([note](../formalisations/davenport-heilbronn.md))

#### `DavenportHeilbronn`: Davenport–Heilbronn in Lean, stage 1

- `PsiOmega.dh_ne_zero`: `dh` is not identically zero ([note](../formalisations/davenport-heilbronn.md))
- `PsiOmega.dh_functional_equation`: The functional equation ([note](../formalisations/davenport-heilbronn.md))

### `lib/zeta23`

#### `BohrLandau`: Bohr and Landau's theorem in the library's zero family

- `BohrLandau.tendsto_NX_div_pos`: For every `w > 0`, the proportion of zero pairs up to height `T` with `|β − ½| ≥ w` tends to `0`
- `BohrLandau.tendsto_outside_div_pos`: The same in sphere form

#### `CountCompare`: The two local zero counts compared

- `CountCompare.local_count_le`: zeta23's local count from the library's zero weight, with the library's explicit constant

#### `CriticalLine`: The zeros of `ζ` on the critical line: Hardy, Selberg, and Alpöge and Furman's two thirds

- `CriticalLine.ncard_zeros_ge`: A positive proportion of the zeros of `ζ` lie on the critical line
- `CriticalLine.exists_zero_im_gt`: The zeros of `ζ` on the critical line have unbounded ordinates
- `CriticalLine.infinite_zeros`: Hardy's theorem
- `CriticalLine.ncard_simple_zeros_ge`: A positive proportion of the zeros of `ζ` are simple and on the critical line
- `CriticalLine.infinite_simple_zeros`: Infinitely many zeros of `ζ` on the critical line are simple
- `CriticalLine.two_thirds`: Two thirds of the zeros of `ζ` lie on the critical line
- `CriticalLine.two_thirds_cumulative`: Two thirds of the zeros of `ζ` up to height `T` lie on the critical line
- `CriticalLine.half_simple`: Half of the zeros of `ζ` are simple and on the critical line
- `CriticalLine.three_quarters_distinct`: Three quarters of the zeros of `ζ` are distinct

#### `HybridCertificate`: The same-space hybrid certificate on zeta23's zero side, with the off-line term displayed

- `HybridCert.cert_general`: The rank–trace certificate in units c
- `HybridCert.cert_offline`: The certificate with the off-line pairs written out
- `HybridCert.hybrid_cert`: The same-space hybrid certificate
- `HybridCert.hybrid_cert_pairs`: The certificate on pair representatives
- `HybridCert.hybrid_cert_of_offline`: The certificate with the off-line input displayed
- `HybridCert.hybrid_cert_of_moments`: The off-line input split by order in η
- `HybridCert.hybrid_cert_of_no_offline`: No off-line zeros
- `HybridCert.hybrid_cert_eta_zero`: Consistency (η = 0)

#### `ShellDensity`: For every `w > ¼`, almost every zero lies within `w` of the critical line, in Bohr-shell form

- `ShellDensity.emBound_zeta23`: The Euler–Maclaurin bound at a zero
- `ShellDensity.density_zeta23`: Zero density
- `ShellDensity.Ncount_le_NX`: zeta23's zeros with `T < γ ≤ 2T` inject into the library's pairs up to height `2T`
- `ShellDensity.NX_zero_ge`: Riemann–von Mangoldt in the library's family
- `ShellDensity.tendsto_NX_div_quarter`: For every `w > ¼`, the proportion of pairs up to height `T` with `|β − ½| ≥ w` tends to `0`
- `ShellDensity.tendsto_outside_div_quarter`: The same in sphere form
- `ShellDensity.ncard_outside_le_unconditional`: The count

#### `ShellSixth`: For every w > 1/6, almost every zero lies within w of the critical line

- `ShellSixth.emApprox_zeta23`: The Euler–Maclaurin approximation of `ζ` by its partial sums
- `ShellSixth.tendsto_NX_div_sixth`: For every `w > 1/6`, the proportion of zero pairs up to height `T` with `|β − ½| ≥ w` tends to `0`
- `ShellSixth.tendsto_outside_div_sixth`: The same in sphere form

#### `SlogZeta`

- `SlogZeta.Slog_eventually`: `S(T) = O(log T)`, eventually
- `SlogZeta.Slog_zeta`: `S(t) = O(log t)` on `t ≥ 14`
- `SlogZeta.wall_law_zeta_S`: 1ca(i)–(iii) for ζ, with von Mangoldt's bound proved

#### `ZeroWindow`: Bounded gaps between the ordinates of the zeros of `ζ`

- `ZeroWindow.zero_in_window`: Bounded gaps between the zeros of `ζ`
