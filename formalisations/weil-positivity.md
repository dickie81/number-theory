# Weil's criterion, and the library's criteria for RH from Weil's form

**Lean:** `lib/core` and `lib/pnt` (namespaces `WeilForm`, `WeilTwinGeneral`, `PsiOmega`, `Dedekind4`); the axioms of
every theorem below are printed by `lib/check/CheckAll.lean`. No paper uses these results; they are kept for their own
sake.

```lean
theorem WeilForm.weil_criterion_zeta :
    (∀ (a : ℝ) (g : ℝ → ℝ), 0 < a → Probe a g → 0 ≤ weilQ a g) ↔ RiemannHypothesis

theorem WeilForm.rh_iff_lam_subexp :
    RiemannHypothesis ↔ ∀ σ > 0, ∃ C, ∀ a, 1 ≤ a → -(C * Real.exp (σ * a)) ≤ lam a
```

Weil's form `Q(g)`, for an even probe `g` supported in `[−a, a]`, is the sum of `ĝ` over the nontrivial zeros of `ζ`,
which Weil's explicit formula writes through the primes and the archimedean place (`WeilForm.weilQ`). In words: `Q` is
nonnegative on every probe at every support if and only if RH holds; and RH holds if and only if the least value `λ₁(a)`
of `Q` on the normalised probes at support `a` has no negative part of exponential rate.

## Source

A. Weil, *Sur les « formules explicites » de la théorie des nombres premiers*, Comm. Sém. Math. Univ. Lund (1952),
252–265, for the criterion. The rest is the library's: the twin form, the ground energies and ground states of `Q`, and
the chains that reduce RH to properties of them. G. Pólya, *Über die Nullstellen gewisser ganzer Funktionen*, Math. Z. 2
(1918), for the real zeros of the transforms of concave functions, and A. Beurling and J. Deny, *Dirichlet spaces*,
Proc. Nat. Acad. Sci. 45 (1959), for the contraction property.

## The criteria

- **Weil's criterion for `ζ`**, both directions (`WeilForm.weil_criterion_zeta`, `WeilForm.rh_of_weil`,
  `WeilForm.line_of_RH`), and for a family of zeros with finitely many off the line (`WeilForm.weil_criterion_finite`).
- **The twin form**, `Q` on the twin boxes `twin (box 1) λ` alone: RH if it is nonnegative (`WeilForm.rh_of_weil_twins`,
  `WeilForm.line_of_weil_twins`, `WeilTwinGeneral.line_of_twins_g`), and RH if and only if its defect is subexponential
  (`WeilForm.rh_iff_twins_subexp`); with the box, with any concave base probe and with any real-rooted monotone one
  (`WeilTwinGeneral.rh_iff_twins_box`, `WeilTwinGeneral.rh_iff_twins_concave`,
  `WeilTwinGeneral.rh_iff_twins_realRooted`, `WeilTwinGeneral.twins_rate_realRooted`).
- **The ground energy** `λ₁`: RH if and only if it has no negative part of exponential rate
  (`WeilForm.rh_iff_lam_subexp`); if RH fails, it fails exponentially (`WeilForm.lam_fails_exponentially`), with a first
  support at which positivity is lost (`WeilForm.first_failure`).
- **The ground states**: RH from ground states `g_n` whose transforms are real-rooted and converge to `Ξ`
  (`WeilForm.rh_of_ground_states`, `WeilForm.rh_of_realRooted_limit`), with Hypothesis D, dodging or a pairing with the
  zeros of `Ξ` in place of the convergence (`WeilForm.rh_of_D_and_realRooted`, `WeilForm.rh_of_D_and_realRooted_proved`,
  `WeilForm.rh_of_D_and_realRooted_final`, `WeilForm.rh_of_pairing_and_realRooted`, `WeilForm.rh_of_dodging`,
  `WeilForm.rh_of_dodging_final`, `WeilForm.rh_of_groundStates_dodging`, `WeilForm.hypConv_of_D`), and from the real
  parameters of a factorisation of `Ξ` (`WeilForm.rh_of_Xi_params`); with the prime side's convergence `HypConv` and
  zeros on `ℝ ∪ iℝ` (`WeilForm.rh_of_prime_side`, `WeilForm.rh_of_prime_side_cross`), with eventual simplicity
  (`WeilForm.rh_of_simple_ground_states`, `WeilForm.rh_of_simple_ground_states'`, `WeilForm.rh_of_eventually_simple`),
  for the top-of-chain ground states with no simplicity (`WeilForm.rh_of_hypConv_top`), with no crossing of the even and
  odd ground energies (`WeilForm.rh_of_no_crossing`) and with the parity gap (`WeilForm.rh_of_parity_gap`). Ground
  states exist at every support (`WeilForm.exists_groundStates`).
- **Dirichlet `L`-functions**: GRH for `χ` if and only if `Q_χ` has no negative part of exponential rate
  (`PsiOmega.grh_iff_QC_subexp`, `PsiOmega.grh_iff_QC_subexp_all`, `PsiOmega.grh_iff_QC_subexp_chi4`), with the rate an
  off-line zero gives (`PsiOmega.QC_fails_rate`); Weil's twin criterion for `χ₋₃`, `χ₋₄`, `χ₋₇` and `χ₋₈`
  (`PsiOmega.grh_iff_twins_chi3`, `PsiOmega.grh_iff_twins_chi4`, `WeilTwinGeneral.grh_iff_twins_chi7`,
  `PsiOmega.grh_iff_twins_chi8`, `PsiOmega.twins_rate_chi4`).
- **Dedekind zeta functions** of imaginary quadratic fields: `RH ∧ GRH(χ)` if and only if `2Q_ζ + Q_χ ≥ 0` on the twin
  boxes, for every good character (`WeilTwinGeneral.rh_grh_iff_QKχ_twins`), for `ℚ(i)` (`Dedekind4.rh_grh_iff_QK_twins`,
  `Dedekind4.rh_grh_iff_QK_subexp`, `WeilTwinGeneral.rh_grh_iff_twins_Q4`) and for `ℚ(√−3)`, `ℚ(√−7)` and `ℚ(√−2)`
  (`WeilTwinGeneral.rh_grh_iff_twins_Q3`, `WeilTwinGeneral.rh_grh_iff_twins_Q7`, `WeilTwinGeneral.rh_grh_iff_twins_Q8`);
  the twin forms of `L(s, χ₋₄)` and of `ζ_{ℚ(i)}` are at least `−o(e^λ)` with no hypothesis
  (`Dedekind4.QC_chi4_littleO`, `Dedekind4.QK_littleO`).
- **The angular family**, the Dirichlet series of the angular averages over the Gaussian integers of each norm, whose
  radial member is `ζ·L(χ₋₄)` (`AngularFamily.member_zero_eq`): the radial member's grand RH gives RH and GRH for `χ₋₄`
  (`AngularFamily.rh_of_member_zero`, `Dedekind4.rh_grh_of_member_zero`, `Dedekind4.QK_nonneg_of_member_zero`).
- **Other criteria**: Pólya's conjecture `L(x) ≤ 0` for `x ≥ 2` gives RH (`PsiOmega.rh_of_polya`; the conjecture is
  false, C. B. Haselgrove, Mathematika 5 (1958)), and so do one-sided bounds for Liouville's `L(x)`
  (`PsiOmega.rh_of_liouville_bound`, `CrossCriteria.rh_of_liouville_theta`); RH says that the normalised Bohr vector of
  every nontrivial zero lies on the unit sphere (`BohrSphere.riemannHypothesis_iff_mem_sphere`,
  `BohrSphere.riemannHypothesis_iff_tendsto`), a reformulation that constrains nothing.

## Unconditional results on Weil's form of `ζ`

- **The ground energies decay**: `λ₁`, the odd `λ₁` and `λ₂` are at most `Ke^{−Ba}` for every `B`
  (`WeilForm.lam_decay_uncond`, `WeilForm.lamO_decay_uncond`, `WeilForm.lam2_decay_uncond`), and double-exponentially
  (`WeilForm.lam_dexp`, `WeilForm.lamO_dexp`, `WeilForm.lam2_dexp`, `Kaiser.lam_kaiser`); with the zero-free half-plane,
  `λ₁(a) ≤ K(a + 1)e^{(59/6)a − 4πe^{2a}}` and the twin form is at least `−Ce^{5λ/6}`
  (`HalfPlaneJoins.lam_prefactor_eleven_twelfths`, `HalfPlaneJoins.weil_rate_eleven_twelfths`).
- **Lower bounds**: `λ₁(δ) ≥ ψ(¼) − log π − 2Σ_{n ≤ e^δ} Λ(n)/√n` (`WeilForm.groundState_energy_ge`); `Q(g) ≥ ‖g‖²/20`
  for every real `g` at every support `a ≤ 1/12` (`WeilForm.weilQg_ge_twentieth_all`); Beurling–Deny for `Q₀`,
  `Q₀(|g|) ≤ Q₀(g)` (`WeilForm.weilQ0_abs_le`).
- **The ground state**: unique up to sign for `a ≤ 0.35` and for `2a < log 2` (`WeilForm.groundState_unique_035`,
  `WeilForm.groundState_unique_below_log2`), and wherever an energy gap or a pole overlap holds
  (`WeilForm.groundState_unique_of_gap`, `WeilForm.simpleGround_of_gap`, `WeilForm.simple_of_pole_overlap`,
  `WeilForm.pole_overlap_identity`); the characterisations of simplicity (`WeilForm.not_simple_iff_secular`,
  `WeilForm.simple_iff_no_green_pair`, `WeilForm.degenerate_flat_fourier`, `WeilForm.first_degeneracy_036`); Theorem C,
  no simple ground state is flat at the edges (`WeilForm.simple_iff_no_flat`, `WeilForm.simple_not_flat`); Theorem D,
  the ground space spanned by a Green chain whose top has its zeros on `ℝ ∪ iℝ` (`WeilForm.theoremD`,
  `WeilForm.chain_top_zeros`), and the zeros of a simple ground state on `ℝ ∪ iℝ` (`WeilForm.zeros_real_or_imag'`).
- **The negative index**: a space of probes on which `Q` is negative definite has dimension at most the number of
  off-line zeros or of their quadruples (`WeilForm.finrank_le_offline_zeta`, `WeilForm.finrank_le_quadruples_C2`); if
  the off-line zeros are finitely many, some support has a space of dimension exactly the number of quadruples
  (`WeilForm.negIndex_eq_quadruples`), and the index is unbounded if infinitely many quadruples are off the line
  (`WeilForm.negDirections_unbounded`); one probe with `Q < 0` exhibits an off-line zero
  (`WeilForm.exists_offline_of_neg_C2`).
- **Forms and transforms**: the symbol form of `Q` and the bilinear zero sum (`WeilForm.weilQ_symbol`,
  `WeilForm.bil_zero_sum`); Pólya's theorem, a probe equal to an even, concave, nonnegative function is real-rooted
  (`WeilForm.realRooted_of_ae_concaveOn`), with the curvature sum rule of a real-rooted transform
  (`WeilForm.ghat_curvature`); the pinning theorems, a zero of `ĝ` near every zero of `ζ` verified on the line
  (`WeilForm.pinned_zeta`, `WeilForm.pinned_unconditional_zero`).

## Conditional results

These results have a hypothesis that the library does not prove, and no unconditional result uses them.

| Result | Hypothesis | Lean |
|---|---|---|
| RH, RH with GRH for `χ₋₄`, and the Dedekind twin form of `ℚ(i)` nonnegative | GRH for the radial member of the angular family (`GRHMemberZero`) | `AngularFamily.rh_of_member_zero`, `Dedekind4.rh_grh_of_member_zero`, `Dedekind4.QK_nonneg_of_member_zero` |
| RH | Pólya's conjecture, `L(x) ≤ 0` for every `x ≥ 2`, which is false | `PsiOmega.rh_of_polya` |
| A first support at which Weil positivity is lost, and the exponential failure of `λ₁` | that RH fails | `WeilForm.first_failure`, `WeilForm.lam_fails_exponentially` |
| The negative index of Weil's form is unbounded | that no finite set of quadruples holds every off-line zero of `ζ` | `WeilForm.negDirections_unbounded` |
| RH, from ground states that satisfy `HypConv` | that the even and odd ground energies never coincide for `a ≥ 1/4` | `WeilForm.rh_of_no_crossing` |
