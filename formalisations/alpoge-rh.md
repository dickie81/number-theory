# The Riemann hypothesis: L. Alpöge's proof, rebuilt

## Source

- L. Alpöge, with Claude: a statement of 20 November 2026, <https://alpo.ge/remark.pdf>.
- The Lean archive it links, in 14 parts at `https://alpo.ge/lean.tar.gz.part01` to `part14`, with SHA-256
  `9631b4f0…49c7fc` once joined (`tools/rh/README.md`).

The archive proves the Riemann hypothesis for `ζ` and for every Dirichlet `L`-function. On its own pins, Lean's
kernel accepts it, and its main theorems use only `propext`, `Classical.choice` and `Quot.sound`. It carries no
licence, so nothing of it is in this repository.

The library takes GRH from it as an input (`docs/account.md`), but not into its Lean, which does not import the archive
and declares no axioms: there GRH stays a hypothesis, stated in the archive's words (`LinnikGRH.DirichletRH`). So the
library's headline Linnik exponent, every exponent above `2`, is `LinnikGRH.linnik_two`, with that hypothesis.

## The library's proof, so far

The library is rebuilding the proof from the top, written fresh from the mathematics, in its own style and on its own
Lean and Mathlib (`docs/rh-rebuild.md`). Steps 1 and 2 are done for `ζ` and every Dirichlet `L`-function, and so
are steps 3 and 4, with the analytic inputs as hypotheses. For `ζ` and every primitive `χ` both analytic inputs, the
thin scales and the twists, are proved, conditionally on the half-plane `Re s > 11/12`.

- **The top.** `HalfPlaneGRH.rhAndGRH_of_zeroFreeRightOf`: if no primitive Dirichlet `L`-function vanishes on
  `Re s > 1/2`, the Riemann hypothesis holds for `ζ` (Mathlib's `RiemannHypothesis`) and every zero of every
  `L(s, χ)` in the critical strip lies on the line. `HalfPlaneGRH.zeroFreeRightOf_half_iff` is the converse, so this
  step loses nothing.
- **Landau's theorem on windows.** `LandauWindow.re_le_of_windows`: let a real function `g` of exponential growth have
  a Laplace transform that continues to `Re s > 0` with simple poles, at an isolated set left of `Re s = 1`, of
  positive residue at the real ones. If `g ≤ C e^{θu}` on windows `[U, λU]` for arbitrarily large `U`, no pole lies
  right of `θ`. The proof compares Taylor coefficients at a point of the line `Re s = σ` whose nearest pole is
  unique.
- **For Dirichlet characters.** `WindowGRH.Family.zeroFree_of_windows`: for a finite family of characters with
  positive weights, a bound `G(x) ≤ C x^θ` on windows `[Y, Y^λ]` keeps every member's `L`-function free of zeros right
  of `θ`. Here `G` is the weighted sum of the real parts of the errors of the ramp sums
  `Σ_{n ≤ x} Λ(n)χ(n)(x/n − 1)`.
- **The theorem.** `WindowGRH.rhAndGRH_of_windowBound`: the Riemann hypothesis for `ζ` and every Dirichlet
  `L`-function, from `WindowGRH.WindowBound`.
- **For `ζ` alone.** `WindowGRH.riemannHypothesis_of_zetaWindowBound`: Mathlib's `RiemannHypothesis` follows from a
  statement about `Λ` alone, `WindowGRH.ZetaWindowBound`. For every `θ > 1/2`, on windows `[Y, Y^λ]` with `Y`
  arbitrarily large, `Σ_{n≤x} Λ(n)(x/n − 1) − x log x + (1 + γ)x ≤ C x^θ`.

- **The balance for `ζ`** (step 3). `ZetaBalance.riemannHypothesis_of_zetaBalanceBound`: the Riemann hypothesis
  follows from `ZetaBalance.ZetaBalanceBound`, a bound on sums over prime powers inert in an imaginary quadratic
  field. Two pieces make it up.
  - **The balance identity** (Lemma B), `ZetaBalance.Setting.balance`. Take primes `q ≡ 3 (mod 4)` and `d` with
    `(2/d) = (q/d) = 1`, a modulus `QS` prime to `q` whose primes `p` have `(p/d) = 1`, a subgroup `K` of `(ℤ/QS)ˣ`,
    and let `A = (ℤ/QS)ˣ/K` and `Φ = {±1} × A`; for `ζ` the archive takes `A = (ℤ/2^{e+2})ˣ/{±1}`. Weights
    `W : Φ → (0, ∞)` give a ramp sum over the prime powers inert in `ℚ(√−d)`, in the classes
    `ρ_t(n) = ((−n/q), [n]_A·t)`. That sum, less its main term, is an exact combination of the ramp errors `g_χ` of
    the characters `χ_d^α χ_q^β ξ`, with `ξ` a character of `A`.
  - **Theorem Z**, `ZetaBalance.BalanceData.zeta_le`. Average the identity over the translates `u ∈ A`, keeping only
    the classes where the weights (`ZetaBalance.Weights`) are near `a_t/x`. Only the characters trivial on `A` survive.
    So a bound on the averaged gap gives `Σ_{n≤x} Λ(n)(x/n − 1) − x log x + (1 + γ)x ≤ 7x^{1/2+3ε}`. The analytic
    inputs are two properties of the setting: it is thin at `X` (`ZetaBalance.Setting.Thin`), with every `g_χ(y)` at
    most `θy` for `y ≥ X`, and its twists are small (`ZetaBalance.Setting.Twists`), with the three quadratic twists at
    most `x^{1/2+ε}` at `x`.

- **Lattices** (step 4). `ZetaBalance.riemannHypothesis_of_zetaLatticeBound`: the Riemann hypothesis follows from
  `ZetaBalance.ZetaLatticeBound`. At each translate there is a frame of lattices meeting the hypotheses of the frame
  inequality. Its gain over the target covers the gap (G), with small losses (Z). That frontier is satisfied by frames
  of rank one whenever the averaged gap bound holds. What is new is how the gap is paid for: by slopes of lattices,
  through the two results below.

- **Every primitive character** (steps 3 and 4). `ZetaBalance.rhAndGRH_of_balanceBound` and
  `ZetaBalance.rhAndGRH_of_latticeBound`: the Riemann hypothesis for `ζ` and every Dirichlet `L`-function follows from
  `ZetaBalance.BalanceBound`, and from `ZetaBalance.LatticeBound`, the frontiers above for every primitive `χ`. For `χ`
  of order `o`, the setting carries a character `κ` of `A` that lifts `χ` (`ZetaBalance.Setting.Lifts`). The translates
  are averaged over its kernel `A₀`, which keeps exactly the characters `κ^k`, `k < o` (`ZetaBalance.sum_dual_sum_A₀`,
  with no count of them), and they carry shares that give these the weights `1/(3o + 1)` of the cyclic family. Theorem
  Z, `ZetaBalance.BalanceData.cyclicG_le`, then bounds the family's error by `(9o − 2)x^{1/2+3ε}`, given the `3o`
  twists `ψ_kχ_q`, `ψ_kχ_d` and `ψ_kχ_qχ_d`, `ψ_k = (χ^k)*`, at most `x^{1/2+ε}` at `x`. `ζ` is the case `χ = 1`.

- **The thin scales**, CONDITIONAL on the half-plane `Re s > 11/12` ([openai-half-plane.md](openai-half-plane.md)).
  `ZetaBalance.thin_of_large`: for `x` large, every setting is thin at `(Nx)^{log x}`. So
  `ZetaBalance.riemannHypothesis_of_zetaTwistBound` gives the Riemann hypothesis from `ZetaBalance.ZetaTwistBound`,
  the frontier after step 4 with that input proved. It rests on `ZetaBalance.norm_rampErr_le`:
  `‖g_χ(y)‖ ≤ C log(N + 2) y^{11/12+2η}` for every primitive `χ` mod `N`. For `χ ≠ 1` this comes from the library's
  bounds, uniform in the modulus, on `ψ(y, χ)` (`lib/pnt/ChiUniform.lean`) and on the tail of `L′/L(1, χ)`
  (`GSTail.logDeriv_one_tail`). For `ζ` it comes from Mertens' theorem with a power saving,
  `Σ_{n≤y} Λ(n)/n = log y − γ + O(y^{2η−1/12})` (`ZetaBalance.mertens_error_le`). That is the unconditional
  `GSTail.tail_le_of_sum_le` applied to `Λ − 1`, whose `L`-series `−ζ′/ζ(s) − ζ(s)` takes the value `−2γ` at `s = 1`.

- **The twists**, CONDITIONAL on the half-plane. `ZetaTwist.exists_winPair_twists`: let `χ` be a Dirichlet character
  of order `o`. For `0 < ε ≤ 1/2` and `A ≥ 1`, every large `Y` has a pair of primes `(q, d)` with the arithmetic the
  lattice side needs (`ZetaTwist.WinPair`), whose `3o` twists `χ_d^α χ_q^β χ^k`, `(α, β) ≠ (0, 0)` and `k < o`
  (`ZetaTwist.twist`), have primitive characters with ramp errors at most `y^{1/2+ε}` at every `y ∈ [Y, Y^A]`. For `ζ`
  these are the quadratic twists `χ_q`, `χ_d` and `χ_qχ_d` (`ZetaTwist.exists_winPair_twists_one`). As in the archive,
  the bound comes from a mean square over a family of primes (`TwistFamily`), not from zeros near the critical line.
  The diagonal of the mean square is small, and its off-diagonal terms are sums of a Jacobi character over the primes
  of a progression, bounded uniformly in the modulus (`lib/pnt/PrimeCharSums.lean`). A discrete Sobolev step and
  Markov's inequality (`MeanSquareSup.card_bad_le`) then make the bound uniform on the window for most of the family,
  for the `o` or `2o` weights `χ^k` and `χ^kχ_q` at once (`TwistFamily.exists_good_fin`). The half-plane takes the
  place of the archive's prime number theorem in progressions with exceptional zeros.
- **The pair-first frontiers.** `ZetaBalance.rhAndGRH_of_pairBound`: the Riemann hypothesis for `ζ` and every
  Dirichlet `L`-function follows, conditionally on the half-plane, from `ZetaBalance.PairBound`, which is the
  construction alone. For every primitive `χ`, at arbitrarily small `ε`, for every large `Y`, every pair with that
  arithmetic has a sub-window `[Y′, Y′²]` of `[Y, Y^A]` on which every `x` has lattice data in a setting with that pair
  and a character `κ` of `A` lifting `χ`. For `ζ` alone, `ZetaBalance.riemannHypothesis_of_zetaPairBound` gives the
  Riemann hypothesis from `ZetaBalance.ZetaPairBound`. The `3o` twists of a setting are the ramp errors of the twists
  of `χ` (`ZetaBalance.Setting.Lifts.g_twist`): `D_{(α,β,κ^k)}` is `χ_d^α χ_q^β χ^k` at a higher level.
- **The six-term interface.** `ZetaBalance.rhAndGRH_of_sixTermBound`: the Riemann hypothesis for `ζ` and every
  Dirichlet `L`-function follows, conditionally on the half-plane, from `ZetaBalance.SixTermBound`, which is
  `ZetaBalance.PairBound` with six-term data (`ZetaBalance.SixTermData`) in place of lattice data. At each translate,
  numbers of the words of a frame and of the translate meet the archive's six inequalities G1–G6: vanishing at the
  inert places raises the sources' slopes above those of the forms (G1); the forms' slopes are bounded below (G2); the
  target's slope and the heights are bounded by a main term that the forced vanishing raises and the auxiliary primes
  lower (G3); the auxiliary primes are large enough (G4); the split primes are bounded (G5); and the gain covers the
  inert-prime sum (G6). A key identity (`ZetaBalance.Setting.key_identity`) sums them, word by word, to the gain (G) of
  the lattice data. This is the algebra of the archive's `ch_top`. Like the frontiers above it, `SixTermBound` holds
  with frames of rank one whenever the averaged gap bound does.
- **Linnik's exponent from the frontier.** `LinnikGRH.dirichletRH_of_rhAndGRH`: the rebuild's conclusion,
  `HalfPlaneGRH.RHandGRH`, which covers every character, gives GRH in the archive's words (`LinnikGRH.DirichletRH`). So
  `ZetaBalance.PairBound` gives `LinnikGRH.linnik_two` and `LinnikAlmostAll.almostAll_one`, conditionally on the
  half-plane.
- **The corollaries of the top.** `lib/pnt/RHHarvest.lean` turns `HalfPlaneGRH.RHandGRH` into the classical
  consequences of RH and GRH, through the library's results for a zero-free half-plane at `1/2` (listed in the
  index's "Conditional results"). So they too follow from `ZetaBalance.PairBound`, conditionally on the half-plane.

- **The frame inequality**, `SlopeFrame.frame_inequality`. Sources `N_i` map to one target `C`. Suppose Bost's slope
  inequality holds on the images, and the images spread their ranks. Then the mean slope of the `N_i`, less the heights
  of the maps, bounds the slope of `C` from below, up to `α·HH + β·u·log(1 + HH/u)`. It is proved for abstract
  lattices of sublattices with a rank and a degree. Under it, `GramVolume` gives volumes of parallelotopes, including
  Hadamard's inequality for maps (`GramVolume.vol_comp_le`).
- **Euclidean lattices satisfy its axioms.** The saturated sublattices of a discrete subgroup of a Euclidean space
  form such a lattice, with `deg = −log covol`. Bost's slope inequality holds on images (`EuclidLattice.bost`): a map
  of norm at most `e^h` lowers minimal slopes by at most `h`. Closure under sums holds (`EuclidLattice.supClosed`),
  because the covolume is supermodular. So Euclidean lattices and maps between them form frames
  (`EuclidLattice.frame`).
- **Heights averaged over places.** `PlaceLattice.bost` works with lattices that have places: pairwise orthogonal
  subspaces `V v`, and a class of saturated sublattices whose spans are balanced, meeting each `V v` in `1/|P|` of their
  dimension. Take a map of norm at most `e^{h_v}` on each `V v`, whose images and preimages keep to the classes. It
  lowers minimal slopes by at most the averaged height `|P|⁻¹ Σ_v h_v`, where `EuclidLattice.bost` loses the largest
  `h_v`. The proof is Hadamard's inequality place by place (`GramVolume.volLe_iSup`); Fischer's inequality joins the
  places, so the map need not respect any decomposition of the target. Such lattices form frames
  (`PlaceLattice.frame`).
- **Hermitian lattices** over the ring of integers `O_K` of a totally complex field `K` are such lattices
  (`HermitianLattice.balanced`). The span of an `O_K`-stable discrete subgroup has the same dimension at every complex
  place. The proof uses only that `O_K` spans `K ⊗ ℝ`, and a count of ranks: the `O_K`-span of `d` vectors independent
  at one place has rank `d·[K:ℚ]`. `HermitianLattice.frame`: hermitian lattices and maps that commute with `O_K` form
  frames, with heights averaged over the places. These are the frames of the archive's `ch_top`, so the frames that
  the frontiers ask for (`ZetaBalance.LatticeData`) can be the archive's own.
- **The frame condition at one place.** `FrameAtPlace.FrameCond.codim_le`: let maps `B_ω : V_ω → W` of
  finite-dimensional real or complex inner product spaces be nearly isometric and nearly tight
  (`FrameAtPlace.FrameCond`):
  - `Σ_ω ‖B_ω*B_ω − 1‖²_HS ≤ e·Σ_ω dim V_ω`, with `e < 1`;
  - `dim W·tr Q² ≤ (1 + η)(tr Q)²` for `Q = Σ_ω B_ω B_ω*`, with `η ≥ 0`.

  If subspaces `N_ω ≤ V_ω` have total codimension at most `ε'·Σ_ω dim V_ω`, with `0 ≤ ε' ≤ 1`, then `Σ_ω B_ω(N_ω)`
  has codimension at most `(η + 2(√e + ε')/(1 − √e))·dim W`. The proof is Bessel's inequality and Cauchy–Schwarz for
  traces. `FrameAtPlace.FrameCond.codim_le_padded` measures it in a subspace of dimension at least `(1 − δ)·dim W`,
  at a cost of `(1 − δ)⁻¹`.
- **Complex-linear maps.** `FrameAtPlace.FrameCond.restrictScalars`: complex-linear maps that meet the condition over
  `ℂ` meet it over `ℝ` with the same `e` and `η`. Real dimensions are twice the complex ones, real traces twice the real
  parts of the complex ones (`FrameAtPlace.trace_restrictScalars`), and adjoints commute with restricting scalars, so
  both sides of (I) double and both sides of (T) quadruple.
- **Rank spreading from one place.** `PlaceLattice.spread_of_frameCond` and `HermitianLattice.spread_of_frameCond`:
  if multiples of the components of a frame's maps at one place meet that condition, the frame spreads ranks
  (`SlopeFrame.Frame.RankSpread`, the hypothesis (RS) of the frame inequality). The constants are
  `α = (1 − δ)⁻¹(η + 2√e/(1 − √e))` and `β = (1 − δ)⁻¹·2/(1 − √e)`. Ranks are read at the one place, as the spans of
  the class are balanced. The components are projections of the maps, so no `O_K`-linearity is used. For hermitian
  frames the place is a complex place of `K`, the components are complex-linear, and the condition is asked of them
  over `ℂ`, as the archive states it.
- **`O_K`-lattices with metrics at the places** (`lib/core/KLattice.lean`), the first layer of a sharp frontier
  (`docs/rh-rebuild.md`, "Next"). An `O_K`-lattice in `K^ι` with a positive definite hermitian metric `G v` at each
  complex place `v` is a hermitian lattice. Its realisation `x ↦ (A_v σ_v(x))_v`, with `A_vᴴA_v = G_v`, has inner
  products `Σ_v σ_v(x)ᴴ G_v σ_v(y)`, so it depends on the metrics alone (`KLattice.inner_ψ`). The metrics may be
  `K`-rational, `σ_v(H)` for an `H` hermitian for a star on `K` (`KLattice.isHermitian_map`), or only known to exist.
  - A `K`-linear map extends to the realisations (`KLattice.hom_ψ`).
  - A real-linear map that commutes with `O_K` is complex-linear at every place (`HermitianLattice.component`). So
    the frame condition at one complex place spreads ranks, with no padding at full rank
    (`KLattice.spread_of_frameCond`).
  - The index and the slope: for `O_K`-lattices `N ≤ M`, `μ(N) = μ(M) − log [M : N]/rk`, with `rk = [K:ℚ]·|ι|`
    (`KLattice.slope_withLattice`, `KLattice.rk_top`).
  - Scaling the metrics by `c > 0` lowers the degree by `(rk/2)·log c` (`KLattice.deg_scale`).
- **The layers of the sharp frontier, in progress** (`docs/rh-rebuild.md`, "Next"). Each defines objects that the
  frontier will state; their sanity theorems guard the definitions.
  - Units: frames in the archive's units, with every hypothesis and the conclusion of the frame inequality
    unchanged (`SlopeFrame.Frame.Spread.loss_le_rescale`, `SlopeFrame.Frame.loss_le_rescale_iff`,
    `SlopeFrame.Frame.slope_rescale`, `SlopeFrame.SlopeLattice.muMax_rescale`); the largest and smallest slopes
    (`SlopeFrame.SlopeLattice.muMin_le_slope_le_muMax`, `SlopeFrame.SlopeLattice.slopeGe_iff_le_muMin`); duals and
    saturation (`HermitianLattice.dual_anti`, `HermitianLattice.saturation_top`).
  - Classes: decorated unimodular hermitian lattices, the group acting on them, classes and mass weights
    (`HermClasses.instMulActionDeco`, `HermClasses.Lsh_of_isEmpty`, `HermClasses.dia_smul`, `HermClasses.mass_mk`,
    `HermClasses.act_ext_eLast`).
  - Coefficients: dual Weyl modules as polynomials, the Fock form and the lattices `Δ_N` (`WeylFock.hw_mem_nabla`,
    `WeylFock.DeltaOL_subset_DeltaN_std`).
  - The host: the CM field of a setting, of degree `4|A|`, and its CM type (`ZetaBalance.Setting.f_eq`,
    `ZetaBalance.Setting.card_gal`, `ZetaBalance.Setting.τ_eq`).
  - Forms: equivariant functions on decorated lattices with Weyl-module values, the integral forms, the Petersson
    form, the diamond operators and the ramified cut; the source as a `KLattice` with the per-place Petersson metrics
    (`HermForms.conj_pet`, `HermForms.dOp_mem`, `HermForms.gram_isHermitian`, `HermForms.source_G`). The metric at
    each place is the complex Petersson form, which agrees with `σ` of the `K`-valued form wherever the star is
    conjugation (`HermForms.petAt_eq_map`).
  - Forced orders: the explicit function `Fo` of the parameters that the frontier pins, with its linear program
    (`ZetaBalance.Setting.lpF_nonneg_le`, `ZetaBalance.Setting.Ranks.FTypeG_nonpos`,
    `ZetaBalance.Setting.Ranks.FInert_nonneg`).
  - Periods and target: the interlacing weight, the branching map, the period, the integral rows, the twisted
    target lattice `C_u` and the sources `N_ω` (`PeriodTarget.coeff_coefLast`, `PeriodTarget.per_eq_classSum`,
    `PeriodTarget.mem_Ctgt`, `PeriodTarget.Nsrc_le`).
  - The theta chain: Hecke and splitting characters, theta functions by the archive's recipe from an existential
    standard theta, jets, the kernels `κ_j`, the lifts and the chain; the local factors at the auxiliary places
    are a parameter with their invariance (`ThetaChain.opU_zero`, `ThetaChain.Chain.comp_zero`,
    `ThetaChain.Chain.lift_add`, `ThetaChain.detShift_wt_succ`); its top step maps straight to the row points,
    with the archive's coupled and top factors (`ThetaChain.Top.col_of_isEmpty`).
  - The frontier: `ZetaBalance.rhAndGRH_of_sharpBound` gives RH with GRH from `ZetaBalance.SharpBound`, through a
    proved bridge to the six-term interface (`ZetaBalance.SharpData.nonempty_sixTermData`,
    `ZetaBalance.SharpData.toSixTermData_Fo`): defined sources, target and periods, the forced orders fixed, and
    nonnegative slacks. `ZetaBalance.rhAndGRH_of_sharpBoundPinned` pins every object to the archive's construction
    (through `ZetaBalance.sharpBoundTheta_of_pinned`): the theta chain, its top step straight to the row points
    (`ThetaChain.Data.comp_zero_inp`, `ThetaChain.Top.col_of_isEmpty`, `ThetaChain.instMulActionDecoF`); the local
    factors read through the frames, with the level-T indicator, the archive's level groups at `SG` and `Q`, and
    representatives in its normal form at `Q` (`ThetaVol.volN_pos`, `ThetaVol.XiFull.scale`); the base theta by
    the archive's fourth-power identity, with the Weierstrass `σ` of a lattice of discriminant 1
    (`ThetaNorm.th0_zero`, `ThetaNorm.F0_zero`, `ThetaNorm.sgStar_zero`); and the row space as the image of a
    character idempotent on Weyl-module-valued forms equivariant under the archive's row level groups
    (`RowSpace.idemOf_empty`, `RowSpace.map_Amb_eq_range`, `RowSpace.tyPt_mul`, `RowSpace.tyRep_apply`). The last
    of twelve adversarial audits finds it true, up to inferred steps, and with no trivial witness. Existential:
    the archive's own freedom (the cusp subspace, the twist characters within their shape, the transfers, the
    target metric, unit phases).
  - The architecture of the proof: `ZetaBalance.sharpBoundPinned_of_inputs` gives the frontier from the deep inputs,
    stated as hypotheses (`ZetaBalance.SharpInputs`), and the pieces to prove (`ZetaBalance.SharpPieces`), each
    discharging named clauses; the reduction is logical packaging, checked against the frontier on every build.
  - The pieces proved so far. Finitely many classes of decorated unimodular hermitian lattices, each with a finite
    stabiliser (`HermClasses.finite_DCl`, `HermClasses.finite_stab`), by Minkowski's theorem and a covolume bound
    through the trace dual: the piece `ZetaBalance.FiniteClasses` (`ZetaBalance.finiteClasses_proved`). Bideterminants
    span the dual Weyl module (`WeylFock.bidet_mem_nabla`, `WeylFock.span_bidet`), by a reproducing formula for the
    Fock form and Cauchy–Binet. From them the piece `ZetaBalance.FormsLattice` (`HermForms.formsLattice`,
    `ZetaBalance.formsLattice_proved`): the forms finite-dimensional, the integral forms a lattice, and the Petersson
    form positive definite at every complex place.
  - The index bookkeeping (V): two `O_K`-lattices with the same metrics, neither inside the other, have slopes
    differing by `(log [N : N ∩ M] − log [M : N ∩ M])/rk` (`KLattice.slope_withLattice_eq`; doubled in the archive's
    units, `KLattice.slope_rescale_withLattice_eq`), through `N + M` and the second isomorphism theorem. So the piece
    `SharpObj.SlopeFV` follows from the slope bound on `M_ω` alone, in the frame's coordinates and the archive's units
    (`ZetaBalance.SharpObj.slopeFV_of_slopeM`). That `M_ω` is a lattice, in any coordinates and for any subspace
    `X_c` of the pins, holds for antitone weights (`HermForms.isLattice_span_Mω`,
    `ZetaBalance.SharpObj.isLattice_map_M`).
  - The core of the auxiliary primes (T), from the input `ShortNorm` at `h = 1`: primes `T = ππ̄`, `π ≡ 1 (mod M)`, in
    every dyadic window `(e^Λ, 2e^Λ]` once `log(4dM²) ≤ c√Λ` (`ZetaBalance.exists_prime_norm_window`), so meeting
    `ArithT` with `log T` within `log 2` of any large target (`ZetaBalance.SharpDesign.exists_prime_arithT`).
  - The slope bound (F), exact. (A first bound, from a spanning family of short integral forms and Hadamard's
    inequality, cannot fit the budget: the comparison constants of the representatives carry the level-`T` denominators,
    and `log κ` alone is of the budget's size; it is removed.) For the integral forms of the whole cut in any
    coordinates with the Petersson metrics, in the archive's units, `μ ≥ −(3|ν| log n + 2(Σλ)⁺·Σ_{P∈ST} log
    N(P)/(n[E:ℚ]) + |ST|·log 2)` (`HermForms.muArch_source_ge`), with no stabiliser orders, class representatives, `κ`
    or constants of the coefficient field (whose discriminant cancels). The degree of the lattice of integral
    polynomials of every `O_E`-lattice is exact, through a pseudo-basis, the determinant of `ρ_λ` and fractional ideals,
    so unimodular lattices all have the standard degree and the level-`T` ones differ by an explicit term; the standard
    one is bounded by integrality (a positive definite integer Gram determinant, no hook formula); stabilisers are
    trivial and the diamond action on classes free when the level group is unipotent at places over two primes (step 0);
    and the cut is a sum of `2^{|ST|}`-scaled copies of the class lattices, so Fischer's inequality applies. The piece
    `SharpObj.SlopeFV` follows for an object whose sources are the whole cut, with antitone weights and `c_F` at least
    the exact constant within the budget (`ZetaBalance.SharpObj.slopeFV_exact`).

## How the statements differ from the archive's

- **The window bound is weaker.** `WindowBound` is the bound for the cyclic family of each primitive character, the
  archive's `Level.cyc` with its `Gm`. It allows any window ratio `λ > 1` and any constant `C`, where the archive's
  argument delivers `λ = 3/2` and `C = 1`.
- **More general.** Landau's theorem on windows is proved for any family with positive weights, and abstractly for
  Laplace transforms with simple poles.
- **Less input.** No symmetry of `L(s, χ)` under conjugation is used: real parts are taken in the transform.
- **The balance for every `χ`.** Lemma B holds for every modulus `QS` and every subgroup `K`, so one setting serves
  `ζ` and every `χ`. It does not use the archive's twist of the Artin map for odd `χ`, which makes complex
  conjugation `(−1, −1, 1)`; that twist only fixes the coordinates in which the shares of the translates are asked
  for. The characters trivial on `A₀` are found by Fourier analysis on `A`, not counted.
- **The constants of rank spreading.** The archive's frame condition gives `α = (1 − δ)⁻¹(η + 4√e)` and
  `β = 4(1 − δ)⁻¹`. The library's, `(1 − δ)⁻¹(η + 2√e/(1 − √e))` and `(1 − δ)⁻¹·2/(1 − √e)`, are no larger when
  `e ≤ 1/4`.

## How it was formalised

The steps were written from the mathematics. Parts were written by helpers given only the statements and Mathlib.

- `WindowKernel`: the kernel `uᵏe^{−bu}/k!`, Chernoff's bound and the choice of `k` for a window.
- `WindowPole`: Taylor coefficients of Laplace transforms as moments (from `LandauLaplace`), Cauchy's estimate, and
  the coefficients near a simple pole.
- `WindowNearest`: the geometry of the nearest pole.
- `RampLaplace`: the transforms of the ramp sums.

`WindowGRH` treats `(s − 1)ζ(s)` and `L(s, χ)` alike, through `−F'/F(s) + s·F'/F(1)` over `s(s − 1)`. Mathlib's
`dslope` continues this across `s = 1`. For `ζ`, the function is Mathlib's `riemannZeta₁`, whose
`deriv_riemannZeta₁_one` gives the constant `γ`. That a nontrivial zero lies in the strip is the library's
`WeilTest.IsNontrivialZero.mem_strip`.

## Conditional results

| Result | Hypothesis | Lean |
|---|---|---|
| The Riemann hypothesis for `ζ` and for every Dirichlet `L`-function | `WindowGRH.WindowBound`: for every primitive `χ` and `θ > 1/2`, the weighted error of the ramp sums of the cyclic family of `χ` is at most `C x^θ` on windows `[Y, Y^λ]` with `Y` arbitrarily large | `WindowGRH.rhAndGRH_of_windowBound` |
| The Riemann hypothesis for `ζ` and for every Dirichlet `L`-function, also resting on the half-plane `Re s > 11/12` for `ζ` and every Dirichlet `L`-function, a result formalised in the library that no referee has read ([openai-half-plane.md](openai-half-plane.md)) | `ZetaBalance.PairBound`, the construction alone: for every primitive `χ` and every `ε₀ > 0` there are `ε ∈ (0, ε₀)` and `A ≥ 1` such that, for every large `Y`, every pair of primes `(q, d)` meeting `ZetaTwist.WinPair ε Y` has a sub-window `[Y′, Y′²]`, with `Y ≤ Y′ ≤ Y^{A/2}`, at every `x` of which a setting `S` with `S.q = q` and `S.d = d` and a character `κ` of `A` lifting `χ` (`ZetaBalance.Setting.Lifts`) has lattice data (`ZetaBalance.LatticeData S κ x ε X`) whose thin classes lie beyond `X = (Nx)^{log x}` | `ZetaBalance.rhAndGRH_of_pairBound` |
| The Riemann hypothesis for `ζ` and for every Dirichlet `L`-function, also resting on the half-plane `Re s > 11/12` for `ζ` and every Dirichlet `L`-function, a result formalised in the library that no referee has read ([openai-half-plane.md](openai-half-plane.md)) | `ZetaBalance.SixTermBound`: `ZetaBalance.PairBound` with six-term data (`ZetaBalance.SixTermData S κ x ε X`) in place of lattice data: weights and, at each translate of the kernel `A₀` of `κ`, a frame meeting the hypotheses of the frame inequality at its rank-weighted mean slope (`SlopeFrame.Frame.mean`), with numbers of its words (the slope of the forms, the split primes, the auxiliary prime) and of the translate (the vanishing gain, the forced vanishing, a scale `v > 0`, `log(g₀g₁)`, six slacks) that meet the archive's six inequalities G1–G6, and one budget for the slacks and the losses of the frame inequality | `ZetaBalance.rhAndGRH_of_sixTermBound` |
| The Riemann hypothesis for `ζ` and for every Dirichlet `L`-function, also resting on the half-plane `Re s > 11/12` for `ζ` and every Dirichlet `L`-function, a result formalised in the library that no referee has read ([openai-half-plane.md](openai-half-plane.md)) | `ZetaBalance.SharpBoundPinned`, the sharp frontier: `ZetaBalance.SixTermBound`'s shape with the frames realised by the construction's defined objects (sources from the forms with the Petersson metric, the target from the integral rows, the periods through the theta chain), each pinned to the archive's construction, with the forced orders fixed and nonnegative slacks; `ZetaBalance.SharpBoundTheta` is the same with fewer pins | `ZetaBalance.rhAndGRH_of_sharpBoundPinned`, `ZetaBalance.sharpBoundTheta_of_pinned` |
| The Riemann hypothesis for `ζ` and for every Dirichlet `L`-function, also resting on the half-plane `Re s > 11/12` for `ζ` and every Dirichlet `L`-function, a result formalised in the library that no referee has read ([openai-half-plane.md](openai-half-plane.md)) | `ZetaBalance.SharpInputs`, the deep classical inputs stated as hypotheses (Siegel–Weil, the covolume bound, good twists, the unitary mass formula, Howe duality, Lerch's formula, primes of norm in short intervals), and `ZetaBalance.SharpPieces`, the statements still to prove in the library (the construction's choices, finite classes, the forms a lattice, the parameters, the pins, the frame, the auxiliary primes, the slope bound and index, the gain, (G↑), (S) and (R)); their conjunction gives `ZetaBalance.SharpBoundPinned` | `ZetaBalance.rhAndGRH_of_inputs`, `ZetaBalance.sharpBoundPinned_of_inputs` |
| The Riemann hypothesis for `ζ` and for every Dirichlet `L`-function | `ZetaBalance.LatticeBound`: for every primitive `χ` and `ε > 0`, on windows `[Y, Y^λ]` with `Y` arbitrarily large, every `x` has a setting `S` with a character `κ` of `A` lifting `χ` (`ZetaBalance.Setting.Lifts`), thin at some `X`, with small twists (`ZetaBalance.Setting.Twists S κ`), and lattice data (`ZetaBalance.LatticeData S κ x ε X`): weights and, at each translate of the kernel `A₀` of `κ`, a frame meeting the hypotheses of the frame inequality, whose gain covers the inert-prime gap (G) with small losses (Z) | `ZetaBalance.rhAndGRH_of_latticeBound` |
| The Riemann hypothesis for `ζ` and for every Dirichlet `L`-function | `ZetaBalance.BalanceBound`: for every primitive `χ` of order `o` and `ε > 0`, on windows `[Y, Y^λ]` with `Y` arbitrarily large, every `x` has a setting `S` with a character `κ` of `A` lifting `χ` (`ZetaBalance.Setting.Lifts`), thin at some `X`, with the `3o` twists `g_{(α,β,κ^k)}`, `(α, β) ≠ (0, 0)` and `k < o`, at most `x^{1/2+ε}` at `x`, and balance data (`ZetaBalance.BalanceData S κ x ε X`): weights with thick classes in the kernel `A₀` of `κ`, of density at least `x^{−ε}` there, translates whose shares `Σ_t a_t κ(t)^k` lie within `x^{ε−1} Σ_t a_t` of `Σ_t a_t/(3o + 1)` for `0 < k < o`, and an inert-prime gap, averaged over `A₀`, at most `x^ε Σ_t a_t` | `ZetaBalance.rhAndGRH_of_balanceBound` |
| The Riemann hypothesis | `WindowGRH.ZetaWindowBound`: for every `θ > 1/2`, `Σ_{n≤x} Λ(n)(x/n − 1) − x log x + (1 + γ)x ≤ C x^θ` on windows `[Y, Y^λ]` with `Y` arbitrarily large | `WindowGRH.riemannHypothesis_of_zetaWindowBound` |
| The Riemann hypothesis, also resting on the half-plane `Re s > 11/12` for `ζ` and every Dirichlet `L`-function, a result formalised in the library that no referee has read ([openai-half-plane.md](openai-half-plane.md)) | `ZetaBalance.ZetaPairBound`, the construction alone: for every `ε₀ > 0` there are `ε ∈ (0, ε₀)` and `A ≥ 1` such that, for every large `Y`, every pair of primes `(q, d)` meeting `ZetaTwist.WinPair ε Y` has a sub-window `[Y′, Y′²]`, with `Y ≤ Y′ ≤ Y^{A/2}`, at every `x` of which a setting `S` with `S.q = q` and `S.d = d` has lattice data (`ZetaBalance.LatticeData S 1 x ε X`) whose thin classes lie beyond `X = (Nx)^{log x}` | `ZetaBalance.riemannHypothesis_of_zetaPairBound` |
| The Riemann hypothesis, also resting on the half-plane `Re s > 11/12` for `ζ` and every Dirichlet `L`-function, a result formalised in the library that no referee has read ([openai-half-plane.md](openai-half-plane.md)) | `ZetaBalance.ZetaTwistBound`: for every `ε > 0`, on windows `[Y, Y^λ]` with `Y` arbitrarily large, every `x` has a setting `S` with small twists (`ZetaBalance.Setting.Twists S 1`) and lattice data (`ZetaBalance.LatticeData S 1 x ε X`) whose thin classes lie beyond `X = (Nx)^{log x}` | `ZetaBalance.riemannHypothesis_of_zetaTwistBound` |
| The Riemann hypothesis | `ZetaBalance.ZetaLatticeBound`: for every `ε > 0`, on windows `[Y, Y^λ]` with `Y` arbitrarily large, every `x` has a setting `S` thin at some `X` (`ZetaBalance.Setting.Thin`), with small twists (`ZetaBalance.Setting.Twists S 1`), and lattice data (`ZetaBalance.LatticeData S 1 x ε X`): weights and, at each translate, a frame meeting the hypotheses of the frame inequality, whose gain covers the inert-prime gap (G) with small losses (Z) | `ZetaBalance.riemannHypothesis_of_zetaLatticeBound` |
| The Riemann hypothesis | `ZetaBalance.ZetaBalanceBound`: for every `ε > 0`, on windows `[Y, Y^λ]` with `Y` arbitrarily large, every `x` has a setting `S` thin at some `X`, with small twists, and balance data (`ZetaBalance.BalanceData S 1 x ε X`). The setting is thin when the errors are at most `θy` for `y ≥ X`, with `8|A|x²θ ≤ 1`, and its twists are small when the three quadratic twists are at most `x^{1/2+ε}` at `x`. The balance data are weights (`ZetaBalance.Weights`) whose inert-prime gap, averaged over translates, is at most `x^ε Σ_t a_t`, with `m ≥ x^{1/2−ε}` words, thick classes of density at least `x^{−ε}`, and `a_t/w ≥ X` on the thin classes | `ZetaBalance.riemannHypothesis_of_zetaBalanceBound` |
| GRH in the words of L. Alpöge's Lean archive (`LinnikGRH.DirichletRH`), the hypothesis of the library's results under GRH (`LinnikGRH.linnik_two`, `LinnikAlmostAll.almostAll_one`) | `HalfPlaneGRH.RHandGRH`, the Riemann hypothesis for `ζ` and for the `L`-function of every Dirichlet character, which `ZetaBalance.PairBound` gives, conditionally on the half-plane | `LinnikGRH.dirichletRH_of_rhAndGRH` |
