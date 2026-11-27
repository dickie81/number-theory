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
    So a bound on the averaged gap gives `Σ_{n≤x} Λ(n)(x/n − 1) − x log x + (1 + γ)x ≤ 7x^{1/2+6ε}`. The analytic
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
  Z, `ZetaBalance.BalanceData.cyclicG_le`, then bounds the family's error by `(9o − 2)x^{1/2+6ε}`, given the `3o`
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
- **The frame inequality enters through its conclusion.** Lattice data, six-term data and sharp data ask, at each
  translate, for a frame loss `L_u` with `s_u − μ(C_u) ≤ L_u`, not for the hypotheses of the frame inequality: the
  reductions read nothing else. A frame that meets those hypotheses gives the loss `αH + βU·log(1 + H/U)`
  (`SlopeFrame.Frame.Spread.frame_le`); for hermitian frames, the archive's route, from the frame condition at one
  complex place with the range and the depth, is `ZetaBalance.KFrame.frame_le_of_frameCond`. A construction may bound
  the loss more cheaply, for a frame of one word with no frame condition and no depth.
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
  - Forced orders: the archive's, an explicit function `Fo` of the parameters, with its linear program
    (`ZetaBalance.Setting.lpF_nonneg_le`, `ZetaBalance.Setting.Ranks.FTypeG_nonpos`,
    `ZetaBalance.Setting.Ranks.FInert_nonneg`).
  - Periods and target: the interlacing weight, the branching map, the period, the integral rows, the twisted
    target lattice `C_u` and the sources `N_ω` (`PeriodTarget.coeff_coefLast`, `PeriodTarget.per_eq_classSum`,
    `PeriodTarget.mem_Ctgt`, `PeriodTarget.Nsrc_le`).
  - The theta chain: Hecke and splitting characters, theta functions by the archive's recipe from a standard theta,
    jets, the kernels `κ_j`, the lifts and the chain; the local factors at the auxiliary places are a parameter with
    their invariance (`ThetaChain.opU_zero`, `ThetaChain.Chain.comp_zero`, `ThetaChain.Chain.lift_add`,
    `ThetaChain.detShift_wt_succ`); its top step maps straight to the row points, with the archive's coupled and top
    factors (`ThetaChain.Top.col_of_isEmpty`). The chain data carry no proofs, so a construction can define them: the
    standard theta is a bare function, and that it is a nonzero theta with rational jets is a predicate, which the
    pinned frontier asks.
  - The frontier: `ZetaBalance.rhAndGRH_of_sharpBound` gives RH with GRH from `ZetaBalance.SharpBound`, through a proved
    bridge to the six-term interface (`ZetaBalance.SharpData.nonempty_sixTermData`): defined sources, target and
    periods, forced orders chosen with the data (they cancel between (G↓) and (G↑); the archive's are `Fo` above), a
    frame loss and nonnegative slacks. `ZetaBalance.rhAndGRH_of_sharpBoundPinned` pins every object to the archive's
    construction (through `ZetaBalance.sharpBoundTheta_of_pinned`): the theta chain, its top step straight to the row
    points (`ThetaChain.Data.comp_zero_inp`, `ThetaChain.Top.col_of_isEmpty`, `ThetaChain.instMulActionDecoF`); the
    local factors read through the frames, with the level-T indicator, the archive's level groups at `SG` and `Q`, and
    representatives in its normal form at `Q` (`ThetaVol.volN_pos`, `ThetaVol.XiFull.scale`); the base theta by the
    archive's fourth-power identity, with the Weierstrass `σ` of a lattice of discriminant 1 (`ThetaNorm.th0_zero`,
    `ThetaNorm.F0_zero`, `ThetaNorm.sgStar_zero`); and the row space as the image of a character idempotent on
    Weyl-module-valued forms equivariant under the archive's row level groups (`RowSpace.idemOf_empty`,
    `RowSpace.map_Amb_eq_range`, `RowSpace.tyPt_mul`, `RowSpace.tyRep_apply`). The last of twelve adversarial audits
    finds it true, up to inferred steps, and with no trivial witness; it read the earlier form, with the forced orders
    fixed and the frame condition and the range and depth in place of the frame loss. Existential: the archive's own
    freedom (the cusp subspace, the twist characters within their shape, the transfers, the target metric, unit phases).
  - The architecture of the proof: `ZetaBalance.sixTermBound_of_inputs` gives the six-term frontier from the deep
    inputs, stated as hypotheses (`ZetaBalance.SharpInputs`), and the pieces to prove (`ZetaBalance.SharpPieces`), each
    discharging named clauses of sharp data; the reduction is logical packaging. It targets the six-term frontier, not
    the pinned one: nothing downstream reads the pins (the bridge discards the realisation), so the archive's objects
    enter only as the construction, with the properties the pieces' proofs use.
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
    `X_c`, holds for antitone weights (`HermForms.isLattice_span_Mω`,
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
  - The design, at the frontier's own scale: for every primitive `χ`, small `ε` and large `Y`, every pair of
    `ZetaTwist.WinPair` has, at every `x` of its window, a setting with a character lifting `χ` and an admissible design
    (`ZetaBalance.sharpParams`, from the input `ShortNorm`, which gives the split primes `g₀ ≠ g₁`). The design is the
    archive's: ranks `k ≈ x^{9/2+10ε}`, `m ≈ x^{1/2−ε/16}`, `t ≤ x^{401}`; one top place per translate, with tops drawn
    at random with coset counts close to the archive's (so the shares hold; Stage 2, below); a thick set of Behrend
    type, free of small-coefficient three-point relations; Harish-Chandra families by kind of place, with a shift making
    every root of unity act trivially; and the setting of the pair, whose discriminant is bounded through the cyclotomic
    field. Admissibility (`ZetaBalance.SharpDesign.Adm`) records what the pieces use, and gives the slope budget its
    sizes: the step-0 weights of every family pinned to a translate are antitone
    (`ZetaBalance.Setting.Ranks.wt0_antitone`) with `|ν|, (Σλ)⁺ ≤ 2Σ_t a_t` (`ZetaBalance.SharpDesign.Adm.sum_natW_le`,
    `ZetaBalance.SharpDesign.Adm.sum_wt0_le`), `log k ≤ 6 log x` (`ZetaBalance.SharpDesign.Adm.log_k_le`) and `[E:ℚ] ≤
    Σ_t a_t/x` (`ZetaBalance.SharpDesign.Adm.card_E_le`); and the auxiliary primes their window: `mx^ε/2 ≤ Λ_u ≤ 24mx^ε`
    (`ZetaBalance.SharpDesign.Adm.lam_bounds`), `Λ_u + log 2 ≤ x` (`ZetaBalance.SharpDesign.Adm.lam_add_log_two_le`),
    `(log 4dM²)³ ≤ Λ_u` (`ZetaBalance.SharpDesign.Adm.logM_cube_le`) and `16x^ε ≤ log(g₀g₁) ≤ 17x^ε`
    (`ZetaBalance.SharpDesign.Adm.log_g_mem`). The two random choices the gain needs, the 2-adic structure and the
    clause G1, are clauses of it (Stage 2, below).
  - The construction (`ZetaBalance.sharpCons`, `SharpChainU`): one word and one level per translate; the auxiliary
    prime `T` the least prime of `ArithT` in the window `(e^{Λ_u − x^{2ε}}, 2e^{Λ_u − x^{2ε}}]`, so `c_T = x^{2ε}`
    (`ZetaBalance.sharpCT`; the second-moment route to the period map's rank needs `T` below a threshold `T*` about
    `e^{x^{7ε/8}}` under `e^{Λ_u}`, and the shift costs `x^{2ε}Σ_t a_t` of the budget); the level-`T` places those of
    `conj((a + b√−d)/2)` and the places `SG` those of `conj π_{g₀}`, `conj π_{g₁}`, with the canonical `√−d` of `E`, a
    quadratic Gauss sum (`ZetaBalance.Setting.gaussE`); the step-0 weights the design's, and the sources the whole cut;
    the forced orders the archive's, and the frame loss its quarter of the budget. The period data are the explicit
    theta chain at Stage U (one word, one level, no twist; below): the row points at `SG`, the step-0 character
    `σ₀⁻¹ ∘ λ(ξ₀)` at `ξ₀ = −1/√−d`, the branching map with its constant and a Fock projection, and the top of the
    chain as the column. The coefficient field is the normal closure in `ℂ` (`CoeffField.coeffClosure`, a number
    field, totally complex, with conjugation as its star) of the images of `E`, the local constants at `SG`, the theta
    constants, the values of the lift characters and the chain's jets, when these generate a finite-dimensional field,
    and the setting's field otherwise. Everything is a definition: each takes its intended value when a fact holds (a
    choice exists, a map is linear or multiplicative, the field contains what it should), and the facts are left to
    the lemmas that use them. `𝔞⁺` and `𝔞⁻` are still placeholders, for the gain, and no proof reads them; the target
    metric is the quotient metric, with heights `0` (`SharpTarget`, below). For it, the pieces (T)
    (`ZetaBalance.sharpPrimes`, from `ShortNorm`) and (F) + (V) (`ZetaBalance.sharpSlopeFV`, from the exact slope bound,
    whose constant is at most `41·Σ_t a_t·log x`) hold eventually in the design.
  - The theta chain at Stage U, as closed definitions:
    - The canonical theta (`ChainCanon`): the CM lattice `Lc = δ(ℤ + ℤω)`, `ω = (1 + √−d)/2`, with `δ` the principal
      12th root of `Δ(ℤ + ℤω)`, so that `Δ(Lc) = 1` (`ChainCanon.discr_cmLat`); the form `s = 1/area(Lc) > 0`
      (`ChainCanon.sC_pos`) and the point `t = δ/2`, which meets the canonical pin's clauses (`ChainCanon.tC_spec`);
      the base theta of a step, a product of values of the canonical `G` (`ChainCanon.isTheta0_canonPin_iff`,
      `ChainCanon.slice_slot0`) with no fourth root taken, as every rank of the chain is even; and the theta
      constants, with `𝔄 = 𝔟⁻¹` (`ChainCanon.mem_ideA`).
    - The local data at `SG` (`ChainLocal`): the level groups, which are the archive's (`ChainLocal.levG_spec`), and
      the group of each step (`ChainLocal.levU_zero`, `ChainLocal.levU_of_ne_zero`); ideles from their components
      (`ChainLocal.ideleOf_apply`), with the single-place idele, the only one with its components
      (`ChainLocal.isLocAt_unique`, `ChainLocal.eq_idAtE`); the residue character, additive at a place of prime norm
      (`ChainLocal.psi0_add`); and the local parameters, which meet the pin `ThetaVol.LocOk` (`ChainLocal.locOk`).
    - The Heisenberg data (`ChainHeis`): the coset integers, and the representatives of the two quotients of a step
      (`ChainHeis.isReps_repsOf`, `ChainHeis.zero_mem_repsOf`, `ChainHeis.card_repsOf`), which give the pinned data
      `ThetaChain.XDPin` when both quotients are finite (`ChainHeis.xdPin_xdU`). The choice `sel` of one place out of
      every split pair fixes the parity rule of the gain: of two conjugate embeddings of the CM type at an inert prime
      at most one is even, and exactly one at a split place (`ChainHeis.not_evenPos_comp_conj`,
      `ChainHeis.evenPos_or_comp_conj`). The determinant ideles are built from uniformisers (`ChainHeis.unif_spec`),
      and their components form an idele when the frames are invertible (`ChainHeis.isIdeleFam_detComp`).
    - The coefficient field (`ChainField`): the `ℂ`-valued lift characters are chosen first (`ZetaBalance.muC_spec`;
      they repeat from step `m` on, `ZetaBalance.muC_of_le`), then the field, then the characters read in it, which
      are lift characters over it (`ThetaChain.Hecke.coe_restrict`, `ZetaBalance.isLift_muK`). The theta constants
      `g_p` are `h`-th roots of a generator of `𝔟^h` (`ZetaBalance.genB_spec`, `ZetaBalance.gτC_pow`,
      `ZetaBalance.coe_gτK`); the local constants carry the values of the residue characters and `√q_P`
      (`ZetaBalance.psi0_mem`, `ZetaBalance.sqrt_mem`); the jets are those whose rationality the chain's predicates
      ask (`ThetaChain.Data.jetsRat_iff`, `ThetaChain.Top.jetsRat_iff`). When the generators generate a
      finite-dimensional field, it contains them all (`ZetaBalance.subset_chainField`), and that reduces to the
      values of the characters and the jets (`ZetaBalance.kOk_of`).
  - The branching map is not forced to zero. The design's branching weight interlaces the column weight of every word
    family pinned to a translate, by the Harish-Chandra inequalities alone (`ZetaBalance.Setting.Ranks.interlace`,
    `ZetaBalance.SharpDesign.PinnedTo.interlace`). Under interlacing the branching constant is nonzero
    (`PeriodTarget.brConst_ne_zero`), and the weight is antitone (`PeriodTarget.antitone_of_interlace_right`), so the
    Fock projection exists (`PeriodTarget.exists_isFockProj`).
  - The frame inequality for one word (`SlopeSingle`): a hermitian frame with one word, whose map is onto, meets the
    frame inequality's conclusion with `e = dim ker B/dim V` and no frame condition
    (`ZetaBalance.KFrame.one_word_le`), by Bost's inequality at the quotient by the kernel sublattice
    (`KLattice.exists_ker_sublattice`). With the range, the frame loss is at most `(dim ker B/rk B)·U`, whatever the
    heights (`ZetaBalance.KFrame.frame_le_of_one_word`).
  - The frame loss of the construction, reduced to two named statements (`SharpNI`): (NI), the near-injectivity of the
    period map of the one word, `0 < rk P` and `dim V_ω ≤ 2 rk P` (`ZetaBalance.SharpNI`; not yet proved, the planned
    route is the whole-word second moment), and (R′), the range `μ_max(N_ω) ≤ μ(N_ω) + U` in every realising frame with
    `0 ≤ U ≤ x^{4ε}Σ_t a_t/4` (`ZetaBalance.SharpRange`, reduced below to gain certificates of small colength, the bound
    on `μ_max(M_ω)` being proved). In a realising frame the map is onto, as the target lattice lies in `W_u = range P`,
    and has the rank of `P`; so the one-word lemma bounds the loss by `U`, and the piece `frameLoss` holds eventually in
    the design (`ZetaBalance.frameLoss_of_sharpNI`), given (NI) and small certificates
    (`ZetaBalance.frameLoss_of_sharpNI_cert`, below).
  - The target metric (`SharpTarget`). The quotient metric of a linear map `P` and a form on its source, with Gram
    matrix `(σ_v(β)·P_v⁻¹·σ_v(β)ᴴ)⁻¹` on `range P`, is positive definite and makes `P` a co-isometry
    (`ZetaBalance.quotGram_spec`); the map of a co-isometry is a contraction (`KLattice.norm_hom_le_of_coisometry`), so
    a realising frame has heights `0`. A frame bounds `μ_g(C_u) + h̄_g` below by the quotient slope for any target
    metric `g`, so this one makes (G↑) as weak as it can be, and the construction takes it: the Petersson metric of the
    source pushed through the period map.
  - The integral rows (`RowsLattice`). `Δ_N ⊆ ∇_N` and `κ·∇_N ⊆ Δ_N` for the integer `κ = ⟨hw, hw⟩`
    (`HermForms.DeltaN_subset_nablaN`, `HermForms.kapN_smul_mem_DeltaN`), so every vector of `VV(σ)` has a nonzero
    integer multiple in `∇_N`, and `∇_N` has bounded denominators (`HermForms.exists_int_smul_mem_nablaN`,
    `HermForms.exists_coeff_twist_mem_nablaN`). Hence the integral rows span the row space and lie in a finitely
    generated `O_L`-module (`HermForms.rows_span`, `HermForms.rows_fg`).
  - The frame (`SharpFrame`). An object of one word whose period map has positive rank, with nonzero `𝔞^±`, no twist,
    the quotient metric, heights `0` and integral rows that span and lie in a finitely generated module, has a realising
    frame (`ZetaBalance.SharpObj.frameExists_of`): its sources and target are `O_K`-lattices with positive definite Gram
    matrices. So the piece `frame` holds for the construction given (NI) (`ZetaBalance.frame_of_sharpNI`, below,
    "Conditional results"), which it uses only for `0 < rk P`.
  - The gain's certificate (`GenIndex`, `GainCert`). The generalised index `logIdx X Y = log [X : X ∩ Y] − log [Y : X ∩
    Y]` satisfies the cocycle rule and is monotone (`AddSubgroup.logIdx_add`, `AddSubgroup.logIdx_mono`); scaling an
    `O_K`-lattice of dimension `d` by `γ` changes it by `−d·log|N(γ)|` (`Submodule.logIdx_smul`, with `[L : γL] =
    |N(γ)|^d` for integral `γ`, `Submodule.relIndex_smul`); finitely many local conditions cut out a sublattice of
    colength at most the sum of theirs (`Submodule.relIndex_inf_iInf_le`); and normalised norms do not depend on the
    field (`NumberField.log_abs_norm_map_div`). The gain's index term is `2·logIdx(N_ω, M_ω)/rk`
    (`ZetaBalance.SharpObj.idx_eq_logIdx`), and for principal `𝔞⁺ = (α)`, `𝔞⁻ = (β)` the source is `(β/α)M_ω ∩
    B_ω⁻¹(C_u)` (`ZetaBalance.SharpObj.N_eq_of_principal`). A certificate, `α`, `β` and a sublattice `L ⊆ M_ω` of finite
    index with `B_ω((β/α)L) ⊆ C_u`, sandwiches the source, `(β/α)L ⊆ N_ω ⊆ (β/α)M_ω`
    (`ZetaBalance.SharpObj.GainCert.le_N`, `ZetaBalance.SharpObj.GainCert.N_le`), with colength at most `[M_ω : L]`
    (`ZetaBalance.SharpObj.GainCert.colength_le`), and bounds the index term below by `(2/[K:ℚ])·log|N(α/β)| −
    (2/rk)·log[M_ω : L]` when `V_ω ≠ 0` (`ZetaBalance.SharpObj.GainCert.idx_ge`). So a certificate per word gives the
    gain (`ZetaBalance.SharpObj.gain_of_cert`).
  - The range (R′) (`SharpRangeCert`, `FormMuMax`, `SourceMuMax`). Scaling by `c ∈ K×` raises the degree of a sublattice
    by at most `h̄(c)` per rank (`KLattice.exists_smul_sublattice`), so for `N ≤ γM` of finite index `μ_max(N) − μ(N) ≤
    μ_max(M) − μ(M) + 2·log[γM : N]/rk` (`KLattice.slopeLe_rescale_of_le_smul`): no norm of `γ` enters. So a bound on
    `μ_max(M_ω)`, with (F) + (V), bounds the range of `M_ω` (`ZetaBalance.SharpObj.sourceRangeLe_of_muMaxLe`), and
    certificates carry it to `N_ω` (`ZetaBalance.SharpObj.rangeLe_of_cert`). For the construction,
    `ZetaBalance.SharpRange` follows from two named statements, the bound `ZetaBalance.SharpMuMax` on `μ_max(M_ω)` and
    certificates of small colength, `ZetaBalance.SharpCertSmall` (`ZetaBalance.sharpRange_of_cert`); the first is proved
    (next), so (R′) follows from the second alone. Integral coordinates `T` on a lattice, injective and dominated by the
    metric, `w·|σ_v(T)y|² ≤ yᴴG_v y`, give `μ_max ≤ −log w` (`KLattice.slopeLe_of_coord`); so for an object `μ_max(M_ω)
    ≤ −log w` from integral coordinates on the forms (`ZetaBalance.SharpObj.muMaxLe_of_coordCert`), and `SharpMuMax`
    follows from `ZetaBalance.SharpCoordCert`, such coordinates within the budget
    (`ZetaBalance.sharpMuMax_of_coordCert`, below), a route the twisted pairing makes unnecessary.
  - The maximal slope of the integral forms, `ZetaBalance.SharpMuMax`, proved (`TwistSlope`, `TwistPair`,
    `SourceMuMaxTw`, `SharpMuMaxProof`). For metrics `σ_v(E)ᴴ·diag(w)·σ_v(E)` from one weighted form and an automorphism
    `c` of `K` that is complex conjugation at one place, a twisted pairing with `D·h_c(x, y) ∈ O_K` on the lattice gives
    `μ_max ≤ log D` in the archive's units (`KLattice.slopeLe_of_twPair`): Cauchy–Schwarz for Gram determinants over the
    permutation of the places by `c`, and the integrality of the ideal `(det H)·c(∏I)·∏I`; the discriminant of `K`
    cancels, and no reduction theory or descent enters. The twisted Petersson pairing is integral: for an integer `m ≠
    0` in every place of `ST`, `m^{2n·negW(λ)}·H_c(F, G) ∈ O_L` on the integral forms (`HermForms.petTw_mem_of_Mint`),
    from the local duality of `Δ_Y` and `Δ_{Y^#}` (`HermForms.pair_mem_one`) and the shrinking `m^{n·negW(λ)}·Δ_{Y₂} ⊆
    Δ_{Y₁}` (`HermForms.pow_smul_mem_DeltaN_of_le`). So the source of the forms has `μ_max ≤ 2n·negW(λ)·log|m|`
    (`HermForms.slopeLe_source`), and at `m = T` this fits the budget: `SharpMuMax` holds eventually in the design
    (`ZetaBalance.sharpMuMax`). Hence (R′) follows from small certificates alone
    (`ZetaBalance.sharpRange_of_certSmall`), and the frame loss from (NI) and small certificates
    (`ZetaBalance.frameLoss_of_sharpNI_cert`), both below, "Conditional results".
  - The design's orbits (`GainConsts`, `DesignOrbits`): the gain's absolute constants, in one package. At an admissible
    design the non-split primes exceed `x^{ε/10}` (`ZetaBalance.Setting.DesignAdm.lt_of_cls_ne_split`) and have `2L₁(p)
    ≤ L₂` (`ZetaBalance.Setting.DesignAdm.two_mul_scL1_le`). The prime step's orbits on the translates have base points
    constant on them and positions (`ZetaBalance.basePoint_mul_pow`, `ZetaBalance.orbitPos_mem_topPositions`), V-type
    tops (`ZetaBalance.IsVType`), and collisions, described at inert primes and absent at signal primes
    (`ZetaBalance.Setting.collides_iff_of_inert`, `ZetaBalance.Setting.not_collides_of_signal`). The tile condition puts
    fewer than `r`, and at most `N₁`, tops in nearby windows and spaces the V-tops
    (`ZetaBalance.TilePar.IsGood.winCard_le_K`, `ZetaBalance.TilePar.IsGood.winCard_le_N₁`,
    `ZetaBalance.TilePar.IsGood.prevV_spec`), with the design's tile parameters meeting the side conditions
    (`ZetaBalance.tilePar_ok`). The scales lie in the window `W_a` (`ZetaBalance.SharpDesign.FamAt.aZ_mem_scWa`), and
    the window `W_b` of the top shifts is an explicit interval (`ZetaBalance.mem_scWb`); the candidates and the bad tops
    are defined (`ZetaBalance.Setting.cand`, `ZetaBalance.SharpDesign.badTops`). The non-split primes of small or odd
    order are sparse, `Σ log p/p ≤ y·log²X′·x^{−(2+7ε)}`, by the 2-adic structure of the pairs' settings
    (`ZetaBalance.pairSetting_twoAdic`, `ZetaBalance.Setting.TwoAdic.sum_log_div_le`,
    `ZetaBalance.Setting.DesignAdm.sum_log_div_smallOrder_le`).
  - The design's Stage 2 (`DesignTiles`, `ProdWeights`, `TileProb`, `TopsSelect`, `DesignG2`, with `SharpAdm` and
    `SharpParams`). Admissibility now holds the 2-adic structure of the setting (a clause of
    `ZetaBalance.Setting.DesignAdm`) and the clause G1, few tops on bad orbits (`ZetaBalance.SharpDesign.FewBadTops`,
    which reads the design only through its rank and its tops, `ZetaBalance.SharpDesign.fewBadTops_iff`); and the top
    data of a translate `t` sit at the place `(1, c·t)`, with `c = [−1]_A` for odd `κ` and `c = 1` for even `κ`. The
    tops are drawn at random, each element of `A` independently with probability `δ₁` on `A₀` and `3δ₁/4` off it, the
    probabilities being weighted finite sums (`ProdWeights`, with the counting tail
    `ZetaBalance.ProdWeights.ind_le_sum_powersetCard`). A marked block of the tile condition has probability at least
    `10^{−(6r+1)}` (`ZetaBalance.ProdWeights.pexp_marked_ge`), and one selection gives coset counts within `x⁻¹|TT|`,
    the density window `δ₁|A|/2 ≤ |TT| ≤ 2δ₁|A|` and G1 (`ZetaBalance.Setting.DesignAdm.exists_tops_G1`). Approximate
    counts give the shares (`ZetaBalance.shares_of_approx`), so admissible designs exist with these clauses
    (`ZetaBalance.Setting.DesignAdm.exists_design`, and `ZetaBalance.sharpParams`, below). The two Stage-2 clauses that
    read the local theory, the narrow window of the top shifts and G2, are stated (`ZetaBalance.SharpDesign.BTNarrow`,
    `ZetaBalance.SharpDesign.G2At`), with the box selection that will give them: a function on a box is at most its mean
    at some point of it (`ZetaBalance.exists_le_boxMean`). No theorem uses them yet.
  - The gain's exponents and numbers (`GainExponents`, `GainOrbit`, `GainAsk`, `GainSums`, `GainLoss`, `GainLoss2`,
    `GainErrors`, `GainCount`). The local exponents of the gain are explicit functions of the design, on the prime
    elements of `ℚ(√−d)` in `E`: the forced orders and the error exponents have signs
    (`ZetaBalance.SharpDesign.Fexp_rat_nonneg`, `ZetaBalance.SharpDesign.Fexp_gi_nonpos`,
    `ZetaBalance.SharpDesign.Fexp_sqrtd_nonpos`, `ZetaBalance.SharpDesign.Eexp_rat_nonneg`,
    `ZetaBalance.SharpDesign.Eexp_gi_sub_nonneg`, `ZetaBalance.SharpDesign.errT_nonneg`); the exponents `s_ϖ` at the
    special elements are explicit (`ZetaBalance.SharpDesign.sExp_gi`, `ZetaBalance.SharpDesign.sExp_gbar`,
    `ZetaBalance.SharpDesign.sExp_cut`, `ZetaBalance.SharpDesign.sExp_sqrtd`,
    `ZetaBalance.SharpDesign.sExp_rat_of_not_mem`); and the elements `α₀`, `β₀` whose images generate `𝔞^±` are nonzero
    (`ZetaBalance.SharpDesign.gainAlpha₀_ne_zero`, `ZetaBalance.SharpDesign.gainBeta₀_ne_zero`), with `λ(α₀/β₀) = Σ_ϖ
    n_ϖ·λ(ϖ)` (`ZetaBalance.SharpDesign.log_norm_gain`) and `λ(ϖ) = log N(ϖ)` at an admissible design when the auxiliary
    prime has the shape `ArithT` (`ZetaBalance.SharpDesign.lnorm_elt_of_adm`, `ZetaBalance.SharpDesign.arithT_sharpT`).
    So the certificate's norm term, through any `τ : E → K`, is `Σ_ϖ n_ϖ·log N(ϖ)`
    (`ZetaBalance.SharpDesign.log_norm_gain_map`); rounding costs at most `Σ_ϖ log N(ϖ)`
    (`ZetaBalance.SharpDesign.abs_sum_round_le`), and the gain at a prime is at most `4|TT|a/p`
    (`ZetaBalance.SharpDesign.gain_le`). On every orbit at an inert prime of even order the asks of the tops are paid by
    the served or the trivial gain, less penalty, depth and denominators (`ZetaBalance.SharpDesign.orbit_ineq`,
    `ZetaBalance.SharpDesign.orbit_ineq_tr`); the orbits cover at most `2|A|` positions
    (`ZetaBalance.SharpDesign.card_basePts_mul_le`), and over the orbits and the lifts the gains cover the asks
    (`ZetaBalance.SharpDesign.gains_ge_ask`). The frontier's ask is a finite sum over prime powers
    (`ZetaBalance.SharpDesign.ask_eq_sum`). With the twisted tops the orbit of a top meets the frontier's partners
    (`ZetaBalance.Setting.pos_twistTop`, `ZetaBalance.SharpDesign.wt_orbit`, `ZetaBalance.SharpDesign.sum_wt_filter`),
    so the gain's ask is the frontier's exactly, for odd `κ` as for even (`ZetaBalance.SharpDesign.askU_eq_askE`); the
    size of the gain at an admissible design gives the fallback of the colength
    (`ZetaBalance.SharpDesign.gain_le_of_adm`, `ZetaBalance.SharpDesign.fallback_le`). The growth package holds
    eventually (`ZetaBalance.gainBig_eventually`; the rank of the tile parameters does not read `x`,
    `ZetaBalance.tilePar_r`), and in a 2-adic setting a non-split prime of odd order is large
    (`ZetaBalance.Setting.TwoAdic.le_of_odd`). The losses, the frontier's asks less the gains net of the depths, are at
    most `c_G/4` (`ZetaBalance.SharpDesign.losses_le`), and so are the errors (`ZetaBalance.SharpDesign.errors_le`),
    with the rounding at most `c_G/12` (`ZetaBalance.SharpDesign.rounding_le`), `c_G ≤ x^{4ε}Σ_t a_t/8`
    (`ZetaBalance.SharpDesign.cG_le`), `log T ≤ Λ_u + log 2` (`ZetaBalance.SharpDesign.log_sharpT_le_lam`), the exponent
    sum by kinds (`ZetaBalance.SharpDesign.sum_sExp_logN`) and the forced orders summing to `Fo`
    (`ZetaBalance.SharpDesign.sum_Fexp_eq_Fo`). Together, for every `κ` and every `col ≤ c_G/6`, `Σ_t Σ_j ASK − m(Σ_t
    a_t)·log(g₀g₁) + Fo − c_G ≤ Σ_ϖ n_ϖ·log N(ϖ) − col` (`ZetaBalance.SharpDesign.gain_numbers`), given the 2-adic
    structure, G1, the growth package and error data meeting their bounds (`ErrOK`, which the providers of the error
    data are to prove). At an admissible design the first two are its clauses
    (`ZetaBalance.SharpDesign.gain_numbers_adm`).
  - The trace bound for (G↑) (`TraceSlope`): in the archive's units, the slope of a hermitian `O_K`-lattice `X` is
    computed through a pseudo-basis (`KLattice.slopeArch_pseudo`), and it is at least `−mean_v log(Σ_i ‖x_i‖²_v/|κ|)`
    for any vectors `x_i` of `X` that span (`KLattice.slopeArch_ge_of_span`; AM–GM, no Cauchy–Binet). With duality,
    `μ(X^∨) = −μ(X)` (`KLattice.slopeArch_dual`), vectors of the dual that span bound it above
    (`KLattice.slopeArch_le_of_dual_span`).
  - The local theory of the gain, at one inert prime:
    - The local model (`InertModel`): lattice tuples, their Weyl lattices, edges, levels, forms and Hecke operators. A
      lattice has finitely many edges below it (`InertModel.finite_edges`), each with a basis in Smith normal form
      (`InertModel.exists_basis_edge`); `p^{A_v}·Δ_{L″} ⊆ Δ_L` and `p^{A_v}·∇_{L″} ⊆ ∇_L` for an edge `L″ ⊂ L`
      (`InertModel.smul_mem_DeltaT_of_edge`, `InertModel.smul_mem_NablaT_of_edge`). So the Hecke operators keep the
      integral forms (`InertModel.hecke_mem_forms_DeltaT`, `InertModel.hecke_mem_forms_NablaT`), and those at
      different orbits commute (`InertModel.hecke_comm`). With finitely many classes and trivial stabilisers the
      integral forms are free of rank `#classes·dim ∇` (`InertModel.forms_free_DeltaT`, `InertModel.forms_free_NablaT`).
    - The local lattice problem (`LocalLattice`): the edge lattices and their duals for the Fock pairing, the source and
      target lattices, the problem `LLPAt` and its exceptional fraction `κ ∈ [0, 1]` (`LocalLattice.kappa_nonneg`,
      `LocalLattice.kappa_le_one`, `LocalLattice.kappa_le`, `LocalLattice.llpAt_of_kappa_lt`), with the pairings that
      smallness bounds (`LocalLattice.pairE_mem_of_small`); and its six model facts: the inclusions
      (`LocalLattice.nab_subset_edgeLat`, `LocalLattice.bdual_nab_le_edgeDual`, `LocalLattice.nab_subset_srcLat`,
      `LocalLattice.bdual_nab_le_tgtLat`), the perfect pairing (`LocalLattice.edgeLat_dualPair`,
      `LocalLattice.bdual_edgeDual`), an adapted basis (`LocalLattice.exists_adapted_basis`), spanning
      (`LocalLattice.exists_basis_NablaT`), duality, `∇(L)^∨ = Δ(L^∨)` (`LocalLattice.bdual_NablaT`,
      `LocalLattice.bdual_nablaB_dualLat`), which agrees with `∇(L^∨)` up to two nonzero integers
      (`LocalLattice.bdual_NablaT_compare`), and that one lattice suffices (`LocalLattice.llpAt_of_llpAt`,
      `LocalLattice.kappa_eq`).
    - The sandwich (`WeylSandwich`): `Δ_A ⊆ ∇_A` for every subring `A`, by a reproducing formula over sorted rows
      (`WeylSandwich.Delta_subset_nablaInt`), and `p^e·∇_O ⊆ Δ_O` over a local ring, by Legendre's formula for the
      multinomials (`WeylSandwich.pow_smul_mem_Delta`, `WeylSandwich.sandwich`); for lattice tuples and the local forms
      (`WeylSandwich.DeltaT_subset_NablaT`, `WeylSandwich.pow_smul_mem_DeltaT`, `WeylSandwich.forms_DeltaT_subset`,
      `WeylSandwich.pow_smul_mem_forms`). The exponent `e` is logarithmic (`WeylSandwich.sandExp_le`,
      `FockNorm.sandExp_le'`): the Fock norm of the highest weight vector is the product of the hook lengths
      (`FockNorm.kapN_formula`), by a Capelli identity in any ring with the Weyl relations (`FockNorm.capelli`).
    - The selection lemma (`SelectionLemma`): for commuting operators that are near-invertible on a common basis, the
      selected span meets `ϖ^τM` in colength at most `d·τ + Σ_v S_v·#{i : v ∈ A_i}` (`SelectionLemma.length_le`,
      `SelectionLemma.selection`), with the constant `1` where the plan had `2`. The plan's per-operator hypothesis
      makes the bound false: four copies of one shift give colength `10 > 8`.
    - The frame of the two local theorems (`LocalRank`): good systems at the edges assemble into the local lattice
      problem (`LocalRank.llpAt_of_rankAll`, `LocalRank.goodSys_of_primitive`), move between edges of one type
      (`LocalRank.goodSys_transport`), and are bounded by the number of edges (`LocalRank.goodSys_card_le`). The
      edges are subspaces of `L/pL`, so as many leave a lattice as enter one (`LocalRank.ncard_outEdges`), at least
      `q^{r(k−r)}` (`LocalRank.nEdges_ge`), and `(q^k − 1)/(q − 1)` of type `1` (`LocalRank.nEdges_one`). Smith's
      normal form splits a sum `Σ_j A_j = z·1` (`LocalRank.smith_split`) and gives the good rank
      (`LocalRank.goodRank_eq_smith`).
    - Tools: the Weyl dimension as a count of Gelfand–Tsetlin patterns, with its product formula
      (`WeylCount.dimW_eq_prod`), duality (`WeylCount.dimW_dual`), Pieri's rule (`WeylCount.dimW_mul_choose`), the
      flat weights `Har_m` and their sums (`WeylCount.dimW_flatW`, `WeylCount.sum_har`, `WeylCount.sum_prod_har`), and
      the counts of subspaces over a finite field (`WeylCount.pow_le_card_codim`, `WeylCount.card_hyperplanes`);
      Legendre's bounds for `v_p(m!)` (`PadicUnits.legendre_lower`, `PadicUnits.legendre_upper`), the factorial units
      (`PadicUnits.factorial_eq_unit`, `PadicUnits.norm_fUnit`) with their Mahler decay and the binomial
      approximation (`PadicUnits.exists_binomial_approx`), Jordan splitting over a discrete valuation ring with `2` a
      unit (`PadicUnits.exists_diagonal_congr`), and the Gram-window lemma (`PadicUnits.gram_window`).
    - The letter/Fock toolkit of the two local theorems (`LetterFock`), with their conventions fixed. The Frobenius
      congruence `σ^s(x) ≡ x^{p^s} (mod p)` (`LetterFock.frob_pow`); the lift substitution maps integral polynomials
      into the `ϖ`-graded integral subalgebra (`LetterFock.liftSub_mem_gInt`); the plane of a matrix, which gives the
      edge adapted to it (`LetterFock.planeOf`); the letter Fock form on monomials, its contravariance, and the
      uniqueness of contravariant forms (`LetterFock.lfock_monomial`, `LetterFock.lfock_letE`,
      `LetterFock.bilin_eq_lfock`). The flat model `θ°` (vector letters at even positions, signed cofactors at odd ones)
      maps onto `∇`, injectively and nondegenerately (`LetterFock.theta0_mem_nabla`, `LetterFock.theta0_injOn`,
      `LetterFock.theta0_surj`, `LetterFock.theta0_nondeg`), meets the shape condition (`LetterFock.theta_shape`),
      intertwines the letters with the row operators (`LetterFock.rowOp_theta0`) and compares the Fock forms, `nf(θ°P,
      θ°Q) = ⟨P, Q⟩/∏_s d_s!` (`LetterFock.nf_theta0`). `θ°P ∈ ∇_A` exactly when `P` has coefficients in `A`
      (`LetterFock.theta0_mem_nablaInt_iff`, `LetterFock.thetaB_mem_nab_iff`), and membership in the edge lattices is
      the order of the lift (`LetterFock.thetaB_mem_edgeLat_iff`).
    - Representations of `gl_n` in characteristic `0` (`GlRep`, `IsoProjectors`). The rank-one and rank-two lemmas
      (`GlRep.E_pfac`, `GlRep.E_pfac_pfac`) make the extremal projector killed by the consecutive raising operators,
      hence by all (`GlRep.kill_of_chain`); it fixes highest weight vectors, kills the lowering images, and on a
      dominant weight space projects onto the highest weight vectors (`GlRep.xproj_of_hw`, `GlRep.xproj_lowSp`,
      `GlRep.isHw_xproj`). The Casimir is central, acts on a highest weight module by `casVal λ`, and `casVal` is
      strictly monotone on dominant weights (`GlRep.cas_comm`, `GlRep.cas_gen`, `GlRep.casVal_lt`). So highest weight
      vectors generate a finite-dimensional stable subspace (`GlRep.le_hwSum`, `GlRep.hwSum_eq`), a highest weight
      vector in the lowering images is `0` (`GlRep.hw_eq_zero_of_mem_lowSp`), and the isotypic parts are independent and
      exhaust it (`GlRep.isoPart_indep`, `GlRep.iSup_isoPart`). Type projectors are equivariant and commute with the
      weight projections, with equivariant operators and with the type projectors of a commuting action
      (`GlRep.typeProj_E`, `GlRep.typeProj_comp`, `GlRep.typeProj_comm`, `GlRep.typeProj_comm_typeProj`); on a dominant
      weight space the extremal projector is the isotypic one (`GlRep.xproj_eq_typeProj`); invariant forms vanishing on
      highest weight pairs vanish (`GlRep.invForm_zero`); and the isotypic projector is an integer multiple of an
      average over `End W` (`GlRep.isoAvg_spec`). Over `ℚ_p`, on a lattice closed under divided powers, the highest
      weight projector loses at most `p^{projExp}` and the isotypic and type projectors `p^{2·projExp}`, `projExp = C(n,
      2)·⌊log_p(l + n − 1)⌋` (`GlRep.hwProj_int`, `GlRep.isoProj_int`, `GlRep.typeProj_int`), with Kostant integrality
      for isotypic vectors (`GlRep.kostant_int`).
    - Frobenius-twisted column states at an inert prime (`TwistedDegree`, T9f). They are integral and weighted
      homogeneous (`TwistedDegree.twCol_int`, `TwistedDegree.twCol_deg`); for every `g` over `W` with unit determinant
      the lift has order at least the column's cost, under the column conditions alone (`TwistedDegree.twCol_ord`),
      which joined paths meet (`TwistedDegree.JoinCond.colCond`); and at `g = 1`, for joined paths with strict
      positions, it is `ϖ^{cost}` times the Frobenius twist of the plane-tangent state modulo `ϖ^{cost+1}`
      (`TwistedDegree.twCol_cong`), the plane state being one monomial, or constant without a plane box
      (`TwistedDegree.colK_plane`, `TwistedDegree.colK_plane_const`).
    - Pieri paths and the path family (`PathBasis`, T2's objects and count). The column states are multilinear
      (`PathBasis.colK_isWH`); each letter of a Pieri path changes exactly `B_t` column heights, by at most one
      (`PathBasis.PieriPath.card_change`, `PathBasis.PieriPath.colH_step`), so the path polynomial has multidegree `B`
      and its columns `c ≥ 1` meet T9f's column conditions (`PathBasis.PieriPath.pathPoly_isWH`,
      `PathBasis.PieriPath.colCond`); it is the product over any window, and is defined over `ℤ`
      (`PathBasis.pathPoly_eq_prod`, `PathBasis.pathPoly_map`); the canonical filling is standard
      (`PathBasis.isStdFilling_canFill`). The standard fillings of `λ` number `dimW λ` (`PathBasis.card_stdFilling`),
      and with Pieri's count over the paths (`PathBasis.sum_dimW_paths`) the path family (`PathBasis.pathFam`) has `∏_t
      C(B_t + m, m)` members (`PathBasis.card_pathIdx`), the number of monomials of multidegree `B`; it is a basis
      (below).
    - The shared vocabulary of the two local theorems (`LocalOrbit`, `SymbolData`, `ChainData`). Orbits: the previous
      V-top is attained (`LocalOrbit.prevVDist_spec`), parity is well defined on positions
      (`LocalOrbit.even_posOf_iff`), and L5's segment condition and the tile condition are defined (`LocalOrbit.SegOK`,
      `LocalOrbit.IsGoodSet`). Frames: the rows of a late letter are `r` increasing even letters of its segment before
      it, all of those from the anchor on (`LocalOrbit.FrameSys.rows_mem`, `LocalOrbit.FrameSys.rows_strictMono`,
      `LocalOrbit.FrameSys.Proper.le_card_evBefore`, `LocalOrbit.FrameSys.card_evBefore_ge_anchor`); the anchor is a
      letter of the segment and not a row (`LocalOrbit.FrameSys.Proper.anchor_mem_seg`,
      `LocalOrbit.FrameSys.Proper.anchor_lt_f`); the first letter of a segment has the largest push, and the anchor is
      pushed more than `L₁` further than its letter (`LocalOrbit.FrameSys.push_le_push_first`,
      `LocalOrbit.FrameSys.Proper.push_add_lt_push_anchor`); a top between the first and the last row of a frame is a
      row, so the late letters of a segment are its loose letters and its frame's rows, `nL j + r` of them, and the
      segment is these and the previous frame's rows (`LocalOrbit.FrameSys.Proper.exists_row_of_top`,
      `LocalOrbit.FrameSys.Proper.late_eq`, `LocalOrbit.FrameSys.Proper.card_late`,
      `LocalOrbit.FrameSys.Proper.seg_eq`), enumerated in increasing order
      (`LocalOrbit.FrameSys.Proper.lateAt_strictMono`, `LocalOrbit.FrameSys.Proper.lateAt_mem_late`); segments, late and
      loose letters and pushes are periodic (`LocalOrbit.FrameSys.Proper.seg_add_J`,
      `LocalOrbit.FrameSys.Proper.late_add_J`, `LocalOrbit.FrameSys.Proper.loose_add_J`,
      `LocalOrbit.FrameSys.Proper.nL_add_J`, `LocalOrbit.FrameSys.Proper.push_add_J`); the late letters of one period
      read every top once (`LocalOrbit.FrameSys.Proper.sum_late`, `LocalOrbit.FrameSys.Proper.sum_card_late`); and there
      are at least four frames (`LocalOrbit.FrameSys.Proper.lt_J_mul`, `LocalOrbit.FrameSys.Proper.three_lt_J`).
      Symbols: the twisted degrees of `0` (`SymbolData.valS_zero`, `SymbolData.topS_zero`), the `ϖ`-degrees, which sum
      to `nd` (`SymbolData.sum_piDeg`), N8's source margin and realisation gap (`LocalOrbit.FrameSys.cPrime`,
      `LocalOrbit.FrameSys.mStar`), the starred threshold, at least `B/2` (`LocalOrbit.FrameSys.half_B_le_thrStar`), the
      Frobenius push of a segment (`LocalOrbit.FrameSys.segPush_X`), the symbol generators
      (`LocalOrbit.FrameSys.symGen`), and the one-sided elements, `0` among them
      (`LocalOrbit.FrameSys.isOneSided_zero`). Chains: the letters' `gl_n` action, with its commutation relations and
      weights, as a representation stable on the finite-dimensional multidegree components (`ChainData.letES_X`,
      `ChainData.letES_comm`, `ChainData.isWH_derivation`, `ChainData.letES_X_isWH`, `ChainData.letES_X_isWH_row`,
      `ChainData.letES_diag_X`, `ChainData.letES_diag_of_isWH`, `ChainData.letterRep`,
      `ChainData.finiteDimensional_LHom`, `ChainData.letterRep_stable`); the model map, the conditions `𝒴` and `H`, and
      the constants `D_m`, `D_l`, `κ_p`, `n₀` (`ChainData.modelMap`, `ChainData.IsY`, `ChainData.HCond`, `ChainData.Dm`,
      `ChainData.Dl`, `ChainData.κp`, `ChainData.n₀`); and the single membership condition of the local theorems
      (`LocalOrbit.FrameSys.Mem`).
    - The path basis (`PathSpan`, `PathStraighten`, T2). No monomial order gives the path polynomials distinct leading
      terms, so the basis comes from a straightening law. A path is read through its column heights and column states,
      wedged with a letter when a height grows and contracted when it drops; the inversion counts of the empty set and
      of singletons (`PathSpan.inv_empty_left`, `PathSpan.inv_singleton_left`) make the letter signs inversion signs
      (`PathSpan.sg_eq_sgn`). Under one more letter the Garnir sums of two states are signed sums of Garnir sums of the
      old states, and Fulton's exchange and symmetry relations follow from them by Möbius inversion. Every Garnir sum of
      a path lies in its lower part, the span of the paths below it in the lexicographic order of the potentials
      (`PathSpan.garnir_step`, `PathSpan.garnir_all`), so every `Ψ(P, C)` lies in the `ℤ`-span of the standard `Ψ(Q, I)`
      with `Q ⪯ P` (`PathSpan.straighten`). These span, by the first-row trick, and they number the monomials of
      multidegree `B` (`PathSpan.card_monomials`, `PathBasis.card_pathIdx`): the path family is a basis of the
      polynomials of multidegree `B` over every commutative ring (`PathBasis.pathFam_basis`,
      `PathBasis.pathFam_basis_apply`).
    - The capacity spans (`TwistWeights`, `CapStates`, `CapacityWeights`, `CapacityTop`, `CapacitySpan`, T3). The
      twisted degrees `val_S`, `top_S` of `SymbolData` are read off the weights of one polynomial, the generic translate
      `gtr F` (`x_l ↦ x_l·adj(g)` at the vector letters of `S`, `x_l ↦ g·x_l` at its covector letters, `g` the generic
      matrix): the twisted substitution factors through it (`TwistWeights.twistSub_eq_comp`), and over a domain its
      exponents at the column `c` are the `c`-th coordinates of the weights of `gtr F` (`TwistWeights.twistExps_eq`,
      H1), so `θ ≤ val_S F` iff every weight `ν` has `θ ≤ ν_{n−1}`, and `top_S F ≤ M` iff every weight has `ν_0 ≤ M`
      (`TwistWeights.le_valS_iff`, `TwistWeights.topS_le_iff`). Column states are runs of wedge and contraction steps,
      which a change of frame transforms by the induced action on states (`CapStates`), so the weights of the translate
      through the first `i` letters of a path polynomial `Ψ(P, I)` are dominated by `μ_i` (E1): `val_{<i} Ψ(P, I) ≥
      μ_i(n − 1)` and `top_{<i} Ψ(P, I) ≤ μ_i(0)` (`CapacitySpan.valS_pathPoly`, `CapacitySpan.topS_pathPoly`, V4). The
      weight-`μ_i` components factor, up to signs and powers of `det g`, through the path polynomials of an extended
      word under an injective substitution, so they are linearly independent
      (`CapacitySpan.gcomp_top_linearIndependent`, E2 and E3; `g` generic is essential). Hence T3: at checkpoints `i`
      with bounds `θ_i`, `M_i`, the path-basis coordinates of a polynomial of multidegree `B` with `θ_i ≤ val_{<i}` and
      `top_{<i} ≤ M_i` (the capacity set) vanish off the paths with `θ_i ≤ μ_i(n − 1)` and `μ_i(0) ≤ M_i`
      (`CapacitySpan.repr_eq_zero_of_mem_capSet`), so over every domain the capacity set is the span of the admissible
      path polynomials (`CapacitySpan.capSet_eq_span`; the inclusion `⊇` holds over every commutative ring,
      `CapacitySpan.span_subset_capSet`). Over a field its dimension is the chain sum, `Σ dimW(μ_N)` over the admissible
      paths (`CapacitySpan.finrank_capSpan`, `CapacitySpan.card_capOK`); membership is detected after an injective
      coefficient map (`CapacitySpan.mem_capSet_map_iff`), and a surjection of domains, such as `O → k`, maps the
      capacity set onto the capacity set (`CapacitySpan.capSet_image_map`).
    - The first local theorem, L5 (`FirstMeans`, `FirstAssembly`, `OffTop`, `FlatDimPf`, `HarmDecomp`, `TwoLetter`,
      `HarmSplitPf`, `FirstCloudBase`, `FirstCloudEdge`, `FirstCloudCount`, `FirstCloudPair`, `FirstCloudDim`,
      `FirstCloud`, `WeylDimPf`, `HwSatPf`), at one orbit of an inert prime in the setting `Unram`. The windows, the box
      mean, the depths and the numeric hypotheses are `FirstMeans`', with box sums monotone (`FirstMeans.boxSum_mono`),
      the shifts multiplying over the tops (`FirstMeans.prod_sum_rho`) and the extension by `0` additive
      (`FirstMeans.ext_add`). Good systems pass to sub-systems (`FirstAssembly.goodSys_le`) and split over the flat
      pieces of the tensor of polynomial pairs, at denominator `D + 2u` (`FirstAssembly.goodSys_split`); so `Σ_j
      κ_F·d(fl_j) ≤ κ_X·dim H(A, B)` (`FirstAssembly.key_ineq`), the box sums of the flat exceptional fraction are at
      most `(4/3)|W_A|^N|W_B|^N(C_P + C_A)N·N₁/Y` (`FirstAssembly.boxSum_kappaF_le`), and the per-weight assembly
      (`FirstAssembly.llp_first`) gives the first local theorem (`FirstAssembly.first_local`): a per-orbit fraction `κ`
      with box mean at most `C·N·N₁/Y`, and the local lattice property at every lattice. Its inputs are named
      statements, arguments of the theorem, for the later modules to prove: `FirstAssembly.InputRank` (I1, the rank
      theorem of layer 2), `FirstMeans.SegMean` (I2, the segment mean of layer 3), the bound I3 on `κ_P`,
      `FirstAssembly.HarmSplit` (the harmonic splitting), `FirstAssembly.FlatDim` (the dimensions of the flat pieces),
      `FirstAssembly.CloudStep` (the cloud step) and `FirstAssembly.OffTop` (the off-top step). The last is proved:
      `∇(λ)` factors into its top and off-top parts and the Fock form is multiplicative over disjoint variables, so a
      good system of the top part gives one of the weight, edge by edge (`OffTop.goodSys_offTop`);
      `FirstAssembly.OffTop` holds (`OffTop.offTop`), and the theorem holds without it (`OffTop.first_local'`, below,
      "Conditional results"). Two more inputs are proved and a third is reduced to one classical input; the versions of
      the theorem without them are there too. `FirstAssembly.FlatDim` holds for `k ≥ 2`
      (`FlatDimPf.flatDim`; without it, `FlatDimPf.first_local_flat`). At a top the block shape of a flat weight is `(p
      + q, q, …, q, 0)`, whose bideterminants are the images, under `X_{0,a} ↦ v_a`, `X_{1,a} ↦ η_a` (`v` the column `0`
      of `x`, `η` the last row of `adj(x)`), of polynomials of multidegree `(p, q)` in a vector and a covector letter;
      the path polynomials span these (T2), those whose Pieri path has `j ≥ 1` are killed (their column `p` reads `⟨v,
      η⟩ = 0`), and the rest number `Har` (`FlatDimPf.flatDim_le`, the half `FirstAssembly.key_ineq` uses); the path
      polynomials of the canonical row path lie in `∇` once placed in a block, and their products over the blocks are
      independent, which gives the other half. `FirstAssembly.HarmSplit` holds in the setting `Unram` for `k ≥ 3`, with
      Annex I's `u` and `a_max = 8a` (`HarmSplitPf.harmSplit`, from `HarmSplitPf.harmSplit_of`, for an `O` in which the
      integers prime to `p` are invertible; without it, `HarmSplitPf.first_local''`). For two letters with pairing `h =
      Σ_c X_{a,c}X_{b,c}` and pair Laplacian `Δ`, explicit operators `f_j`, with inverses of binomial coefficients as
      coefficients, split a polynomial as `Σ_j h^j·f_j` with `Δf_j = 0`, losing at most `p^{(k + 1)⌊log_p(u + 2i)⌋}` on
      integral polynomials (`HarmDecomp.fj_mem_intP`); at several positions `F = Σ_j (∏_s h_s^{j_s})·π_j(F)`
      (`HarmDecomp.Pairs.sum_piL`), the losses of the projectors adding (`HarmDecomp.piL_mem_intP`). `H(A, B)` and the
      flat weights are both images of letter polynomials, two letters per position (`TwoLetter`, I4), the flat model
      being injective on the polynomials harmonic at every position (`TwoLetter.eq_zero_of_beta`, by evaluation at test
      matrices whose last cofactor row is a scaling modulo the pairing); the splitting maps are the projectors `π_j`
      read through the two models, and their twists by block lattices lose exactly what the twist constants absorb. The
      cloud step `FirstAssembly.CloudStep` holds for `b′ > 0` and `k ≥ 2` given three classical inputs, named statements
      (`FirstCloud.cloudStep`; with them in its place, `FirstCloud.first_local''`): the Weyl dimension formula for `∇`
      (`FirstCloud.WeylDim`, I8); the cloud pairing, an equivariant, integral contraction `V(λ) × V(μ*) → V(H⁺)` with
      top cloud vectors `s_b`, `s′_a`, `Con(F·s_b, s′_a) = δ_{ab}p^{κ_a}F·hw(fl₂)` and `κ_a ≤ D_c`, as many as the Weyl
      dimension of the middle entries (`FirstCloud.CloudPair`, I5 with the contraction of N16); and the saturation of
      multiplication by a highest weight vector (`FirstCloud.HwSat`, the domain half of I6). At one edge, a good system
      at `H = fl(A, B)` gives targets at `H⁺ = fl(A + 2c, B + 2c)` through `·hw(fl₂)`
      (`FirstCloud.exists_retract_targets`), a good system at `H⁺` leaves `r` combinations of its sources with
      `#edges·(n₁ − r + n₂) ≤ d(H⁺)` (`FirstCloud.cloud_count`), and the adjoints of the contractions with the `s′_a`
      are targets at `λ` (`FirstCloud.exists_adj_tgt`), so the edge carries a good system of size `m·r` at `λ`, `m` the
      number of cloud vectors (`FirstCloud.goodSys_cloud`, N16 and N17); with the dimensions, `m·d(H) ≤ d(λ) ≤
      e^ε·m·d(H)` and `d(H⁺) ≤ e^ε·d(H)`, `ε = 12Nkc/b′` (`FirstCloud.cloud_dims`), that is the rank the cloud step
      asks. Two of its inputs are proved. `FirstCloud.WeylDim` holds over every field of characteristic `0`
      (`WeylDimPf.weylDim`): block by block, the products of the standard row path polynomials span `∇`, since every
      bideterminant straightens along the row path, the least path of its word (`WeylDimPf.nabla_eq_span`); they are
      independent over every field (`WeylDimPf.stdProd_linearIndependent`) and number `∏_b dimW(ν_b)`
      (`WeylDimPf.finrank_nabla`). `FirstCloud.HwSat` holds over a discrete valuation ring with fraction field of
      characteristic `0` (`HwSatPf.hwSat`, from `HwSatPf.hwSat_blocks`): those products are bideterminants defined over
      `ℤ` and stay independent over the residue field, so Gauss's lemma and the saturation of `∇_O` run at once modulo
      the uniformiser. So the theorem holds from `FirstCloud.CloudPair`, `FirstAssembly.HarmSplit`, I1, I2 and I3
      (`HwSatPf.first_local_cloud`), and, `FirstAssembly.HarmSplit` being proved, the inputs of L5 not yet proved are
      the cloud pairing `FirstCloud.CloudPair` and I1, I2, I3.
    - The source side of the second local theorem, first part (`SourceKeys`, `SourceCore`, `SourceOneSided`; L6 N8). The
      explicit polynomials of N8 (pushed entries, plane determinants, even and odd keys, the localiser) under the
      adapted substitution `Φ_g`: `Φ_1` fixes the plane determinant of the rows (`SourceKeys.ad_one_Tp`), and the
      localiser vanishes off the main plane (`SourceKeys.locPoly_offPlane`, C1). Graded-integral polynomials are
      integral (`SourceCore.ordGe_of_gInt`), the key product is graded-integral and on the tops
      (`SourceCore.keyprod_gInt`), and the key-presentable polynomials contain the unscaled ones and are closed under
      products (`SourceCore.keyPres_unscaled`, `SourceCore.keyPresSpan_mul`). By the iteration lemma
      (`SourceCore.iterate`), a polynomial `Z·fixFactor(c) + p^c·Y` with `Z` key-presentable and `Y` integral is
      realisable at its level with margin `c` (`SourceCore.realise_core`, C4 at `g = 1`). For the one-sided realisation
      two interfaces to the toolkit are stated, named statements not yet proved, which no theorem uses yet:
      `SourceOneSided.GapZeroKeyed` (the push of a gap-0 pair is key-presentable) and `SourceOneSided.DetDiv` (C5 over a
      field: a power of the row determinant divides). With them come the budget determinants
      (`SourceOneSided.budgetDet`), the key presentation of the digit labels (`SourceOneSided.label_keyPres`) and the
      other-row degree bound, at most `B(j, x)/80` for `p ≥ 13` (`SourceOneSided.otherDeg_le`).
  - The CM theta, one variable (`CMThetaOne`, `CMThetaJets`). Mathlib has `℘` but not `σ` or `ζ`: `ζ_W′ = −℘`, `σ_W′ =
    σ_W·ζ_W` and `℘″ = 6℘² − g₂/2` are proved here (`CMThetaOne.hasDerivAt_zetaW`, `CMThetaOne.hasDerivAt_sigmaW`,
    `CMThetaOne.eqOn_deriv_derivWeierstrassP`), with the normalisation `th0(0) = 1` (`CMThetaOne.th0L_zero`).
    `CMThetaOne` derives the rest from Legendre's relation, stated as `CMThetaOne.Legendre`; `EllipticLegendre.legendre`
    proves it (below), and `CMThetaJets` states the results without it. Masser's half-period identity
    (`CMThetaOne.zetaW_half'`) and Hurwitz's formula (`CMThetaOne.th0_taylor'`) hold, and every jet of `th0` at a
    half-period `t` is a polynomial over `ℤ` in `g₂/2`, `℘(t)` and `s₂` (`CMThetaOne.th0_jets_mem'`,
    `CMThetaOne.th0_jets_mem_closure'`), so it lies in `σ₀(K)`, is algebraic and is `ℓ`-integral for `ℓ ≠ 2` wherever
    these do or are (`CMThetaOne.th0_jets_mem_range'`, `CMThetaOne.th0_jets_isAlgebraic'`, `CMThetaOne.th0_jets_int'`).
    At the construction's lattice `Lc` and point `t = δ/2` the jets lie in `σ₀(K)` when `g₂`, `℘(t)` and `s₂` do
    (`CMThetaOne.canon_jets_mem_range'`), and with the CM inputs they are algebraic and integral at every `ℓ ≥ 5`, `ℓ ∤
    d` (`CMThetaOne.canon_jets_isAlgebraic'`, `CMThetaOne.canon_jets_int'`, below).
  - The Weierstrass addition theory (`EllipticAdd`, `EllipticLegendre`, `EllipticDivisor`, `EllipticSigma`). The `σ`
    addition formula `σ(z + w)σ(z − w) = σ(z)²σ(w)²(℘(w) − ℘(z))`, by Liouville's theorem for elliptic functions
    (`EllipticAdd.sigmaW_add_mul_sub`), so `℘(z) = ℘(w)` exactly when `z ≡ ±w` (`EllipticAdd.weierstrassP_eq_iff`); the
    addition theorems of `ζ` and `℘`, and the duplication `σ(2z) = −℘′(z)σ(z)⁴` (`EllipticAdd.zetaW_add`,
    `EllipticAdd.weierstrassP_add`, `EllipticAdd.sigmaW_two_mul`); and the Laurent coefficients of `℘` at `0`, the
    formal recursion `wpC`, equal to `(2k − 1)G_{2k}` (`EllipticAdd.wpC_eq_lc`, `EllipticAdd.wpC_eq_G`,
    `EllipticAdd.hasSum_weierstrassP`). Legendre's relation `η₁ω₂ − η₂ω₁ = 2πi` (`EllipticLegendre.legendre`), by
    Cauchy's theorem on the fundamental parallelogram, which comes from Mathlib's divergence theorem on the square; so
    `η₁ω₂ − η₂ω₁ ≠ 0` in either orientation (`EllipticDivisor.legendre_ne_zero`). An elliptic function with poles only
    at the periods is `P(℘) + ℘′·Q(℘)` (`EllipticDivisor.EllPole.exists_poly`). For a torsion point `q ∉ Λ`, `Nq ∈ Λ`,
    the translate `G_q(z) = e^{−η(q)z}σ(z + q)/(σ(z)σ(q))` has `G_qᴺ` of that form (`EllipticDivisor.Gq_pow_eq_poly`), a
    simple pole of residue `1` at the periods and simple zeros exactly at `−q + Λ` (`EllipticDivisor.tendsto_mul_Gq`,
    `EllipticDivisor.Gq_eq_zero_iff`, `EllipticDivisor.hasDerivAt_Gq_neg`), with logarithmic derivative `ζ(q) − η(q) +
    ½(℘′(z) − ℘′(q))/(℘(z) − ℘(q))` (`EllipticDivisor.hasDerivAt_Gq`, `EllipticDivisor.logDeriv_Gq`). The Taylor series
    of `σ* = σ_W·e^{−s₂z²/2}` at `0` is the formal `σ*` of `CMFormalGroup` (`EllipticSigma.sgStar_taylor`,
    `EllipticSigma.sigE_taylor`), so identities of `σ*` near `0` are identities of the formal series.
  - The formal group at an inert prime (`CMFormalInert`, `CMFormalGroup`). The height-2 Lubin–Tate exponential has
    `π^{N−1}·e_N ∈ ℤ` for `π^{ℓ²−1} = ℓ` (`CMFormalInert.expLT_eq`, `CMFormalInert.pow_mul_coeff_expLT`,
    `CMFormalInert.norm_coeff_expLT_le`, `CMFormalInert.expLT_subst_logLT`), and `e_N = 0` unless
    `N ≡ 1 (mod ℓ² − 1)` (`CMFormalInert.coeff_expLT_eq_zero`); so the jets of an integral series in its coordinate
    gain over divided powers (`CMFormalInert.norm_coeff_subst_expLT_le`,
    `CMFormalInert.norm_factorial_mul_coeff_subst_expLT_le`, `CMFormalInert.exists_ltCoord`), for the CM curve too
    (`CMFormalInert.cm_inert_jets`, below). The integrality relation `≃` is an equivalence, compatible with sums,
    negation and integral substitution (`CMFormalInert.Simeq.refl`, `CMFormalInert.Simeq.symm`,
    `CMFormalInert.Simeq.trans`, `CMFormalInert.Simeq.add`, `CMFormalInert.Simeq.neg`, `CMFormalInert.Simeq.subst`,
    `CMFormalInert.simeq_iff_sub`, `CMFormalInert.simeq_smul_ell`). Dwork's lemma holds both ways
    (`CMFormalInert.dwork`, `CMFormalInert.simeq_zero_of_dwork`, `CMFormalInert.isDivK_of_isIntK_exp`,
    `CMFormalInert.simeq_zero_iff_dwork`), and Hazewinkel's functional-equation lemma makes the formal group law
    integral (`CMFormalInert.isIntK_expLT_subst`, `CMFormalInert.isIntK_ltAdd`, `CMFormalInert.logLT_subst_ltAdd`);
    roots prime to `ℓ` of integral series are integral (`CMFormalInert.isIntK_of_pow_eq`). The explicit Gaussian
    `serAB` is hermitian, with a product of logarithms as its Frobenius defect (`CMFormalInert.coeff_serAB_herm`,
    `CMFormalInert.expand_serAB_add_smul`), and the formal `σ*`, the exponent `ph` and the pairing `be` are defined
    over any field that holds their coefficients (`CMFormalInert.C_mul_X_mul_exp_neg_ph`, `CMFormalInert.map_be`,
    `CMFormalInert.constantCoeff_be`). With the Weierstrass addition theory, `be` is biadditive and classified (below).
  - Biadditivity and the classification (`CMFormalBiadd`). The `σ` addition law and the Weierstrass differential
    equation become formal identities of `σ*` and `℘`, for every lattice and its image under a ring map
    (`CMFormalBiadd.addLaw_lattice`, `CMFormalBiadd.weierODE_lattice`, `CMFormalBiadd.addLaw_weierODE_map`), and `℘` in
    Lubin–Tate coordinates is integral (`CMFormalBiadd.isInt_rhoLT`). The parallelogram law for `ph`
    (`CMFormalBiadd.parallelogram`) makes `be` symmetric and biadditive up to `≃` (`CMFormalBiadd.be_symm`,
    `CMFormalBiadd.be_biadd`), for the CM curve at an inert prime with the CM inputs (`CMFormalBiadd.be_biadd_cm`,
    below). The translate `U = εT·G_q(z(T))` is an integral unit given the integrality of the coefficients of `G_qᴺ` as
    a polynomial in `℘`, `℘′` (`CMFormalBiadd.isInt_translate`), and `th0 = exp(−ph)·U_t` in Lubin–Tate coordinates
    (`CMFormalBiadd.th0_eq_exp_neg_ph_mul`). For `φ(c) = −c` and `‖c‖ ≤ 1`, `c·serAB` is biadditive and hermitian
    (`CMFormalBiadd.serAB_biadd`, `CMFormalBiadd.isHerm_C_mul_serAB`); and given the uniqueness statement
    `CMFormalBiadd.GaussClass` and the hermitian property of `be`, `be ≃ c·serAB` (`CMFormalBiadd.be_classification`),
    for the CM curve with the CM inputs (`CMFormalBiadd.be_classification_cm`). Both hypotheses are now proved for the
    CM curve: `GaussClass` over every closed field with a Frobenius lift, and the hermitian property from CM
    equivariance (next).
  - The uniqueness statement (`CMFormalGauss`). Dwork's lemma in `T`-form and the coefficients of the group law give the
    structure theorem: over a closed subfield `k` of `ℂ_ℓ` with a Frobenius lift, a symmetric series without constant
    term, biadditive up to `≃`, is `≃ α·L(X)L(Y) + γ·serAB` (`CMFormalGauss.gauss_structure`, with no hermitian
    hypothesis), and the hermitian condition, or bounded coefficients of `X·Y^{ℓ^{2j}}`, gives `α = 0`. So
    `CMFormalBiadd.GaussClass` holds for a closed `k` containing a Teichmüller `ζ` with `‖ζ − ζ^ℓ‖ = 1`
    (`CMFormalGauss.gaussClass_of_isClosed`), in particular for `unramC ℓ`, the closure of the maximal unramified
    extension (`CMFormalGauss.gaussClass_unramC`); it can fail for a field that is not closed. The classification of the
    CM curve then needs only the hermitian property of `be`, or the bound on those coefficients in its place
    (`CMFormalGauss.be_classification_cm'`, `CMFormalGauss.be_classification_cm_bdd`, below).
  - CM equivariance and the hermitian property (`CMEquiv`, `UnramFrobLift`). For `ω = (1 + √−d)/2` and `N = N(ω)`,
    Masser's `σ*` satisfies `σ*(ωz) = ω·σ*(z)^N·∏_q G_q(z)`, the product over representatives of the kernel of `[ω]`
    (`CMEquiv.sgStar_omK0_mul`, by Liouville's theorem). So `ph([ω]T) ≃ N·ph(T)` (`CMEquiv.cm_equiv`), and with a
    Frobenius lift on the maximal unramified extension, `be ≃ c·serAB` with no hermitian hypothesis
    (`CMEquiv.be_simeq_serAB_cm`): `be` is hermitian (`CMEquiv.isHerm_be_cm`) and classified
    (`CMEquiv.be_classification_cm_omega`). Beyond the CM inputs these take a Frobenius lift and the named statement
    `CMEquiv.TorsionTransl`, that the translates by the kernel of `[ω]` are integral units. The lift exists for every
    prime `ℓ` (`UnramFrobLift.unramFrob`), built on the ring generated by the roots of unity of order prime to `ℓ`, with
    no Galois theory of local fields; so the hermitian property and the classification hold without it
    (`UnramFrobLift.isHerm_be_cm'`, `UnramFrobLift.be_classification_cm_omega'`, below).
  - The torsion translates (`EllipticDivPoly`, `TorsionInt`, `GqAdd`, `TorsTransl`, `CMTorsion`). The division values
    `σ(nz)/σ(z)^{n²}` are Mathlib's normalised elliptic divisibility sequence, so the torsion values of `℘` are roots of
    the division polynomials (`EllipticDivPoly.eval_ΨSq_eq_zero`), and with the integrality of their coefficients `℘(q)`
    and `℘′(q)` are integral away from the order of `q` (`TorsionInt.norm_iota_weierstrassP_le_one`). The translates
    multiply by the Frobenius–Stickelberger formula (`GqAdd.Gq_mul_Gq`), and a telescoped product makes every translate
    by torsion of order prime to `ℓ` an integral unit (`TorsTransl.isInt_translate'`), which is `CMEquiv.TorsionTransl`.
    So CM equivariance needs only CM-c (`CMTorsion.cm_equiv'`), and `be ≃ c·serAB`, the hermitian property and the
    classification of the CM curve hold from the classical CM inputs alone (`CMTorsion.be_simeq_serAB_cm'`,
    `CMTorsion.isHerm_be_cm_classical`, `CMTorsion.be_classification_cm_classical`, below).
  - The theta at an inert prime (`MvTay`, `ThetaHeis`, `ThetaCompare`, `HermGS`, `FormalQuad`, `HClass`, `ThetaGauss`;
    D1b). Multivariable Taylor series of analytic functions, as power series: multiplicative and compatible with
    substitutions (`MvTay.mtay_mul`), determined near `0`, with the value at `0` as constant term (`MvTay.mtay_congr`,
    `MvTay.constantCoeff_mtay`), and reduced to one variable on lines (`MvTay.lineR_mtay`, `MvTay.mtay_unit`). On the
    theta spaces, the averaging operator `Iop` maps `Th(Λ₁)` to `Th(Λ₂)` (`ThetaHeis.Iop_mem_Th`), does not depend on
    its representatives (`ThetaHeis.Iop_eq_finsum`) and commutes with `H`-isometries (`ThetaHeis.comp_mem_Th`,
    `ThetaHeis.Iop_comp`); going to `Λ₂` and back is a positive scalar on `Th(Λ₁)` for self-dual `Λ₁`, the injectivity
    identity (`ThetaHeis.Iop_Iop_eq_smul`). So the theta space of the canonical CM lattice is the line `ℂ·F0`
    (`ThetaCompare.eq_smul_F0c`), the moved theta lies in its theta space (`ThetaCompare.thMoved_mem_Th`), and every
    theta of a self-dual theta lattice is a multiple of the adapted model theta (`ThetaCompare.theta_compare`), with no
    input on `dim Th`. Gram–Schmidt over `ℤ_(ℓ)[ω]` gives `ℓ`-adapted orthogonal bases (`HermGS.exists_gsBasis`), and
    four squares an orthonormal basis of `C⁴` (`HermGS.orth4_spec`), a self-dual theta lattice
    (`HermGS.pow4_theta_edual`); the quadratic transfer for integer matrices (`FormalQuad.quad_transfer`) gives `ph ≃
    (γ/2)·serAB` on the diagonal (`FormalQuad.ph_simeq_serAB_diag`). The class `HClass(h)` of the series with
    coefficients `Σ_i ℓ^{−i}[hⁱg_i]`, `g_i` integral, contains the Gaussian `exp(−(ϖ^{ℓ+1}/ℓ)h)`
    (`ThetaHClass.hClass_exp`; small exponentials are integral, `ThetaHClass.isIntK_expMv_of_small`) and is closed under
    integral multiples and changes of variables (`ThetaHClass.HClass.mul`, `ThetaHClass.HClass.change`): the shape of
    the step theta for D1b-8 and D2, which do not use it yet. Together, with the diagonal trick
    (`ThetaGauss.norm_coeff_pow_four_le`), the Taylor series of a theta at an inert `ℓ ≥ 5`, in Lubin–Tate coordinates
    along an adapted basis, is `c₀·exp(−Ψ)·U` with `U` integral and `Ψ = Σ_i u_i(γ/2)·serAB(X_i, X_i)`
    (`ThetaGauss.theta_gauss`, for any Frobenius lift, and `ThetaGauss.theta_gauss'`, for that of `UnramFrobLift`), from
    the classical CM inputs alone (below).
  - D2, the served valuation of the theta chain: first modules (`JetMinor`, `KernelCount`, `HeckeTheta`,
    `LocalKernels`). Series (D2-1): the jet pairing `Σ_κ Q_κ·κ!·F_κ` of a polynomial with a power series pairs the
    chain's series with products of minors of frame blocks. A rank-one update is affine in its coefficient, `det(B +
    w·uᵀ) = det B + Σ_c u_c·det(B with column c replaced by w)` (`JetMinor.det_add_rankOne`), so along directions at one
    position with one vector a product of minors has degree at most the number of its minors there, and its Hasse
    derivatives beyond that vanish (`JetMinor.hasseDir_minorProd_eq_zero`); with a vector per direction but only the
    Z-columns in `J`, a minor with Z-columns `I` has degree at most `#(I ∩ J)`
    (`JetMinor.hasseDir_minorProd_eq_zero_cols`). The frame jet of one orbit (`JetMinor.frameJet`) and of all orbits,
    the degree of the column product, `ρ_p = 1/(p² − 1)` and the column weights of a Hecke edge are defined, for the
    frame-jet bounds and the bridge below. Lattices (D2-4, D2-5): Gaussian binomials satisfy q-Vandermonde, `[m + n, k]
    = Σ_j q^{(m−j)(k−j)}·[m, j]·[n, k − j]` (`KernelCount.qBinom_add`), and count the subspaces of a space over a field
    with `q` elements (`KernelCount.card_subspace_eq_qBinom`); so for `x·L ⊆ L′`, with `φ̄ : p⁻¹L/L → L′/pL′` of rank
    `ρ`, the type-`i` edges `L₁ ⊂ L′` with `x·L ⊆ L₁` number `[N′ − ρ, i]_q` and the type-`r` edges `A ⊃ L` with `x·A ⊆
    L′` number `[N − ρ, r]_q` (`KernelCount.edge_count`). Over class representatives of the lattice tuples under a
    level, the sums over the edges up and down, weighted by the inverse orders of the stabilisers, agree for an
    invariant function (`KernelCount.hecke_adjoint`, Hecke adjointness). Normalised Hecke operators with a one-step
    relation `H_{j+1}(i)∘K_j = Σ_{l ≤ i} ε_{j,l}·K_j∘H_j(i − l)` along the steps `K_j` satisfy `H_j(i)∘chain_j = Σ_{l ≤
    i} c_{j,l}·chain_j∘H_0(i − l)`, `c_j` the coefficients of `∏_{j′<j} Σ_l ε_{j′,l}X^l` (`HeckeTheta.hecke_chain`, by
    convolution, `HeckeTheta.sum_conv`), so the combination of the `H_j(r − l)` by the coefficients of the inverse of
    that product modulo `X^{r+1}` turns `chain_j` into `chain_j∘H_0(r)` (`HeckeTheta.iterate_hecke`, the iteration
    lemma). The contract from D1 to D2 (D2-0, definitions only, which no theorem uses yet): the local chain at a served
    prime (`LocalContract.LocalChain`: levels with ranks, class representatives, coefficient lattices and steps on the
    local functions), its composite (`LocalContract.LocalChain.chain`), the valuation predicate `F ∈ ϖ^{⌈2g⌉}·Int j`
    (`LocalContract.LocalChain.vGe`) and the served Hecke-product lattice (`LocalContract.LocalChain.Iprod`); the kernel
    data D1 is to deliver (`LocalContract.LocalKernels`: the expansion of a step over the class representatives, K1; the
    Gaussian frame form `ser = posGauss(γ)·R`, `R` integral and mixed-integral, K2; level equivariance, K5; and the
    stabiliser losses); and two clauses stated on top, the bridge from frame jets to lattice valuations
    (`LocalContract.Bridge`, K3) and the normalisation law (`LocalContract.NormLaw`, K4).

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
| The piece `frameLoss` of `ZetaBalance.SharpPieces` for the construction `ZetaBalance.sharpCons`: at every admissible design with `ε` small and `x` large, in every frame realising a translate's object, the words have positive total rank and the mean slope exceeds the target's by at most the frame loss `x^{4ε}Σ_t a_t/4` | `ZetaBalance.SharpNI`, (NI), the near-injectivity of the period map of the construction's one word (`0 < rk P`, `dim V_ω ≤ 2 rk P`), not yet proved, with the whole-word second moment its planned route; and `ZetaBalance.SharpCertSmall`, a gain certificate (`ZetaBalance.SharpObj.GainCert`) at every word with `2·log[M_ω : L]/rk ≤ x^{4ε}Σ_t a_t/8`, not yet proved. The range (R′) follows from the second, as `ZetaBalance.SharpMuMax` is proved (`ZetaBalance.sharpMuMax`) | `ZetaBalance.frameLoss_of_sharpNI_cert` |
| The piece `frame` of `ZetaBalance.SharpPieces` for the construction `ZetaBalance.sharpCons`: at every admissible design with `ε` small and `x` large, at every translate `u ∈ A₀`, some frame realises the translate's object, with the quotient target metric and heights `0` | `ZetaBalance.SharpNI`, (NI), the near-injectivity of the period map of the construction's one word (`0 < rk P`, `dim V_ω ≤ 2 rk P`), of which the proof uses only `0 < rk P` | `ZetaBalance.frame_of_sharpNI` |
| The range (R′) of the frame loss, `ZetaBalance.SharpRange`: at every admissible design with `ε` small and `x` large, in every frame realising a translate's object, `μ_max(N_ω) ≤ μ(N_ω) + U` with `0 ≤ U ≤ x^{4ε}Σ_t a_t/4` | `ZetaBalance.SharpCertSmall`, a gain certificate (`ZetaBalance.SharpObj.GainCert`) at every word with `2·log[M_ω : L]/rk ≤ x^{4ε}Σ_t a_t/8`, not yet proved | `ZetaBalance.sharpRange_of_certSmall` |
| The bound `ZetaBalance.SharpMuMax` on the maximal slope of the construction's lattice of integral forms `M_ω`, a route that `ZetaBalance.sharpMuMax` makes unnecessary by proving the bound | `ZetaBalance.SharpCoordCert`: at every admissible design with `ε` small and `x` large, at every translate, integral coordinates (`ZetaBalance.SharpObj.CoordCert`) of some weight `w > 0` with `−log w + c_F ≤ x^{4ε}Σ_t a_t/8` on the source of every word: injective, integral on the integral forms, and with `w·\|σ_v ∘ T\|²` below the Petersson form at every complex place | `ZetaBalance.sharpMuMax_of_coordCert` |
| The piece (T) of `ZetaBalance.SharpPieces` for the construction `ZetaBalance.sharpCons`: at every admissible design with `x` large, every translate's auxiliary prime is a prime `T = ππ̄`, `π ≡ 1 (mod M)`, with `log T > Λ_u − x^{2ε}` and slack `c_T = x^{2ε}` within its quarter of the budget | `ZetaBalance.ShortNorm` | `ZetaBalance.sharpPrimes` |
| Admissible designs exist (the piece `params` of `ZetaBalance.SharpPieces`): for every primitive `χ`, small `ε` and large `Y`, every pair of `ZetaTwist.WinPair` has, at every `x` of its window, a setting with a character lifting `χ` and an admissible design (`ZetaBalance.SharpDesign.Adm`) | `ZetaBalance.ShortNorm`, which gives the design's split primes `g₀ ≠ g₁` | `ZetaBalance.sharpParams` |
| The core of the auxiliary primes (T): primes `T = ππ̄`, `π = (a + b√−d)/2 ≡ 1 (mod M)`, in every dyadic window `(e^Λ, 2e^Λ]` once `log(4dM²) ≤ c√Λ`, so meeting `ArithT` with `log T` within `log 2` of any large target; a step of the piece `primes` of `ZetaBalance.SharpPieces` | `ZetaBalance.ShortNorm`: Chebotarev in short intervals for `ℚ(√−d)`, an input of `ZetaBalance.SharpInputs` | `ZetaBalance.exists_prime_norm_window`, `ZetaBalance.SharpDesign.exists_prime_arithT` |
| The jets of `th0` at the construction's lattice `Lc = δ(ℤ + ℤω)`, of discriminant `1`, and point `t = δ/2` are algebraic, and integral at every prime `ℓ ≥ 5` with `ℓ ∤ d` | The CM inputs `CMThetaOne.CMjIntegral` (CM-c, Weber and Deuring: `j` is an algebraic integer) and `CMThetaOne.CMs2` (CM-d, Masser and Katz: `s₂` of the CM lattice of discriminant `1` is algebraic and integral at every `ℓ ≥ 5` with `ℓ ∤ d`) | `CMThetaOne.canon_jets_isAlgebraic'`, `CMThetaOne.canon_jets_int'` |
| The jets of the CM curve at an inert prime `ℓ ≥ 5` (`CMFormalInert`): for the model of discriminant `1` of a CM lattice, every series integral in the formal parameter has `z`-expansion with `v([z^N]) ≥ −(N − 1)/(ℓ² − 1)` and `v(N!·[z^N]) ≥ Nℓ/(ℓ² − 1) − s_ℓ(N)/(ℓ − 1) + 1/(ℓ² − 1)` | `CMFormalInert.CMInertLubinTate` (CM-b, Deuring, Lubin–Tate and Honda): at an inert `ℓ ≥ 5` a unit `ε` of the maximal unramified extension makes `t(ε·log_LT(T))` integral | `CMFormalInert.cm_inert_jets` |
| Biadditivity of the formal Gaussian pairing for the CM curve at an inert prime (`CMFormalBiadd`): for the model of discriminant `1` of a CM lattice and an inert `ℓ ≥ 5`, `ℓ ∤ d`, a unit `ε` of the maximal unramified extension makes `be = ph(X ⊕ Y) − ph(X) − ph(Y)` biadditive up to `≃` | The CM inputs `CMFormalInert.CMInertLubinTate` (CM-b, Deuring, Lubin–Tate and Honda: at an inert `ℓ ≥ 5` a unit `ε` of the maximal unramified extension makes `t(ε·log_LT(T))` integral) and `CMThetaOne.CMjIntegral` (CM-c, Weber and Deuring: `j` is an algebraic integer) | `CMFormalBiadd.be_biadd_cm` |
| CM equivariance of the formal Gaussian exponent (`CMEquiv`): for the model of discriminant `1` of the CM lattice, an inert `ℓ ≥ 5` with `ℓ ∤ d`, a Frobenius lift `φ` on the maximal unramified extension and `ω = (1 + √−d)/2`, `ph([ω]T) ≃ N(ω)·ph(T)` | The CM input `CMThetaOne.CMjIntegral` (CM-c, Weber and Deuring: `j` is an algebraic integer) and `CMEquiv.TorsionTransl`, that the translates by the kernel of `[ω]` are integral units, which `TorsTransl.isInt_translate'` proves | `CMEquiv.cm_equiv` |
| CM equivariance from CM-c alone (`CMTorsion`): `ph([ω]T) ≃ N(ω)·ph(T)` for the model of discriminant `1` of the CM lattice, an inert `ℓ ≥ 5` with `ℓ ∤ d` and a Frobenius lift `φ` on the maximal unramified extension | The CM input `CMThetaOne.CMjIntegral` (CM-c, Weber and Deuring: `j` is an algebraic integer) | `CMTorsion.cm_equiv'` |
| The formal Gaussian pairing of the CM curve at an inert `ℓ ≥ 5`, `ℓ ∤ d`, with no hermitian input (`CMEquiv`, `UnramFrobLift`): for a Frobenius lift `φ` on the maximal unramified extension and every unit `ε` of it making `t(ε·log_LT(T))` integral, `be ≃ c·serAB` with `φ(c) = −c` and `‖c‖ ≤ 1`; and `be` is hermitian, given that some Frobenius lift exists (`CMEquiv.UnramFrob ℓ`, an argument of `CMEquiv.isHerm_be_cm`, which `UnramFrobLift.unramFrob` proves) or with none asked (`UnramFrobLift.isHerm_be_cm'`) | The CM inputs `CMThetaOne.CMjIntegral` (CM-c), `CMFormalBiadd.CMUnramified` (CM-a′, Weber and Shimura reciprocity: the invariants of the model lie in the maximal unramified extension at `ℓ ≥ 5`, `ℓ ∤ d`) and `CMFormalBiadd.CMs2Unram` (CM-d strengthened, Masser and Katz: `s₂` of that lattice lies there and is integral); and `CMEquiv.TorsionTransl`, the integrality of the translates by the kernel of `[ω]`, which `TorsTransl.isInt_translate'` proves | `CMEquiv.be_simeq_serAB_cm`, `CMEquiv.isHerm_be_cm`, `UnramFrobLift.isHerm_be_cm'` |
| The classification of the formal Gaussian pairing of the CM curve at an inert `ℓ ≥ 5`, `ℓ ∤ d` (`CMEquiv`, `UnramFrobLift`): some unit `ε` of the maximal unramified extension has `be ≃ c·serAB` with `φ(c) = −c` and `‖c‖ ≤ 1`, for a given Frobenius lift `φ` (`CMEquiv.be_classification_cm_omega`) or for the lift of `UnramFrobLift` (`UnramFrobLift.be_classification_cm_omega'`) | The CM inputs `CMFormalInert.CMInertLubinTate` (CM-b, Deuring, Lubin–Tate and Honda: at an inert `ℓ ≥ 5` a unit `ε` of the maximal unramified extension makes `t(ε·log_LT(T))` integral), `CMThetaOne.CMjIntegral` (CM-c), `CMFormalBiadd.CMUnramified` (CM-a′) and `CMFormalBiadd.CMs2Unram` (CM-d strengthened); and `CMEquiv.TorsionTransl`, which `TorsTransl.isInt_translate'` proves | `CMEquiv.be_classification_cm_omega`, `UnramFrobLift.be_classification_cm_omega'` |
| The formal Gaussian pairing of the CM curve at an inert `ℓ ≥ 5`, `ℓ ∤ d`, from the classical CM inputs (`CMTorsion`): for a Frobenius lift `φ` on the maximal unramified extension and every unit `ε` of it making `t(ε·log_LT(T))` integral, `be ≃ c·serAB` with `φ(c) = −c` and `‖c‖ ≤ 1`; and `be` is hermitian | The CM inputs `CMThetaOne.CMjIntegral` (CM-c), `CMFormalBiadd.CMUnramified` (CM-a′) and `CMFormalBiadd.CMs2Unram` (CM-d strengthened) | `CMTorsion.be_simeq_serAB_cm'`, `CMTorsion.isHerm_be_cm_classical` |
| The classification of the formal Gaussian pairing of the CM curve at an inert `ℓ ≥ 5`, `ℓ ∤ d`, from the classical CM inputs alone (`CMTorsion`): some unit `ε` of the maximal unramified extension has `be ≃ c·serAB` with `φ(c) = −c` and `‖c‖ ≤ 1`, for the Frobenius lift `φ` of `UnramFrobLift` | The CM inputs `CMFormalInert.CMInertLubinTate` (CM-b), `CMThetaOne.CMjIntegral` (CM-c), `CMFormalBiadd.CMUnramified` (CM-a′) and `CMFormalBiadd.CMs2Unram` (CM-d strengthened) | `CMTorsion.be_classification_cm_classical` |
| The classification of the formal Gaussian pairing of the CM curve with the uniqueness statement proved (`CMFormalGauss`): at an inert `ℓ ≥ 5`, `ℓ ∤ d`, for a Frobenius lift `φ` on the maximal unramified extension, some unit `ε` of it has `be ≃ c·serAB` with `φ(c) = −c` and `‖c‖ ≤ 1`, given, as an argument, the hermitian property of `be` or, in its place, bounded coefficients of `X·Y^{ℓ^{2j}}` in `be` | The CM inputs `CMFormalInert.CMInertLubinTate` (CM-b), `CMThetaOne.CMjIntegral` (CM-c), `CMFormalBiadd.CMUnramified` (CM-a′) and `CMFormalBiadd.CMs2Unram` (CM-d strengthened) | `CMFormalGauss.be_classification_cm'`, `CMFormalGauss.be_classification_cm_bdd` |
| The Gaussian factorisation of the theta at an inert prime (`ThetaGauss`): for `θ` in the theta space of an `ω`-stable self-dual theta lattice `C` (`d ≡ 7 (mod 8)`), an inert `ℓ ≥ 5` with `ℓ ∤ d` and an `ℓ`-adapted orthogonal basis of `C`, some unit `ε` of the maximal unramified extension makes the Taylor series of `θ` in the Lubin–Tate coordinates of `ε` along the basis `c₀·exp(−Ψ)·U`, with `U` integral and `Ψ = Σ_i u_i(γ/2)·serAB(X_i, X_i)`, `φ(γ) = −γ`; for a given Frobenius lift `φ` (`ThetaGauss.theta_gauss`) or that of `UnramFrobLift` (`ThetaGauss.theta_gauss'`) | The CM inputs `CMFormalInert.CMInertLubinTate` (CM-b), `CMThetaOne.CMjIntegral` (CM-c), `CMFormalBiadd.CMUnramified` (CM-a′) and `CMFormalBiadd.CMs2Unram` (CM-d strengthened) | `ThetaGauss.theta_gauss`, `ThetaGauss.theta_gauss'` |
| The first local theorem (L5): at one orbit of an inert `p ≥ 5` in the setting `Unram`, a per-orbit fraction `κ` with box mean at most `C·N·N₁/Y` and the local lattice property at every lattice, for the weights of the shape | Named statements, arguments of the theorems (each mentions their variables, so none is a closed hypothesis): `FirstAssembly.InputRank` (I1, the rank theorem of layer 2), `FirstMeans.SegMean` (I2, the segment mean of layer 3), the bound `κ_P ≤ C_P·N·N₁/Y` (I3), `FirstAssembly.HarmSplit` (the harmonic splitting, which `HarmSplitPf.harmSplit` proves for `k ≥ 3`), `FirstAssembly.FlatDim` (the dimensions of the flat pieces, which `FlatDimPf.flatDim` proves), `FirstAssembly.CloudStep` (the cloud step, which `FirstCloud.cloudStep` proves from three classical inputs) and, for `FirstAssembly.first_local` only, `FirstAssembly.OffTop` (the off-top step, which `OffTop.offTop` proves) | `OffTop.first_local'`, `FirstAssembly.first_local` |
| The first local theorem (L5) with one input discharged: without `FirstAssembly.FlatDim` (`FlatDimPf.first_local_flat`), without `FirstAssembly.HarmSplit` (`HarmSplitPf.first_local''`), or with `FirstAssembly.CloudStep` replaced by the cloud step's three classical inputs (`FirstCloud.first_local''`) | Named statements, arguments of the theorems (each mentions their variables, so none is a closed hypothesis): `FirstAssembly.InputRank` (I1), `FirstMeans.SegMean` (I2), the bound `κ_P ≤ C_P·N·N₁/Y` (I3), and the two of `FirstAssembly.FlatDim`, `FirstAssembly.HarmSplit` and `FirstAssembly.CloudStep` not discharged; for `FirstCloud.first_local''`, in place of the last, `FirstCloud.WeylDim` (I8), `FirstCloud.CloudPair` (I5 with the contraction of N16) and `FirstCloud.HwSat` (the domain half of I6) | `FlatDimPf.first_local_flat`, `HarmSplitPf.first_local''`, `FirstCloud.first_local''` |
| The cloud step of L5 (A-N15 to N17): at one orbit of an inert `p` in the setting `Unram`, for `b′ > 0` and `k ≥ 2`, `FirstAssembly.CloudStep` with the cloud exponent `D_c` | Classical inputs, named statements, arguments of the theorems (each mentions their variables, so none is a closed hypothesis): `FirstCloud.WeylDim` (I8, the Weyl dimension formula for `∇`, which `WeylDimPf.weylDim` proves), `FirstCloud.CloudPair` (I5 with the contraction of N16: an equivariant contraction `V(λ) × V(μ*) → V(H⁺)`, integral on `∇_O × ∇_O`, with top cloud vectors pairing to `δ_{ab}p^{κ_a}·hw(fl₂)`, `κ_a ≤ D_c`, not yet proved) and `FirstCloud.HwSat` (the domain half of I6: `F·hw(ν₂) ∈ ∇_O(ν + ν₂)` implies `F ∈ ∇_O(ν)`, which `HwSatPf.hwSat` proves over a discrete valuation ring) | `FirstCloud.cloudStep` |
| The first local theorem (L5) with `FirstAssembly.FlatDim`, `FirstCloud.WeylDim` and `FirstCloud.HwSat` discharged: at one orbit of an inert `p ≥ 5` in the setting `Unram`, a per-orbit fraction `κ` with box mean at most `C·N·N₁/Y` and the local lattice property at every lattice | `FirstCloud.CloudPair` (I5 with the contraction of N16, the cloud pairing, with exponents at most `D_c`, not yet proved) and the named statements `FirstAssembly.HarmSplit` (which `HarmSplitPf.harmSplit` proves), `FirstAssembly.InputRank` (I1), `FirstMeans.SegMean` (I2) and the bound `κ_P ≤ C_P·N·N₁/Y` (I3), arguments of the theorems (each mentions their variables, so none is a closed hypothesis) | `HwSatPf.first_local_cloud` |
| The Riemann hypothesis for `ζ` and for every Dirichlet `L`-function | `WindowGRH.WindowBound`: for every primitive `χ` and `θ > 1/2`, the weighted error of the ramp sums of the cyclic family of `χ` is at most `C x^θ` on windows `[Y, Y^λ]` with `Y` arbitrarily large | `WindowGRH.rhAndGRH_of_windowBound` |
| The Riemann hypothesis for `ζ` and for every Dirichlet `L`-function, also resting on the half-plane `Re s > 11/12` for `ζ` and every Dirichlet `L`-function, a result formalised in the library that no referee has read ([openai-half-plane.md](openai-half-plane.md)) | `ZetaBalance.PairBound`, the construction alone: for every primitive `χ` and every `ε₀ > 0` there are `ε ∈ (0, ε₀)` and `A ≥ 1` such that, for every large `Y`, every pair of primes `(q, d)` meeting `ZetaTwist.WinPair ε Y` has a sub-window `[Y′, Y′²]`, with `Y ≤ Y′ ≤ Y^{A/2}`, at every `x` of which a setting `S` with `S.q = q` and `S.d = d` and a character `κ` of `A` lifting `χ` (`ZetaBalance.Setting.Lifts`) has lattice data (`ZetaBalance.LatticeData S κ x ε X`) whose thin classes lie beyond `X = (Nx)^{log x}` | `ZetaBalance.rhAndGRH_of_pairBound` |
| The Riemann hypothesis for `ζ` and for every Dirichlet `L`-function, also resting on the half-plane `Re s > 11/12` for `ζ` and every Dirichlet `L`-function, a result formalised in the library that no referee has read ([openai-half-plane.md](openai-half-plane.md)) | `ZetaBalance.SixTermBound`: `ZetaBalance.PairBound` with six-term data (`ZetaBalance.SixTermData S κ x ε X`) in place of lattice data: weights and, at each translate of the kernel `A₀` of `κ`, a frame meeting the hypotheses of the frame inequality at its rank-weighted mean slope (`SlopeFrame.Frame.mean`), with numbers of its words (the slope of the forms, the split primes, the auxiliary prime) and of the translate (the vanishing gain, the forced vanishing, a scale `v > 0`, `log(g₀g₁)`, six slacks) that meet the archive's six inequalities G1–G6, and one budget for the slacks and the losses of the frame inequality | `ZetaBalance.rhAndGRH_of_sixTermBound` |
| The Riemann hypothesis for `ζ` and for every Dirichlet `L`-function, also resting on the half-plane `Re s > 11/12` for `ζ` and every Dirichlet `L`-function, a result formalised in the library that no referee has read ([openai-half-plane.md](openai-half-plane.md)) | `ZetaBalance.SharpBoundPinned`, the sharp frontier: `ZetaBalance.SixTermBound`'s shape with the frames realised by the construction's defined objects (sources from the forms with the Petersson metric, the target from the integral rows, the periods through the theta chain), each pinned to the archive's construction, with the forced orders fixed and nonnegative slacks; `ZetaBalance.SharpBoundTheta` is the same with fewer pins | `ZetaBalance.rhAndGRH_of_sharpBoundPinned`, `ZetaBalance.sharpBoundTheta_of_pinned` |
| The Riemann hypothesis for `ζ` and for every Dirichlet `L`-function, also resting on the half-plane `Re s > 11/12` for `ζ` and every Dirichlet `L`-function, a result formalised in the library that no referee has read ([openai-half-plane.md](openai-half-plane.md)) | `ZetaBalance.SharpInputs`, the deep classical inputs stated as hypotheses (Siegel–Weil, good twists, the unitary mass formula, Lerch's formula, primes of norm in short intervals), and `ZetaBalance.SharpPieces`, the statements still to prove in the library (the construction's choices, finite classes, the forms a lattice, the parameters, the frame, the auxiliary primes, the slope bound and index, the gain, (G↑), (S) and (R)); their conjunction gives `ZetaBalance.SixTermBound` | `ZetaBalance.rhAndGRH_of_inputs`, `ZetaBalance.sixTermBound_of_inputs` |
| The Riemann hypothesis for `ζ` and for every Dirichlet `L`-function | `ZetaBalance.LatticeBound`: for every primitive `χ` and `ε > 0`, on windows `[Y, Y^λ]` with `Y` arbitrarily large, every `x` has a setting `S` with a character `κ` of `A` lifting `χ` (`ZetaBalance.Setting.Lifts`), thin at some `X`, with small twists (`ZetaBalance.Setting.Twists S κ`), and lattice data (`ZetaBalance.LatticeData S κ x ε X`): weights and, at each translate of the kernel `A₀` of `κ`, a frame meeting the hypotheses of the frame inequality, whose gain covers the inert-prime gap (G) with small losses (Z) | `ZetaBalance.rhAndGRH_of_latticeBound` |
| The Riemann hypothesis for `ζ` and for every Dirichlet `L`-function | `ZetaBalance.BalanceBound`: for every primitive `χ` of order `o` and `ε > 0`, on windows `[Y, Y^λ]` with `Y` arbitrarily large, every `x` has a setting `S` with a character `κ` of `A` lifting `χ` (`ZetaBalance.Setting.Lifts`), thin at some `X`, with the `3o` twists `g_{(α,β,κ^k)}`, `(α, β) ≠ (0, 0)` and `k < o`, at most `x^{1/2+ε}` at `x`, and balance data (`ZetaBalance.BalanceData S κ x ε X`): weights with thick classes in the kernel `A₀` of `κ`, of density at least `x^{−ε}` there, translates whose shares `Σ_t a_t κ(t)^k` lie within `x^{ε−1} Σ_t a_t` of `Σ_t a_t/(3o + 1)` for `0 < k < o`, and an inert-prime gap, averaged over `A₀`, at most `x^{4ε} Σ_t a_t` | `ZetaBalance.rhAndGRH_of_balanceBound` |
| The Riemann hypothesis | `WindowGRH.ZetaWindowBound`: for every `θ > 1/2`, `Σ_{n≤x} Λ(n)(x/n − 1) − x log x + (1 + γ)x ≤ C x^θ` on windows `[Y, Y^λ]` with `Y` arbitrarily large | `WindowGRH.riemannHypothesis_of_zetaWindowBound` |
| The Riemann hypothesis, also resting on the half-plane `Re s > 11/12` for `ζ` and every Dirichlet `L`-function, a result formalised in the library that no referee has read ([openai-half-plane.md](openai-half-plane.md)) | `ZetaBalance.ZetaPairBound`, the construction alone: for every `ε₀ > 0` there are `ε ∈ (0, ε₀)` and `A ≥ 1` such that, for every large `Y`, every pair of primes `(q, d)` meeting `ZetaTwist.WinPair ε Y` has a sub-window `[Y′, Y′²]`, with `Y ≤ Y′ ≤ Y^{A/2}`, at every `x` of which a setting `S` with `S.q = q` and `S.d = d` has lattice data (`ZetaBalance.LatticeData S 1 x ε X`) whose thin classes lie beyond `X = (Nx)^{log x}` | `ZetaBalance.riemannHypothesis_of_zetaPairBound` |
| The Riemann hypothesis, also resting on the half-plane `Re s > 11/12` for `ζ` and every Dirichlet `L`-function, a result formalised in the library that no referee has read ([openai-half-plane.md](openai-half-plane.md)) | `ZetaBalance.ZetaTwistBound`: for every `ε > 0`, on windows `[Y, Y^λ]` with `Y` arbitrarily large, every `x` has a setting `S` with small twists (`ZetaBalance.Setting.Twists S 1`) and lattice data (`ZetaBalance.LatticeData S 1 x ε X`) whose thin classes lie beyond `X = (Nx)^{log x}` | `ZetaBalance.riemannHypothesis_of_zetaTwistBound` |
| The Riemann hypothesis | `ZetaBalance.ZetaLatticeBound`: for every `ε > 0`, on windows `[Y, Y^λ]` with `Y` arbitrarily large, every `x` has a setting `S` thin at some `X` (`ZetaBalance.Setting.Thin`), with small twists (`ZetaBalance.Setting.Twists S 1`), and lattice data (`ZetaBalance.LatticeData S 1 x ε X`): weights and, at each translate, a frame meeting the hypotheses of the frame inequality, whose gain covers the inert-prime gap (G) with small losses (Z) | `ZetaBalance.riemannHypothesis_of_zetaLatticeBound` |
| The Riemann hypothesis | `ZetaBalance.ZetaBalanceBound`: for every `ε > 0`, on windows `[Y, Y^λ]` with `Y` arbitrarily large, every `x` has a setting `S` thin at some `X`, with small twists, and balance data (`ZetaBalance.BalanceData S 1 x ε X`). The setting is thin when the errors are at most `θy` for `y ≥ X`, with `8\|A\|x²θ ≤ 1`, and its twists are small when the three quadratic twists are at most `x^{1/2+ε}` at `x`. The balance data are weights (`ZetaBalance.Weights`) whose inert-prime gap, averaged over translates, is at most `x^{4ε} Σ_t a_t`, with `m ≥ x^{1/2−ε}` words, thick classes of density at least `x^{−ε}`, and `a_t/w ≥ X` on the thin classes | `ZetaBalance.riemannHypothesis_of_zetaBalanceBound` |
| GRH in the words of L. Alpöge's Lean archive (`LinnikGRH.DirichletRH`), the hypothesis of the library's results under GRH (`LinnikGRH.linnik_two`, `LinnikAlmostAll.almostAll_one`) | `HalfPlaneGRH.RHandGRH`, the Riemann hypothesis for `ζ` and for the `L`-function of every Dirichlet character, which `ZetaBalance.PairBound` gives, conditionally on the half-plane | `LinnikGRH.dirichletRH_of_rhAndGRH` |
