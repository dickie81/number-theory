# Rebuilding the proof of the Riemann hypothesis

On 20 November 2026 Levent Alpöge posted a statement (<https://alpo.ge/remark.pdf>) and a Lean archive claiming,
with Claude, a proof of the Riemann hypothesis for `ζ` and for every Dirichlet `L`-function. On its own pins, Lean's
kernel accepts the archive, and its two main theorems use only the three standard axioms (`tools/rh/README.md`). The
proof is enormous: 10.7 million lines in the dependency cone of `riemannHypothesis`.

The archive carries no licence, so none of it is in this repository. This file plans a proof in the library itself,
written fresh from the mathematics, in the library's style, on its own Lean and Mathlib, and published under the
library's licence.

## Rules

- **Fresh.** No archive text is committed, and none is translated mechanically. The archive is read to learn what
  is true and how the argument goes; the Lean here is written anew. Helpers who write parts are given statements and
  Mathlib, not the archive.
- **Top down, always checked.** At every stage the library holds a theorem "frontier ⇒ RH for `ζ` and every
  Dirichlet `L`-function", with the frontier a named proposition. The build has no `sorry` and only the three
  standard axioms. Each stage makes the frontier smaller or more classical.
- **Simplify aggressively.** Before formalising a step as the archive does, look for a shorter route: a Mathlib or
  library lemma, a weaker frontier the next step still delivers, a different classical argument, or a published
  simplification. Record the archive's size for each step against ours.

## The shape of the argument

1. **The top**: RH for `ζ` and every Dirichlet `L`-function follows from a zero-free half-plane `Re s > 1/2` for
   the primitive characters.
2. **Landau on windows**: the half-plane follows from a one-sided bound on smoothed prime sums. For the cyclic family
   of a primitive `χ`, the weighted error `G(x)` of the ramp sums `Σ_{n ≤ x} Λ(n)χ(n)(x/n − 1)` must satisfy
   `G(x) ≤ C x^θ` on windows `[Y, Y^λ]` with `Y` arbitrarily large, for every `θ > 1/2`. The weights are `1` for `ζ`
   and `1/(3o + 1)` for the others, `o` the order of `χ`.
3. **Balance**: that bound follows from an upper bound on sums over inert primes, weighted by `log p·(a/pⁱ − w)⁺`,
   less their main terms, in every coset of a subgroup. The archive's `ch_balance` is an exact identity between the
   inert-prime sum and the character errors; its `ch_core` takes the bound from the cosets to the family.
4. **Lattices**: the inert-prime bound is read off the data of Euclidean lattices (ranks, slopes, sizes), with Bost's
   slope inequality.
5. **Theta lifts**: the lattices come from chains of theta lifts between definite unitary groups, about `√X` of them
   for a sum of length `X`, each lift standing in for a multiplicity in Stepanov's method.
6. **The inputs**: the core theorem takes seven inputs: two bundles of published results (162 named theorems, among
   them Deligne–Ribet, Artin reciprocity, Casselman–Wallach, Clozel purity, Bhatt–Scholze, Siegel–Weil, Howe
   duality, toroidal compactifications, Hironaka's resolution), an agreement of two theta integrals, a local
   matching, a covolume bound, local Langlands for `GL_n`, and a Vandiver-type bound (`VWin`).

## Status

| Step | Library | Lines | Archive | State |
|---|---|---|---|---|
| 1. The top | `HalfPlaneGRH` | 183 | about 130 | Done: `HalfPlaneGRH.rhAndGRH_of_zeroFreeRightOf`, with its converse `zeroFreeRightOf_half_iff` |
| 2. Landau on windows | `WindowKernel`, `WindowPole`, `WindowNearest`, `LandauWindow`, `RampLaplace`, `WindowGRH` | about 1,600 | about 2,100 (the declarations `lemmaL` and `formB` name) | Done: `WindowGRH.rhAndGRH_of_windowBound` |
| 3. Balance | `ZetaBalance`, `ZetaGap` | about 1,520 | about 4,000 (`ChBalance`, `ChCore`, `core_gm`) | Done for `ζ` and every primitive `χ`: `ZetaBalance.riemannHypothesis_of_zetaBalanceBound`, `ZetaBalance.rhAndGRH_of_balanceBound` |
| 4. Lattices | `SlopeFrame`, `GramVolume`, `EuclidLattice`, `PlaceLattice`, `HermitianLattice`, `ZetaFrame` | about 1,750 | about 6,600 (hermitian lattices, Bost, polygons, `TheoremF`), and `ch_top`, about 3,000 | Done for `ζ` and every primitive `χ`: `ZetaBalance.riemannHypothesis_of_zetaLatticeBound`, `ZetaBalance.rhAndGRH_of_latticeBound`. The frames may be Euclidean (`EuclidLattice.frame`) or, as the archive's are, hermitian over a totally complex `K` with heights averaged over the places (`HermitianLattice.frame`) |
| The analytic inputs | `PsiExplicit`, `ZetaThin`, `PrimeCharSums`, `MeanSquareSup`, `TwistFamily`, `ZetaTwist`, `ZetaPair` | about 2,410 | about 28,000 for the twists, mostly a prime number theorem in progressions | Done for `ζ` and every primitive `χ`, conditionally on the half-plane `Re s > 11/12`: `ZetaBalance.riemannHypothesis_of_zetaPairBound`, `ZetaBalance.rhAndGRH_of_pairBound` |
| The six-term interface | `SixTerm` | 265 | the rest of `ch_top` (counted in step 4) | Done for `ζ` and every primitive `χ`, conditionally on the half-plane: `ZetaBalance.rhAndGRH_of_sixTermBound` |
| 5–6. | | | almost all of 10.7 million lines | Later |

Library line counts include the documentation; the archive has none.

**The frontier now** is `WindowGRH.WindowBound`: for every primitive `χ` and every `θ > 1/2`, the weighted error
`(WindowGRH.cyclic χ).G` is at most `C x^θ` on windows `[Y, Y^λ]` with `Y` arbitrarily large, for some `λ > 1` and
`C`. The archive's core theorem proves this in the form `HasWindows {x | Gm x ≤ x^θ} (3/2)`, which is stronger.

**For RH alone**, step 2 leaves a statement about `Λ` only. `WindowGRH.ZetaWindowBound` asks, for every
`θ > 1/2`, that `Σ_{n≤x} Λ(n)(x/n − 1) − x log x + (1 + γ)x ≤ C x^θ` on windows `[Y, Y^λ]` with `Y` arbitrarily large.
`WindowGRH.riemannHypothesis_of_zetaWindowBound` gives Mathlib's `RiemannHypothesis` from it.

**After step 3**, the frontier for RH is `ZetaBalance.ZetaBalanceBound`: for every `ε > 0`, balance data
(`ZetaBalance.BalanceData S 1 x ε X`) at every `x` of windows with `Y` arbitrarily large. It is the inert-prime gap
averaged over translates, with the analytic inputs as separate hypotheses: the setting is thin at `X`
(`ZetaBalance.Setting.Thin`, errors at most `θy` for `y ≥ X`), and its twists are small (`ZetaBalance.Setting.Twists`,
the three quadratic twists at most `x^{1/2+ε}` at `x`). `ZetaBalance.riemannHypothesis_of_zetaBalanceBound` gives RH
from it. Like every frontier so far, it is equivalent to RH until the construction is formalised. What has grown is the
formalised machinery.

**After step 4**, the frontier for RH is `ZetaBalance.ZetaLatticeBound`. At each translate there is a frame of
lattices (`SlopeFrame.Frame`) meeting the hypotheses of the frame inequality. The lattices' gain over the target covers
the inert-prime gap (G), with small losses (Z). `ZetaBalance.riemannHypothesis_of_zetaLatticeBound` gives RH from it.
- **Equivalent to the frontier after step 3.** Whenever the averaged gap bound holds, frames of rank one satisfy it.
  Its content is how the gap is paid for: by slopes of lattices, through Bost's inequality and the frame inequality.
- **A real cut needs more.** The frontier below it must say where (G) comes from: vanishing at inert primes, mass
  formulas, and the sizes of the auxiliary primes.

**For every primitive `χ`**, steps 3 and 4 leave `ZetaBalance.BalanceBound` and `ZetaBalance.LatticeBound`: the same
data for each primitive `χ`, in a setting with a character `κ` of `A` lifting `χ`, averaged over the kernel `A₀` of
`κ`, with translates carrying the shares of the cyclic family, and with the `3o` twists as the analytic input.
`ZetaBalance.rhAndGRH_of_balanceBound` and `ZetaBalance.rhAndGRH_of_latticeBound` give the Riemann hypothesis for `ζ`
and every Dirichlet `L`-function, through `WindowGRH.rhAndGRH_of_windowBound`. `ζ` is the case `χ = 1`, `κ = 1`
(section "Steps 3 and 4 for every primitive character").

**With the thin scales proved**, conditionally on the half-plane `Re s > 11/12`, the frontier for RH is
`ZetaBalance.ZetaTwistBound`: lattice data with small twists, the thin classes beyond `(Nx)^{log x}`.
`ZetaBalance.riemannHypothesis_of_zetaTwistBound` gives RH from it.

**With both analytic inputs proved**, conditionally on the half-plane, the frontier for RH is
`ZetaBalance.ZetaPairBound`, the construction alone. At arbitrarily small `ε`, for every large `Y`, every pair of
primes `(q, d)` with the arithmetic of `ZetaTwist.WinPair` has a sub-window `[Y′, Y′²]` of `[Y, Y^A]` on which every
`x` has lattice data in a setting with that pair. `ZetaBalance.riemannHypothesis_of_zetaPairBound` gives RH from it.

**For RH and GRH**, conditionally on the half-plane, the frontier is `ZetaBalance.PairBound`: the same for every
primitive `χ`, in settings with a character `κ` of `A` lifting `χ`. `ZetaBalance.rhAndGRH_of_pairBound` gives the
Riemann hypothesis for `ζ` and every Dirichlet `L`-function from it, and `LinnikGRH.dirichletRH_of_rhAndGRH` turns that
into the hypothesis of the library's results under GRH (`LinnikGRH.linnik_two`, `LinnikAlmostAll.almostAll_one`).

**Below `PairBound`**, the frontier is `ZetaBalance.SixTermBound` (`SixTerm`): the same with six-term data in place of
lattice data. At each translate, numbers of the words and of the translate meet the archive's six inequalities G1–G6,
and a key identity sums them to (G). `ZetaBalance.rhAndGRH_of_sixTermBound` gives RH and GRH from it. Like the
frontiers above it, frames of rank one satisfy it whenever the averaged gap bound holds.

**What step 2 simplified against the archive.**
- Landau's theorem on windows is proved once, for any finite family of characters with positive weights. The
  weights `1/(3o + 1)` matter only for step 3.
- Real parts are taken in the transform, `(Φ(s) + conj Φ(conj s))/2`. So no symmetry of `L(s, χ)` under
  conjugation is needed, where the archive proves one in 100 lines.
- `(s − 1)ζ(s)` and `L(s, χ)` are handled by one construction, `−F'/F(s) + s·F'/F(1)` over `s(s − 1)`, continued
  across `s = 1` with Mathlib's `dslope`. For `ζ`, `F` is Mathlib's `riemannZeta₁`, with `ζ₁'(1) = γ` from Mathlib.
- The Taylor coefficients of the Laplace transform come from the library's `LandauLaplace`. Cauchy's estimate and
  the derivatives of `c/(s − p)` come from Mathlib.

**Reuse.** An audit of the library against steps 1 and 2 (23 November 2026) found three things.
- **Replaced by the stack:**
  - the trivial zeros of `ζ`, now `WeilTest.IsNontrivialZero.mem_strip` from the library's `T1bt`, which cut 45
    lines;
  - `(s − 1)ζ(s)`, now Mathlib's `riemannZeta₁`;
  - our copy of Mathlib's `riemannZeta_ne_zero_of_one_le_re`;
  - the punctured neighbourhoods of `conj`, now Mathlib's `Homeomorph.map_punctured_nhds_eq`.
- **Nowhere in the stack:** Landau's theorem on windows, the ramp transforms, the pole asymptotics, the
  nearest-pole geometry and the character families.
- **Duplicated in heavy modules:** five small lemmas of `HalfPlaneGRH` had seven copies in six other modules
  (`RealCharHalfPlane`, `RealDirichlet`, `HalfPlaneJoinsChar`, `D2GS`, `LinnikAFE`, `LinnikCGLReflect`). Those
  modules now import `HalfPlaneGRH` instead.

## Step 3, re-examined

A reading of the archive's balance layer (`ch_balance`, `ch_core`, `core_gm`; about 6,000 lines with Landau on
windows) shows that it only converts between statements of the same strength.

- **Its input.** It takes an inequality on ramp-weighted sums over prime powers inert in `ℚ(√−d)`. The primes lie in
  given Frobenius classes of an abelian CM field `E` of degree about `x^{2+8ε}`. The sums run over `m ≈ √x` weight
  vectors, and the inequality must hold with the error of a single one.
- **Its strength.** Averaged over the 2-part of `Gal(E/ℚ)`, that inequality is GRH for `4o` characters, stated
  one-sidedly.
- **Where the new mathematics is.** In the lattice argument that proves the inequality: one lattice quantity bounds
  the sum over all the weight vectors at once, through slopes (`ch_top` and below).

So formalising the balance layer as the archive does would make the frontier more complicated, not more classical.

## The lattice layer, read

A second reading (23 November 2026) found the archive's new idea under `ch_top`. It is Stepanov's method in
Arakelov form.

1. **Vanishing.** A period `B_u` is built from a chain of `m ≈ √x` theta lifts between definite unitary groups,
   `U(X₀) → U(X₁) → … → U(X_m)`. It vanishes to high order at every place above an inert prime `p`. Each lift
   adds one more order, and the gain per lift is exactly the ramp `(a/pᵉ − w)⁺` of the inert-prime sum, for odd `e`.
2. **Degree.** Dividing out that vanishing gives a hermitian lattice `N_u` of algebraic modular forms whose
   Arakelov slope rises by the whole ramp sum.
3. **The cap.** A frame version of Bost's slope inequality (`TheoremF`) bounds the mean of `μ(N_u) − h(B_u)` by the
   slope of one target lattice. That slope cancels.
4. **The balance.** Order `m` against degree `m²` gives `m ≈ √x` and the square-root error.

**The cleanest cut** sits just below `ch_top`. Call it the Arakelov–Stepanov frontier, for `ζ` alone. For all large
`x` and every translate there are:
- hermitian lattices `N_u` and `C` over a number field;
- maps `B_u : N_u → C`;

with three properties:
- **gain beats excess:** `μ(N_u) − h(B_u) ≥ μ(C) + (the inert-prime gap) − E`;
- **spread:** bounded spread of the slopes;
- **frame:** an almost tight frame at one archimedean place.

Above that cut everything is elementary or general theory:
- the balance identity and the step from cosets to the family, about 4,000 archive lines;
- hermitian lattices with Bost's inequality, Harder–Narasimhan polygons and the frame inequality, about 6,600;
- the algebra of `ch_top`, about 3,000;
- a classical choice of the auxiliary primes `q` and `d`, by Jutila's zero-density estimate and Page's theorem.

Below it is the construction: the theta lifts and their periods, local divisibility (`LinkG`, 240,000 lines), the
frame condition (`LinkS`, 105,000), slopes of modular forms (mass formulas), and a covolume bound (2.16 million).
The theta side holds 5.75 million lines, 1.34 million of them formalised literature. Of the whole proof, 2.98
million lines (29%) are the 176 published inputs.

**Shortcuts it suggests** (inferred, not checked):
- build the lattices concretely and drop the witness layers;
- drop the literature the proof never reaches (Rallis, seesaw);
- replace the toroidal covolume bound by a mass-formula computation, since only a lower bound on one slope is
  needed;
- for `ζ`, check whether the three quadratic twists, and with them `VWin`, `Row` and local Langlands, can be
  avoided. That question decides several million lines.

## Blueprint for steps 3 and 4, `ζ` alone

Specifications read from the archive on 23 November 2026, and simplified.

### Step 3: the balance (elementary)

**Objects at scale `x`**, for `0 < ε < 1/52`:
- **The primes.** `q ≡ 3 (mod 8)` and `d ≡ 7 (mod 16)` are primes with `(2/d) = (q/d) = 1`. The archive also asks
  for bounds on their size, and that every odd prime `p ≤ Y^{ε/5}` divide `d + 1`.
- **The group.** Fix `2^e ≈ x^{2+8ε}`, and let `A = (ℤ/2^{e+2})ˣ/{±1}`, cyclic of order `2^e`. Put
  `Φ = {±1} × A`; it is `Gal(E/ℚ(√−d))` for `E = ℚ(√−q, √−d, ζ_{2^{e+2}} + ζ_{2^{e+2}}⁻¹)`.
- **The partner.** For `n` prime to `2q`, `ρ_t(n) = ((−n/q), [n]_A·t) ∈ Φ`.
- **Weights.** `w : Φ → (0, ∞)`.
- **The inert sum.** `ASK(a,t,w) = Σ_{(n,2q)=1} Λ(n)(1 − χ_d(n))·(a/n − w(ρ_t(n)))⁺`, with `χ_d = (·/d)`. It counts
  the prime powers inert in `ℚ(√−d)` and the powers of `d`.
- **Its main term.** `MAIN(a,w) = a(log a − 1 − γ + L′/L(1,χ_d) − |Φ|⁻¹Σ_{ρ∈Φ} log w(ρ))`.
- **The gap.** `gap(u₀) = Σ_{t∈TT} Σ_{j<m} [ASK(a_t, t, w_{u₀,j}) − MAIN(a_t, w_{u₀,j})]`.

**The lemmas.**
- **Lemma B, the balance identity.** `ASK − MAIN = |Φ|⁻¹ Σ_{ρ∈Φ} W(ρ) Σ_{χ∈Ĝ} conj χ(γ_t(ρ)) g_χ(a/W(ρ))`. Here:
  - `Ĝ` is the set of Dirichlet characters `χ_d^α χ_q^β ξ`, with `ξ` an even character mod `2^{e+2}`;
  - `g_χ` is the ramp error of the primitive `χ*`;
  - `γ_t(ρ) = c·ρ·t⁻¹`.

  The proof is orthogonality, the ramp identity, and `Σ_{g∉Φ} conj χ(g) = |Φ|(1[χ=1] − 1[χ=χ_d])`.

  **Done** (`ZetaBalance.Setting.balance`, 728 lines), with real parts. It holds for every real `a`. It needs only `q`
  and `d` prime, `q ≡ 3 (mod 4)` and `(2/d) = (q/d) = 1`: neither `q ≡ 3 (mod 8)` nor any congruence on `d`. The powers
  of `d` need no case of their own. The key lemma is new: at a prime `p` prime to the level of `ψ`, the primitive
  character of `ψ·D` takes the value `ψ*(p)·D*(p)` (`ZetaBalance.prim_mul_apply`).
- **Lemma T, the thick part.** The thick classes are `Θ(u₀) = {(−1, s·u₀) : s ∈ T2}`. `Th(u₀,t)` is the part of
  the identity at `Θ(u₀)`, with every thick weight replaced by one value. Then `Th(u₀,t) ≤ ASK − MAIN + (small)`.
  Only this side is used. Two facts give it:
  - a Lipschitz bound on `w·g_χ(a/w)` in `w`, from Chebyshev;
  - `|g_χ(y)| ≤ θy` for `y` beyond the thin scales, for all `4|A|` characters. This cannot be dropped: every `ξ`
    occurs on thin classes, and only the thick part is averaged.
- **Lemma Avg.** Averaging over `u₀` translates `Θ(u₀)`, so it keeps only the characters trivial on `A`:
  `Σ_{u₀} Th(u₀,t) = (r|T2|/2)·(Gz − g_{χ_d} + g_{χ_q} − g_{χ_qχ_d})(y)`, with `r` the thick value. The weights may vary
  freely with `u₀` and `j`.
- **Theorem Z.** The averaged gap bound with `m ≥ x^{1/2−ε}`, `|T2| ≥ x^{−ε}|A|` and bounds on the three twists gives
  `Gz(x) ≤ x^{1/2+O(ε)}`. On windows this is `ZetaWindowBound` (Theorem E).

**What the archive does** (`ch_core`, `core_gm`, `ch_top`, read on 23 November 2026).
- It measures the thick weights against one `b = exp(x^ε)`, with integer `a_t` and `|a_t/b − x| ≤ 1`.
- So it must move each `a_t/b` to `x`. That needs a Lipschitz bound on `Gz`, from Mertens, and on the twists, from a
  bound on `L′/L(1, χ)`.
- `ch_top` bounds the gap at every translate, though only the average is used.
- `q` and `d` are fixed once per window, not at each `x`.
- The analytic inputs are proved, not cited: a mean-square argument over `q` and `d` (about 4,300 lines) gives the
  twist bounds, zero-free boxes and the thin-class bounds. Jutila and Page are stated, but only for a route the main
  theorem does not use.

**Ours** (`ZetaGap`, in progress) is simpler.
- It measures the thick weights for the translate `t` against `a_t/x`. Then the averaged identity evaluates every
  error at `x` itself. So it needs:
  - no Lipschitz bound on `Gz`, and no Mertens;
  - no bound on `L′/L(1, χ)`;
  - the twists bounded only at the point `x`.
- It needs no `b`, `k`, `X′`, `b′` or `Bracket`.
- All losses are powers `x^ε`. The frontier asks only the averaged gap bound, `Σ_u gap(u) ≤ |A|·x^ε·Σ_t a_t`, and
  Theorem Z gives `Gz(x) ≤ 7x^{1/2+3ε}`.
- The archive's data meet these conditions for large `x`. The spread of its `a_t` is far below what the thick weights
  allow.

### Step 4: slopes

**Lattices.** A hermitian `O_K`-lattice, for `K` totally complex, can be taken as a Euclidean ℤ-lattice with an
`O_K`-action, using only `O_K`-stable saturated sublattices. Its degree is `−log covol`, and
`μ = 2·deg/rk_ℤ − log 2 + log|d_K|/[K:ℚ]`. The height of a map is `h(φ) = n_∞⁻¹Σ_v log‖φ_v‖²`.

**What is used of them.**
- **(P1)** Additivity of degree on quotients.
- **(P2)** Monotonicity in equal rank.
- **(P3)** `μ(ψΛ) ≥ μ(Λ) − h(ψ)`, from Hadamard's inequality.
- **(P4)** The rank of a sublattice is read at any one place.
- **Bost's inequality**, in the form (B1): `μ_min(A) − h(φ) ≤ μ_min(φA)`. Its proof uses quotients and (P3) only.

No finiteness theorem for sublattices is needed. Approximate maximisers of `deg − θ·rk` suffice, because rank is
strictly monotone on saturated sublattices.

**The frame inequality**, in sharp form with rank spreading.
- **Rank spreading (RS):** sublattices of total corank at most `ε′Σr_i` have images of corank at most
  `(α + βε′)·rk C`.
- **Hypotheses:**
  - `s·Σr_i ≤ Σr_i(μ(N_i) − h_i)`;
  - `μ_max(N_i) − h_i ≤ s + u`;
  - `s − μ_min(C) ≤ HH`.
- **Conclusion:** `μ(C) ≥ s − βu·log(1 + HH/u) − α·HH`.
- **Proof:** sublattices nearly maximising `deg − θ·rk`, then Markov, then (B1) on images, then Abel summation. No
  slope polygon is needed.
- **Done:** `SlopeFrame.frame_inequality` (216 lines) proves this over abstract lattices of sublattices. It assumes
  rank and degree with rank strictly monotone, Bost's inequality on images, closure under sums, and rank spreading.

**The frontier for `ζ`.** For all large `x` in windows, there are lattices `N_u`, `C` and maps `B_u` with:
- **(G):** `s ≥ μ(C) + gap − E`, on average over translates and words;
- **(R)**, the range condition;
- **(RS)**;
- **(Z):** `E + βU·log(1 + HH/U) + α·HH ≤ x^{C₀ε}·B`.

The frame inequality then gives the averaged gap bound.

**What `ch_top` is** (read on 23 November 2026). It touches no lattice: it is algebra on real numbers under eleven
numeric hypotheses. The frame inequality has already been applied, once per translate `u`.
- **The frame at `u`.** Each translate has its own words `ω`. Each word has a lattice `N_ω`, the vanishing part of the
  algebraic modular forms of its theta chain. All map into one target `C_u`, the dual of a lattice of periods, by
  `B_ω`.
- **Over what.** The lattices are hermitian over a totally complex Galois field `K`.
- **Heights.** These are averaged over the infinite places, `h(φ) = n_∞⁻¹Σ_v log‖φ_v‖²`, and Bost's inequality is used
  in that averaged form.
- **Slopes.** `μ = 2·deg/rk_ℤ − log 2 + log|d_K|/[K:ℚ]`, as above.
- **(G) is six inequalities, summed.**
  - The vanishing at inert primes raises `μ(N_ω)` above the slope of the modular forms.
  - The gain dominates the inert-prime sum.
  - The slope of `C`, the sizes of auxiliary primes and the split primes give `MAIN`, once the forced vanishing,
    `log(g₀g₁)`, `v` and `π` cancel.
  - The weights `w_{u,j}(ρ) = e_j(τ)`, the Harish-Chandra parameters, reach the lattices only through the sizes of the
    auxiliary primes.
- **(RS)** holds at one complex place, for nearly orthogonal periods. It gives `α = (1 − δ)⁻¹(η + 4√e)` and
  `β = 4(1 − δ)⁻¹`.

**The cleanest cut**, per translate `u`, is a frame `N_{u,ω} → C_u` with Bost's inequality, closure under sums and
(RS). Put `s_u` for the rank-weighted mean of `μ(N_{u,ω}) − h_{u,ω}`, and let `U_u > 0` and `H_u ≥ 0` bound the range:
`μ_max(N_{u,ω}) − h_{u,ω} ≤ s_u + U_u`, and `μ_min(C_u) ≥ s_u − H_u`. Then:
- **(G)** `Σ_u gap(u) ≤ Σ_u (s_u − μ(C_u)) + E`;
- **(Z)** `E + Σ_u (α H_u + β U_u log(1 + H_u/U_u)) ≤ |A|·x^ε·Σ_t a_t`.

The frame inequality at each `u` gives the averaged gap bound of `ZetaBalance.BalanceData`. Against the archive:
- (G) is needed only on average over translates, not at each;
- its cancelling pairs merge;
- the archive's `−log|W|` slack goes, since closure under sums is exact here;
- (B1) comes from Hadamard place by place (`GramVolume.volLe_iSup`) rather than by rescaling.

**Hermitian lattices, done** (23 November 2026). The frames of the frontiers can now be the archive's own.
- **Lattices with places** (`PlaceLattice`). A discrete subgroup carries pairwise orthogonal subspaces `V v` at its
  places, and a class `S` of saturated sublattices: a sublattice of `Sat Λ` with `0` and `Λ`, whose spans are balanced,
  `|P|·dim (U ∩ V v) = dim U` at each place. Balance makes a span the orthogonal sum of its parts, so no separate
  compatibility condition is needed. `S` is a slope lattice, closed under sums, by `EuclidLattice`'s modularity.
- **Bost with averaged heights** (`PlaceLattice.bost`). If `‖φ x‖ ≤ e^{h v}‖x‖` on each `V v`, and images and preimages
  keep to the classes, then `μ_min(img φ a) ≥ μ_min(a) − h̄`, with `h̄ = |P|⁻¹ Σ_v h v`. `EuclidLattice.bost_le` now asks
  only that `φ` multiply volumes in `W = span a ⊖ span K` by at most `e^{h·dim W}` (`GramVolume.VolLe`). `W` is
  balanced when `span a` and `span K` are (`PlaceLattice.Balanced.orthogonal_inf`), and Hadamard place by place gives
  the factor (`GramVolume.volLe_iSup`). Fischer's inequality joins the places, so the map need not be block-diagonal:
  only its norm on each `V v` counts.
- **Hermitian `O_K`-lattices** (`HermitianLattice`), for a totally complex `K`. `E` is a complex inner product space,
  the orthogonal sum of `V v` over the complex places, with `k ∈ K` acting by `σ_v(k)` on `V v`. The class is the
  `O_K`-stable saturated sublattices. Their spans are balanced (`HermitianLattice.balanced`) by two facts:
  - `O_K` spans `K ⊗ ℝ` (Mathlib's `latticeBasis`), so spans are `K ⊗ ℝ`-stable and contain their parts;
  - a count of ranks: the `O_K`-span of `d` vectors independent at one place has rank `d·[K:ℚ] = 2d·n_∞`, while its
    part at each place has dimension at most `2d`.

  No `K`-vector space, Galois group or unit enters. Maps that commute with `O_K` keep the classes, so hermitian lattices
  form frames with the archive's averaged heights (`HermitianLattice.frame`). The archive's units,
  `μ = 2·deg/rk_ℤ − log 2 + log|d_K|/[K:ℚ]` and `h = 2h̄`, double and shift these.
- **Size.** `PlaceLattice` has 220 lines and `HermitianLattice` 345. `GramVolume` grew by 111 lines, and `EuclidLattice`
  by 10.

**Order of work.**
1. **In parallel:** Lemma B with its objects, and the abstract frame inequality.
2. **Then:**
   - Lemmas T and Avg and Theorems Z and E, giving the frontier after step 3;
   - the concrete lattices for the abstract frame inequality;
   - the `ζ` form of `ch_top`.

## The analytic inputs

The frontier after step 4 assumed two classical inputs: the thin scales and the twists. Both are now proved, using what
the library has formalised. That includes the half-plane `Re s > 11/12` for every Dirichlet `L`-function
(`Eis.LFunction_ne_zero_of_re_gt`), an input no referee has read (`formalisations/openai-half-plane.md`). Results that
use it are conditional on it, as the library's own D2 modules say.

- **Thin scales** (`ZetaThin`). Done: `ZetaBalance.thin_of_large`, so `ZetaBalance.riemannHypothesis_of_zetaTwistBound`
  gives RH from `ZetaBalance.ZetaTwistBound`, the frontier after step 4 without that input.
  - For a primitive `χ ≠ 1`, `g_χ(y) = y(L′/L(1, χ) + Σ_{n≤y} χΛ(n)/n) − ψ(y, χ)`. Both parts are bounded uniformly in
    the modulus, by `GSTail.logDeriv_one_tail` and `ChiUniform.psiChi_le_uniform`.
  - For `ζ`, the same needs `Σ_{n≤y} Λ(n)/n = log y − γ + O(y^{−1/12+η})` (`ZetaBalance.mertens_error_le`). It is
    `GSTail.tail_le_of_sum_le`, the argument of `GSTail.logDeriv_one_tail` made general, applied to `Λ − 1`.
  - So every thin class beyond `(N x)^{log x}` is covered. The archive's zero-free boxes near `s = 1` and its checks of
    small conductors are not needed.
- **Twists** (`PrimeCharSums`, `MeanSquareSup`, `TwistFamily`, `ZetaTwist`). Done: `ZetaTwist.exists_winPair_twists`.
  Let `χ` be a character of order `o`. For `0 < ε ≤ 1/2` and `A ≥ 1`, every large `Y` has a pair `(q, d)` meeting
  `ZetaTwist.WinPair ε Y` whose `3o` twists `χ_d^α χ_q^β χ^k` (`ZetaTwist.twist`), `(α, β) ≠ (0, 0)` and `k < o`, have
  `|g(y)| ≤ y^{1/2+ε}` at every `y ∈ [Y, Y^A]`, `g` the ramp error of the primitive character. For `ζ` these are `χ_q`,
  `χ_d` and `χ_qχ_d` (`ZetaTwist.exists_winPair_twists_one`). As in the archive, this comes from a mean square over a
  family of primes, not from zeros near the critical line.
  - Write `g_χ(y) = −Σ_{n≤Z} Λ(n)χ(n)min(1, y/n) + y·(L′/L(1, χ) + Σ_{n≤Z} χΛ(n)/n)` (`PrimeCharSums.rampErr_eq`).
    The second term is a tail, small by `GSTail`.
  - The mean square of the first sum over the primes of a progression is dominated by its diagonal, `y` times a power
    of `log y`. The off-diagonal terms are sums of a Jacobi character over those primes, small by the uniform prime
    number theorem for characters (`PrimeCharSums.norm_sum_Ioc_modEq_le`).
  - The same holds for its increments in `y`. A discrete Sobolev step and Markov's inequality
    (`MeanSquareSup.card_bad_le`) then give most of the family a bound uniform in `y ∈ [Y, Y^A]`, for finitely many
    complex weights at once (`TwistFamily.exists_good_fin`). This is done for `q`, with the `o` weights `χ^k`, then
    for `d` given `q`, with the `2o` weights `χ^k` and `χ^kχ_q`.
  - The primitive character of a twist is its weight times the Jacobi symbol at every `n` prime to `f·q·d`
    (`ZetaTwist.prim_twist_apply`). The other `n`, the prime powers of `fqd` and of the family's modulus, weigh
    `O(z log³Y)` in all, far below `√Y`, so no formula at those primes is needed. The twist is not trivial, as the
    conductor of `χ_d` or of `χ_q` cannot divide that of the other factors (`ZetaTwist.twist_ne_one`).
  - The archive spends about 28,000 lines here, mostly on a prime number theorem in progressions that copes with
    exceptional zeros. The half-plane removes that, together with Siegel, Page and Deuring–Heilbronn. The library's
    four modules take about 1,900 lines.
- **The shape of the frontier.** The lattice side fixes the pair `(q, d)` from the window's base and then chooses its
  sub-window. That is why the twist bound must hold uniformly on `[Y, Y^A]`. The lattice side needs only arithmetic
  of the pair (`ZetaTwist.WinPair`):
  - `q ≡ 3 (mod 8)` and `d ≡ 7 (mod 16)`, in given size ranges;
  - `q` and every odd prime `p ≤ Y^{ε/5}` divide `d + 1`.

  So the frontier for `ζ`, `ZetaBalance.ZetaPairBound` (`ZetaPair`), quantifies over every such pair, as the archive's
  own window input does. It is the construction alone: every `x` of a sub-window `[Y′, Y′²]` of `[Y, Y^A]` has lattice
  data in a setting with that pair. `ZetaBalance.riemannHypothesis_of_zetaPairBound` gives RH from it, and
  `ZetaBalance.PairBound`, the same for every primitive `χ` with `κ` lifting `χ`, gives RH and GRH
  (`ZetaBalance.rhAndGRH_of_pairBound`). On the way, the `3o` twists of a setting become the ramp errors of the
  concrete twists: for `κ` lifting `χ`, `D_{(α,β,κ^k)}` is `χ_d^α χ_q^β χ^k` changed from the level `f·q·d` to `N`
  (`ZetaBalance.Setting.Lifts.g_twist`). For `ζ`, `κ = 1` lifts the character mod `1`.
- **The modules.** Line counts include the documentation.

  | Module | Lines | Content |
  |---|---|---|
  | `PsiExplicit` | 66 | `ψ` and `θ` within `C t^{11/12+η}` of `t` at every `t ≥ 1` |
  | `ZetaThin` | 284 | the thin scales |
  | `PrimeCharSums` | 413 | sums of a character over the primes of a progression, uniformly in the modulus; the ramp error at a cutoff |
  | `MeanSquareSup` | 90 | discrete Sobolev and Markov: few members of a family are bad anywhere on an interval |
  | `TwistFamily` | 852 | the mean square over a family of primes, and a member good on the whole window for finitely many weights |
  | `ZetaTwist` | 550 | the pair `(q, d)` whose `3o` twists of `χ` are small on `[Y, Y^A]`; for `ζ`, `χ_q`, `χ_d` and `χ_qχ_d` |
  | `ZetaPair` | 159 | the twists of a setting as concrete characters; RH and GRH from `ZetaBalance.PairBound`, RH from `ZetaBalance.ZetaPairBound` |

## Steps 3 and 4 for every primitive character

Done on 23 November 2026, by generalising `ZetaBalance`, `ZetaGap` and `ZetaFrame` in place; the names below are in
the namespace `ZetaBalance`. `ζ` is the case `χ = 1`.

- **The setting** (`ZetaBalance.Setting`). It takes primes `q ≡ 3 (mod 4)` and `d` with `(2/d) = (q/d) = 1`, a modulus
  `QS` prime to `q` whose every prime `p` has `(p/d) = 1`, and any subgroup `K` of `(ℤ/QS)ˣ`. Then `A = (ℤ/QS)ˣ/K`, and
  the level is `N = QS·q·d`. The archive's choices are instances: `QS` a common multiple of `2^{e+2}` and `f`, and
  `K = {u ≡ ±1 (mod 2^{e+2}) : χ(u) = 1}`. The exponent `e` is no longer part of the setting.
- **Lemma B** (`Setting.balance`) keeps its form. `ASK` runs over `n` prime to `QS·q`, and `ξ̃` is the lift of `ξ` to a
  character mod `QS`. The primes of `QS·q` contribute `0` to the kernel, as `(p/d) = 1` there. `χ* = 1` only for
  `χ = 1`, since `ξ̃*` vanishes at a prime of `QS` unless `ξ = 1` (`Setting.eq_one_of_prim_lift`).
- **The parity twist is not needed.** Lemma B never uses that `c = (−1, −1, 1)` is complex conjugation, so it holds as
  it stands for odd `χ`, where `[−1]_A ≠ 1`. The archive's twist of the Artin map only fixes coordinates. Taking
  `(−1, −1, [−1]_A)` for `c` replaces each translate `t` by `[−1]_A t`, which multiplies the `k`-th share below by
  `χ(−1)^k`. The frontiers ask for the shares in the coordinates of Lemma B.
- **Lemma Avg** (`Setting.sum_Th`). Let `κ` be a character of `A` of order `o`, with kernel `A₀`, and let `T2 ⊆ A₀`.
  Then `Σ_{u ∈ A₀} Th(u, t) = (r|T2|/2o)·Re Σ_{k<o} κ(t)^k Σ_{α,β} (−1)^α g_{(α,β,κ^k)}(y)`. The kept characters are
  not counted. Since `1[κ(u) = 1] = o⁻¹ Σ_{k<o} κ(u)^k`, orthogonality keeps exactly the `κ^k` (`sum_dual_sum_A₀`).
- **Theorem Z** (`BalanceData.cyclicG_le`). The translates carry shares:
  `|Σ_t a_t κ(t)^k − Σ_t a_t/(3o + 1)| ≤ x^{ε−1} Σ_t a_t` for `0 < k < o`. Assume the gap averaged over `A₀` is
  bounded as for `ζ`, the setting is thin, the `3o` twists are at most `x^{1/2+ε}` at `x` (`Setting.Twists`), and the
  kept errors `g_{(0,0,κ^k)}(x)` are at most `x^{3/2+ε}`. Then
  `Re g_1(x) + (3o + 1)⁻¹ Σ_{0<k<o} Re g_{κ^k}(x) ≤ (9o − 2)x^{1/2+3ε}`. For `ζ` this is `7x^{1/2+3ε}`, as before.
  The kept errors bound the share errors; a crude bound gives them for large `x` (`eventually_norm_rampErr_le`, from
  `Λ(n) ≤ log x` and `Σ_{n≤x} 1/n ≤ 1 + log x`).
- **The cyclic family** (`Setting.Lifts.cyclicG_eq`). Say `κ` lifts `χ` (`Setting.Lifts`) when `f ∣ QS` and `κ̃ = χ` at
  level `QS`. Then `κ^k` lifts `χ^k`, and the weighted error is `(WindowGRH.cyclic χ).G(x)`.
- **The frontiers**, `BalanceBound` and `LatticeBound`, ask for this data for every primitive `χ`. Frames are needed
  only at `u ∈ A₀`, and (G) and (Z) are summed over `A₀`.
- **The thin scales carry over.** `thin_of_large` holds for every setting, so for every `χ`, conditionally on the
  half-plane.
- **The twists for every `χ`** (`ZetaTwist.exists_winPair_twists`, section "The analytic inputs"). The archive's
  `ψ_kχ_q`, `ψ_kχ_d` and `ψ_kχ_qχ_d`, `ψ_k = (χ^k)*`, have the primitive characters of the library's twists
  `χ_d^α χ_q^β χ^k` at level `f·q·d` (`ZetaTwist.twist`), and these are the characters of a setting in which `κ` lifts
  `χ` (`Setting.Lifts.g_twist`). No primitive character `ψ_k` is formed: the weights of the mean square are the
  values of `χ^k`, which agree with those of `ψ_k` at every `n` prime to `f`.
- **The pair-first frontier for every `χ`** (`ZetaPair`): `PairBound`, and `rhAndGRH_of_pairBound`, conditionally on
  the half-plane. Done on 23 November 2026, with no change to `lib/core`. The pair `(q, d)` is chosen for `χ`, and the
  settings asked for exist once `Y` is large: their modulus `QS` must be a multiple of `f` whose every prime `p` has
  `(p/d) = 1`, and a pair of `ZetaTwist.WinPair` has `(p/d) = 1` for every prime `p ≤ Y^{ε/5}`, by quadratic
  reciprocity, as `d ≡ −1` modulo every odd one and `d ≡ 7 (mod 16)`.
- **Linnik's exponent.** `HalfPlaneGRH.RHandGRH` covers every character, primitive or not, so it is GRH in the words of
  the library's results under it (`LinnikGRH.dirichletRH_of_rhAndGRH`, in `RHJoinsLinnik`): `PairBound` gives
  `LinnikGRH.linnik_two` and `LinnikAlmostAll.almostAll_one`, conditionally on the half-plane.

## The construction, measured

Two studies of the archive (23 November 2026) measured what lies below the frontier.

**No cut with free objects has content.** Suppose a frontier leaves the lattice of forms, the target `C` and the period
maps existential, however much structure it demands. Then rank-one witnesses satisfy it whenever the gap bound holds.
- **The witness.** Take one word, `C = O_K`, `N = C` and `B = id`. Choose the orders so that the split-prime term and
  the gain balance the main term, and scale `C`'s metric so its slope is that main term.
- **What holds.** The six gain inequalities G1–G6 (the archive's `QuotientSlopeBoundsWith`, `Slopes`, `DIV`,
  `Count5`, `EComp5`, `LossBounds`), the range, depth and rank spreading all hold. G6 holds exactly when the gap bound
  does.
- **Where content starts.** Content appears only once the objects are *defined*: the periods up to scalars, `C` with its
  metric, and the integral forms.

So the honest next frontier is the archive's interface evaluated at a canonical theta datum. The objects behind it:
- **forms:** definite hermitian spaces over a CM field `E`; lattices in a genus, up to isometry, with mass weights
  `1/|Aut L|`; Weyl-module coefficients with a Fock norm; the Petersson norm; the forms of level `T_ω`;
- **periods:** theta kernels, their chain, the periods `B_ω`, and the target `C = RR^∨`.

Stating it is estimated at 5,000–10,000 lines. Mathlib has CM fields, infinite places, adeles, sesquilinear forms and
double cosets as types. It has no hermitian spaces over CM fields, unitary groups, genus theory, mass formulas,
highest-weight theory or theta correspondence.

**The sizes.** Rule-`L` cones, from the archive's declaration map:

| Part | Lines | Of which literature |
|---|---|---|
| `riemannHypothesis` | 10.23M | 2.98M |
| the 182 published results, taken as given | frees only 1.05M | |
| the construction itself | 9.2M | |

- **Why so little is freed.** The construction reuses most of the literature's cone directly, and 31 of the 182
  published statements are never consumed (18K lines).
- **Redundancy** is about 10–20%: repeated statements, trivial lemmas, unused structure fields. The rest of any saving
  must come from writing the proofs differently.
- **The rebuild's own ratio so far:** 0.28 for steps 1–4, 0.11 for the lattices, 0.09 for the twists (with the
  half-plane).

The core theorem's seven inputs, and what to do with each:
- **The covolume bound (`hX`, 2.16M).** It is the largest prize: taking it as given frees 1.66M lines (toroidal
  compactifications, Arakelov geometry, vanishing theorems, Hironaka). A mass-formula route may exist, but the bound is
  on the indefinite side and the mass formula on the definite side.
- **The window input (`VWin`, 2.23M).** It bounds Tate–Shafarevich-type groups of the host cyclotomic fields, through
  automorphy lifting and `p`-adic Hodge theory. It is fed by **Row** (2.26M): Galois representations for regular
  algebraic polarized cuspidal representations over CM fields, proved through theta lifts. If Row is as broad as its
  statement reads, that is a new proof of a major theorem; this has not been audited. Both are best kept as stated
  inputs.
- **The theta constants (`hA`, `hM`, 0.48M).** Matched local data and Rallis-type step identities, with the closing
  theorem `theoremK` (0.29M).
- **The published bundles `P` and `F`.** Representation theory of unitary groups, Siegel–Weil, the Weil representation
  and Howe duality. Their statements total about 31K lines.
- **Local Langlands (`hL`).** Only the tame part, 57K lines; not Harris–Taylor.
- **The core proper (5.9M).** It proves the unitary mass formula itself (252K lines).

Fresh-rebuild estimates, all rough:

| Taken as stated inputs | Estimated size |
|---|---|
| The seven inputs and Row | 0.5–1.5M lines |
| Only the 182 published results | 0.8–2.5M lines |
| Nothing | 1.0–3.2M lines |

## Next

For `ζ` and every Dirichlet `L`-function, every step above the construction is done. RH and GRH follow from
`ZetaBalance.PairBound`, and from `ZetaBalance.SixTermBound` below it; RH alone follows from
`ZetaBalance.ZetaPairBound`. These frontiers ask only for the construction: lattice data on a sub-window, for every
pair `(q, d)` with the archive's arithmetic. Their frames may be the archive's own, hermitian lattices over a totally
complex `K` with heights averaged over the places (`HermitianLattice.frame`). In order:

1. **The six-term interface.** Done on 24 November 2026 (`SixTerm`, 265 lines, 57 of them the module's
   documentation): G1–G6, the key identity (`ZetaBalance.Setting.key_identity`) with its cancellations, and the frame
   inequality give `PairBound` (`ZetaBalance.rhAndGRH_of_sixTermBound`). With `ZetaFrame`'s 109 lines, that is the
   algebra of `ch_top`, about 3,000 archive lines. Against the archive:
   - G5 is one-sided, and the range condition (R) stays a hypothesis of the frame;
   - the words' losses and the archive's slack sizes merge into one slack per inequality, all in one budget with the
     losses of the frame inequality.

   It is still equivalent to the gap bound, as above: frames of rank one satisfy it whenever that bound holds.
2. **Self-contained components:**
   - the sizes of the auxiliary primes;
   - the frame condition at one complex place (`LinkS`, about 100K archive lines). The step from it to (RS) is done
     (24 November 2026, `FrameAtPlace`, 550 lines, 113 of them documentation; the linear algebra takes 317, 47 of
     them for complex-linear maps, and the frames 162):
     - `FrameAtPlace.FrameCond.codim_le`: if maps `B_ω : V_ω → W` are nearly isometric (I) and nearly tight (T), and
       `Σ_ω codim N_ω ≤ ε′Σ_ω dim V_ω`, then `codim Σ_ω B_ω(N_ω) ≤ (η + 2(√e + ε′)/(1 − √e))·dim W`. The proof is
       Bessel's inequality and Cauchy–Schwarz for traces;
     - `FrameAtPlace.FrameCond.restrictScalars`: complex-linear maps meet the condition over `ℝ` with the `e` and `η`
       with which they meet it over `ℂ`. Mathlib lacks the trace and the adjoint of a map with restricted scalars: the
       trace is twice the real part (`FrameAtPlace.trace_restrictScalars`, from Mathlib's
       `LinearMap.restrictScalars_toMatrix` and `Algebra.trace_complex_apply`), and the adjoint commutes with
       restricting scalars (`FrameAtPlace.adjoint_restrictScalars`);
     - `PlaceLattice.spread_of_frameCond` and `HermitianLattice.spread_of_frameCond`: the condition for multiples of
       the components `π_w ∘ φ_ω` of a frame's maps at one place gives (RS), with `α = (1 − δ)⁻¹(η + 2√e/(1 − √e))`
       and `β = (1 − δ)⁻¹·2/(1 − √e)`. For `e ≤ 1/4` these are no larger than the archive's `(1 − δ)⁻¹(η + 4√e)` and
       `4(1 − δ)⁻¹`. For hermitian frames the condition is asked over `ℂ`, of the complex-linear components, as the
       archive states it;
     - ranks are read at the place, as spans of the class are balanced. The components are projections, so no
       `O_K`-linearity is used, and the image of the span at the place need only lie in the span of the image there.

     What remains is (I) and (T) for the construction's period maps at one complex place;
   - the slopes of algebraic modular forms through the mass formula (250K);
   - local divisibility at inert primes (`LinkG`, 160K), given the Weil-representation statements.
3. **The theta layer**, with the theta constants and Howe duality first taken as stated inputs.
4. **The mass-formula route to the covolume bound**, tried before any toroidal work.
