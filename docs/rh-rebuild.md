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
| 3. Balance, for `ζ` | `ZetaBalance`, `ZetaGap` | about 1,070 | about 4,000 (`ChBalance`, `ChCore`, `core_gm`) | Done: `ZetaBalance.riemannHypothesis_of_zetaBalanceBound` |
| 4. Lattices | `SlopeFrame`, `GramVolume`, `EuclidLattice`, `ZetaFrame` | about 1,030 | about 6,600 (hermitian lattices, Bost, polygons, `TheoremF`), and `ch_top`, about 3,000 | Done for Euclidean lattices: `ZetaBalance.riemannHypothesis_of_zetaLatticeBound`. Hermitian lattices with heights averaged over places, later |
| The analytic inputs, for `ζ` | `PsiExplicit`, `ZetaThin`, `PrimeCharSums`, `MeanSquareSup`, `TwistFamily`, `ZetaTwist`, `ZetaPair` | about 2,260 | about 28,000 for the twists, mostly a prime number theorem in progressions | Done, conditionally on the half-plane `Re s > 11/12`: `ZetaBalance.riemannHypothesis_of_zetaPairBound` |
| 5–6. | | | almost all of 10.7 million lines | Later |

Library line counts include the documentation; the archive has none.

**The frontier now** is `WindowGRH.WindowBound`: for every primitive `χ` and every `θ > 1/2`, the weighted error
`(WindowGRH.cyclic χ).G` is at most `C x^θ` on windows `[Y, Y^λ]` with `Y` arbitrarily large, for some `λ > 1` and
`C`. The archive's core theorem proves this in the form `HasWindows {x | Gm x ≤ x^θ} (3/2)`, which is stronger.

**For RH alone**, step 2 leaves a statement about `Λ` only. `WindowGRH.ZetaWindowBound` asks, for every
`θ > 1/2`, that `Σ_{n≤x} Λ(n)(x/n − 1) − x log x + (1 + γ)x ≤ C x^θ` on windows `[Y, Y^λ]` with `Y` arbitrarily large.
`WindowGRH.riemannHypothesis_of_zetaWindowBound` gives Mathlib's `RiemannHypothesis` from it.

**After step 3**, the frontier for RH is `ZetaBalance.ZetaBalanceBound`: for every `ε > 0`, balance data
(`ZetaBalance.BalanceData S x ε X`) at every `x` of windows with `Y` arbitrarily large. It is the inert-prime gap
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

**With the thin scales proved**, conditionally on the half-plane `Re s > 11/12`, the frontier for RH is
`ZetaBalance.ZetaTwistBound`: lattice data with small twists, the thin classes beyond `(Nx)^{log x}`.
`ZetaBalance.riemannHypothesis_of_zetaTwistBound` gives RH from it.

**With both analytic inputs proved**, conditionally on the half-plane, the frontier for RH is
`ZetaBalance.ZetaPairBound`, the construction alone. At arbitrarily small `ε`, for every large `Y`, every pair of
primes `(q, d)` with the arithmetic of `ZetaTwist.WinPair` has a sub-window `[Y′, Y′²]` of `[Y, Y^A]` on which every
`x` has lattice data in a setting with that pair. `ZetaBalance.riemannHypothesis_of_zetaPairBound` gives RH from it.

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
- (B1) comes from Hadamard place by place (`GramVolume`) rather than by rescaling.

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
  For `0 < ε ≤ 1/2` and `A ≥ 1`, every large `Y` has a pair `(q, d)` meeting `ZetaTwist.WinPair ε Y` whose twists
  `χ_q`, `χ_d`, `χ_qχ_d` have `|g_χ(y)| ≤ y^{1/2+ε}` at every `y ∈ [Y, Y^A]`. As in the archive, this comes from a
  mean square over a family of primes, not from zeros near the critical line.
  - Write `g_χ(y) = −Σ_{n≤Z} Λ(n)χ(n)min(1, y/n) + y·(L′/L(1, χ) + Σ_{n≤Z} χΛ(n)/n)` (`PrimeCharSums.rampErr_eq`).
    The second term is a tail, small by `GSTail`.
  - The mean square of the first sum over the primes of a progression is dominated by its diagonal, `y` times a power
    of `log y`. The off-diagonal terms are sums of a Jacobi character over those primes, small by the uniform prime
    number theorem for characters (`PrimeCharSums.norm_sum_Ioc_modEq_le`).
  - The same holds for its increments in `y`. A discrete Sobolev step and Markov's inequality
    (`MeanSquareSup.card_bad_le`) then give most of the family a bound uniform in `y ∈ [Y, Y^A]`
    (`TwistFamily.exists_good`). This is done for `q`, then for `d` given `q`.
  - The archive spends about 28,000 lines here, mostly on a prime number theorem in progressions that copes with
    exceptional zeros. The half-plane removes that, together with Siegel, Page and Deuring–Heilbronn. The library's
    four modules take about 1,770 lines.
- **The shape of the frontier.** The lattice side fixes the pair `(q, d)` from the window's base and then chooses its
  sub-window. That is why the twist bound must hold uniformly on `[Y, Y^A]`. The lattice side needs only arithmetic
  of the pair (`ZetaTwist.WinPair`):
  - `q ≡ 3 (mod 8)` and `d ≡ 7 (mod 16)`, in given size ranges;
  - `q` and every odd prime `p ≤ Y^{ε/5}` divide `d + 1`.

  So the frontier for `ζ`, `ZetaBalance.ZetaPairBound` (`ZetaPair`), quantifies over every such pair, as the archive's
  own window input does. It is the construction alone: every `x` of a sub-window `[Y′, Y′²]` of `[Y, Y^A]` has lattice
  data in a setting with that pair. `ZetaBalance.riemannHypothesis_of_zetaPairBound` gives RH from it. On the way, the
  three twists of a setting become the ramp errors of `χ_d`, `χ_q` and `χ_qχ_d`, as `χ_qχ_d` is primitive
  (`ZetaTwist.chiQD_isPrimitive`).
- **The modules.** Line counts include the documentation.

  | Module | Lines | Content |
  |---|---|---|
  | `PsiExplicit` | 66 | `ψ` and `θ` within `C t^{11/12+η}` of `t` at every `t ≥ 1` |
  | `ZetaThin` | 284 | the thin scales |
  | `PrimeCharSums` | 413 | sums of a character over the primes of a progression, uniformly in the modulus; the ramp error at a cutoff |
  | `MeanSquareSup` | 90 | discrete Sobolev and Markov: few members of a family are bad anywhere on an interval |
  | `TwistFamily` | 873 | the mean square over a family of primes, and a member good on the whole window |
  | `ZetaTwist` | 391 | the pair `(q, d)` with small twists on `[Y, Y^A]` |
  | `ZetaPair` | 146 | the twists as concrete characters, and RH from `ZetaBalance.ZetaPairBound` |

## Next

For `ζ`, every step above the construction is done. RH follows from `ZetaBalance.ZetaPairBound`. That frontier asks
only for the construction: lattice data on a sub-window, for every pair `(q, d)` with the archive's arithmetic.
Remaining, in order:

- **GRH.** Redo steps 3 and 4 and the analytic inputs for the cyclic family of every primitive character, with the
  weights `1/(3o + 1)`, the kept characters and the subgroups `A₀` of `ch_core` and `core_gm`. Steps 1 and 2 already
  cover every character.
- **Hermitian lattices.** Euclidean lattices with an action of `O_K` and heights averaged over the places, as the
  archive's frames use, with Bost's inequality place by place (`GramVolume`).
- **A cut with content.** Split the gain (G) into the archive's statements: vanishing at inert primes, the slopes of
  algebraic modular forms, the sizes of the auxiliary primes. Before starting on the construction itself, measure
  which of its 176 published inputs the proof reaches.
