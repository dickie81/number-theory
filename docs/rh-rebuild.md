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
| 1. The top | `HalfPlaneGRH` | 211 | about 130 | Done: `HalfPlaneGRH.rhAndGRH_of_zeroFreeRightOf`, with its converse `zeroFreeRightOf_half_iff` |
| 2. Landau on windows | `WindowKernel`, `WindowPole`, `WindowNearest`, `LandauWindow`, `RampLaplace`, `WindowGRH` | about 1,600 | about 2,100 (the declarations `lemmaL` and `formB` name) | Done: `WindowGRH.rhAndGRH_of_windowBound` |
| 3. Balance | | | `ChBalance`, `ChCore`, `ChTop`, `core_gm` | Next |
| 4–6. | | | almost all of 10.7 million lines | Later |

Library line counts include the documentation; the archive has none.

**The frontier now** is `WindowGRH.WindowBound`: for every primitive `χ` and every `θ > 1/2`, the weighted error
`(WindowGRH.cyclic χ).G` is at most `C x^θ` on windows `[Y, Y^λ]` with `Y` arbitrarily large, for some `λ > 1` and
`C`. The archive's core theorem proves this in the form `HasWindows {x | Gm x ≤ x^θ} (3/2)`, which is stronger.

**What step 2 simplified against the archive.**
- Landau's theorem on windows is proved once, for any finite family of characters with positive weights. The
  weights `1/(3o + 1)` matter only for step 3.
- Real parts are taken in the transform, `(Φ(s) + conj Φ(conj s))/2`. So no symmetry of `L(s, χ)` under
  conjugation is needed, where the archive proves one in 100 lines.
- `(s − 1)ζ(s)` and `L(s, χ)` are handled by one construction, `−F'/F(s) + s·F'/F(1)` over `s(s − 1)`, continued
  across `s = 1` with Mathlib's `dslope`. For `ζ` the only extra input is Mathlib's `ζ(s) − 1/(s − 1) → γ`.
- The Taylor coefficients of the Laplace transform come from the library's `LandauLaplace`. Cauchy's estimate and
  the derivatives of `c/(s − p)` come from Mathlib.

## Next

Step 3 states the inert-prime sums and proves the balance identity and the step from the cosets to the family. That
should take elementary character sums only, and it leaves as frontier an explicit inequality about primes, the
place where the lattices enter. Before formalising it, look for the shortest form of the identity that step 4 can
still feed.
