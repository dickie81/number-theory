/-
# A bound by the search with the reversal through the largest prime, at `L = 2165/1000`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement (`flip_box_21650`): at `L = 2165/1000`, take the term of the sieve's decomposition for two primes
`p₁ > p₂`, `p₁` between `x^{0.4237}` and `x^{0.4287}` and `p₂` between `x^{0.2687}` and `x^{0.2737}`: the count
of the `n ≡ a (mod q)` in `(x, 2x]` of the form `p₁p₂m` with `m` free of primes below `p₂`. It is at least its
count in the comparison set less `(c/K + o(1))x/(φ(q) log x)`, with `c = 578145987376059`, which is
`0.000501·K`. The search of the theorem at `2165/1000` drops this term, at `0.000734·K`.

It is the first bound by the search with the reversal of a box through its largest prime
(`SieveAdFlipSearch.lean`): `SieveAd.pr_of_kidsF` at the route of `Linnik21650.lean`, on the part
`SieveAd.flipPart21650` that the kernel checks. Below this box the search decomposes by Buchstab's identity, and
bounds seven of the terms of three primes of the sign `−` by reversing them through `p₁`: the sum over the frozen
numbers `p₂p₃m` of the terms of `n/(p₂p₃m)`, searched as a tree with the tests `SieveAd.frozTests`.

The file imports `SieveAdFlipSearch.lean`, `Linnik21650.lean` and `SieveFlipPart21650.lean`.
-/
import SieveAdFlipSearch
import Linnik21650
import SieveFlipPart21650

namespace Linnik21650

open SieveCert SieveRoute SieveQ SieveAd

section

attribute [local instance] route21650 routeOK21650 ibPar21650 ibFits21650

/-- **A bound by the search with the reversal through the largest prime**, at `L = 2165/1000`: the term of the
box of the second prime between `x^{0.2687}` and `x^{0.2737}` under the first between `x^{0.4237}` and
`x^{0.4287}`, of the sign `+`, is at least `−(c/K + o(1))x/(φ(q) log x)` in `𝒜` minus the comparison set, with
`c = 578145987376059`, which is `0.000501·K`. -/
theorem flip_box_21650 :
    PR [(295487308541, 300984866680), (465911610850, 471409168989)] true 578145987376059 :=
  pr_of_kidsF sound21650 soundX21650 stratK21650 200 (cutsQ 21990232556) stratFz21650 200 4 stratFl21650 200
    flipPart21650 (by decide)

end

end Linnik21650

#print axioms Linnik21650.flip_box_21650
