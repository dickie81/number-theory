/-
# A part of the search with the reversal through the largest prime, at `L = 2165/1000`

The search of `SieveAdFlipDefs.lean` at the exponent and with the parameters of the theorem at `2165/1000`
(`SieveFill21650.lean`), and one part of it that the kernel checks. The values are those of
`tools/linnik/flip_cert.py`, which is that search in Python (`--box` prints a part).

* `stratFl21650`: the strategy of the search: `SieveAd.stratGFF` with the parameters of `strat21650`, that is,
  `strat21650` with one more cut, one unit below the largest prime's cell.
* `stratFz21650`: the strategy of the trees over the frozen parts: `SieveAd.stratFF` with chains of fewer than `3`
  primes, in cells of side at most `13194139533/DEN` (`0.012`) and at most the exponent over `10`.
* `opsFl21650`: the nodes of the search: `SieveAd.opsF` with the tests `SieveAd.fillTests`, the reversal of
  `ops21650`, and the reversal through the largest prime for boxes of at most `4` primes, its trees searched with
  the fuel `200`.
* `flipPart21650`: on the box of two primes of the sign `+`, the second prime with exponent between
  `295487308541/DEN` and `300984866680/DEN` (`0.2687` and `0.2737`) under the first between `465911610850/DEN` and
  `471409168989/DEN` (`0.4237` and `0.4287`), the search returns at most `578145987376059`, which is
  `0.000501·K`, by `decide +kernel`. It takes seven reversals through the largest prime of the nineteen it tries.
  The search of the theorem at `2165/1000` (`ops21650`, `strat21650`) drops this box, at its `dropCost`
  `845771771128570`, which is `0.000734·K`.

The file imports `SieveAdFlipStratDefs.lean` and `SieveFill21650.lean`; so it loads no more of `Mathlib` than
`Mathlib.Data.Nat.Notation`.
-/
import SieveAdFlipStratDefs
import SieveFill21650

namespace SieveAd

open SieveCert

/-- **The strategy of the search with the reversal through the largest prime at `2165/1000`.** -/
def stratFl21650 : Strat := @stratGFF ibPar21650 10 5497558139 6 549755814

/-- **The strategy of the trees over the frozen parts at `2165/1000`.** -/
def stratFz21650 : Cell → List Cell → Strat := @stratFF ibPar21650 10 13194139533 3 549755814

/-- **The nodes of the search with the reversal through the largest prime at `2165/1000`.** -/
def opsFl21650 : Ops :=
  @opsF ibPar21650 (@fillTests ibPar21650) stratK21650 200 (cutsQ 21990232556) stratFz21650 200 4

section

attribute [local instance] ibPar21650

/-- **A part of the search with the reversal through the largest prime**: on the box of the second prime between
`0.2687` and `0.2737` under the first between `0.4237` and `0.4287`, of the sign `+`, the search returns at most
`0.000501·K`. -/
theorem flipPart21650 : kids (solveG opsFl21650 fillTests stratFl21650 200) 300984866680 [(465911610850,
    471409168989)] true [] 295487308541 K ≤ 578145987376059 := by decide +kernel

end

end SieveAd

#print axioms SieveAd.flipPart21650
