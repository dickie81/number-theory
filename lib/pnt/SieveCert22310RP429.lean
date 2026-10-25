/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1724–1727 of 1732

File 429 of 430: the parts `rows22310R_1724` … `rows22310R_1727` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 23826 tests: rows 384–385, rows 386–387, rows 388–389, rows 390–391), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1724 : rows2 384 386 ≤ 18089509946708441 := by decide +kernel

theorem rows22310R_1725 : rows2 386 388 ≤ 18561969641464820 := by decide +kernel

theorem rows22310R_1726 : rows2 388 390 ≤ 19055544028755261 := by decide +kernel

theorem rows22310R_1727 : rows2 390 392 ≤ 19565769730590244 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1724
#print axioms SieveCert.rows22310R_1727
