/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1712–1715 of 1732

File 426 of 430: the parts `rows22310R_1712` … `rows22310R_1715` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29809 tests: rows 298–299, rows 300–301, rows 302–303, rows 304–305), each a
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

theorem rows22310R_1712 : rows2 298 300 ≤ 15290810449566138 := by decide +kernel

theorem rows22310R_1713 : rows2 300 302 ≤ 15350127668939818 := by decide +kernel

theorem rows22310R_1714 : rows2 302 304 ≤ 15413442829337993 := by decide +kernel

theorem rows22310R_1715 : rows2 304 306 ≤ 15475460942671690 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1712
#print axioms SieveCert.rows22310R_1715
