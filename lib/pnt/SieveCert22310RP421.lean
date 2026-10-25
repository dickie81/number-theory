/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1682–1687 of 1732

File 421 of 430: the parts `rows22310R_1682` … `rows22310R_1687` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (6 parts, 26004 tests: rows 266–266, rows 267–267, rows 268–268, rows 269–269, rows
270–270, rows 271–271), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1682 : rows2 266 267 ≤ 6630329265477345 := by decide +kernel

theorem rows22310R_1683 : rows2 267 268 ≤ 6684706886582132 := by decide +kernel

theorem rows22310R_1684 : rows2 268 269 ≤ 6777128767848932 := by decide +kernel

theorem rows22310R_1685 : rows2 269 270 ≤ 6834130196826070 := by decide +kernel

theorem rows22310R_1686 : rows2 270 271 ≤ 6929284070982105 := by decide +kernel

theorem rows22310R_1687 : rows2 271 272 ≤ 6989078573717658 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1682
#print axioms SieveCert.rows22310R_1687
