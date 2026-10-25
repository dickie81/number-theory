/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1688–1693 of 1732

File 422 of 430: the parts `rows22310R_1688` … `rows22310R_1693` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (6 parts, 27311 tests: rows 272–272, rows 273–273, rows 274–274, rows 275–275, rows
276–276, rows 277–277), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22310R_1688 : rows2 272 273 ≤ 7087142845513591 := by decide +kernel

theorem rows22310R_1689 : rows2 273 274 ≤ 7149913913128693 := by decide +kernel

theorem rows22310R_1690 : rows2 274 275 ≤ 7251081936178651 := by decide +kernel

theorem rows22310R_1691 : rows2 275 276 ≤ 7317028787627679 := by decide +kernel

theorem rows22310R_1692 : rows2 276 277 ≤ 7281499443834384 := by decide +kernel

theorem rows22310R_1693 : rows2 277 278 ≤ 7348199357809102 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1688
#print axioms SieveCert.rows22310R_1693
