/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1597–1599 of 1732

File 402 of 430: the parts `rows22310R_1597` … `rows22310R_1599` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 23451 tests: row 200 columns 43–49, row 200 columns 50–399, row 201 columns
0–42), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1597 : rowsJ2 200 201 43 50 ≤ 83932612419496 := by decide +kernel

theorem rows22310R_1598 : rowsJ2 200 201 50 400 ≤ 2214411558419826 := by decide +kernel

theorem rows22310R_1599 : rowsJ2 201 202 0 43 ≤ 37624061503280 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1597
#print axioms SieveCert.rows22310R_1599
