/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1523–1525 of 1732

File 383 of 430: the parts `rows22310R_1523` … `rows22310R_1525` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 22284 tests: row 184 columns 49–54, row 184 columns 55–59, row 184 columns
60–64), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22310R_1523 : rowsJ2 184 185 49 55 ≤ 43968993238648 := by decide +kernel

theorem rows22310R_1524 : rowsJ2 184 185 55 60 ≤ 52555628756725 := by decide +kernel

theorem rows22310R_1525 : rowsJ2 184 185 60 65 ≤ 35395860541140 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1523
#print axioms SieveCert.rows22310R_1525
