/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1394–1396 of 1732

File 350 of 430: the parts `rows22310R_1394` … `rows22310R_1396` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 22646 tests: row 166 columns 55–60, row 166 columns 61–64, row 166 columns
65–68), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22310R_1394 : rowsJ2 166 167 55 61 ≤ 24421691913696 := by decide +kernel

theorem rows22310R_1395 : rowsJ2 166 167 61 65 ≤ 27054728142581 := by decide +kernel

theorem rows22310R_1396 : rowsJ2 166 167 65 69 ≤ 32727726394250 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1394
#print axioms SieveCert.rows22310R_1396
