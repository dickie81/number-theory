/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 507–510 of 1732

File 128 of 430: the parts `rows22310R_507` … `rows22310R_510` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 22379 tests: row 105 columns 99–100, row 105 columns 101–102, row 105 columns
103–104, row 105 columns 105–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_507 : rowsJ2 105 106 99 101 ≤ 4999849771472 := by decide +kernel

theorem rows22310R_508 : rowsJ2 105 106 101 103 ≤ 4514960157277 := by decide +kernel

theorem rows22310R_509 : rowsJ2 105 106 103 105 ≤ 4088029557698 := by decide +kernel

theorem rows22310R_510 : rowsJ2 105 106 105 400 ≤ 1971088734555 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_507
#print axioms SieveCert.rows22310R_510
