/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1335–1338 of 1732

File 335 of 430: the parts `rows22310R_1335` … `rows22310R_1338` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28725 tests: row 159 columns 91–399, row 160 columns 0–56, row 160 columns
57–62, row 160 columns 63–66), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1335 : rowsJ2 159 160 91 400 ≤ 170546291790168 := by decide +kernel

theorem rows22310R_1336 : rowsJ2 160 161 0 57 ≤ 119215466499681 := by decide +kernel

theorem rows22310R_1337 : rowsJ2 160 161 57 63 ≤ 19893735365356 := by decide +kernel

theorem rows22310R_1338 : rowsJ2 160 161 63 67 ≤ 22737330205135 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1335
#print axioms SieveCert.rows22310R_1338
