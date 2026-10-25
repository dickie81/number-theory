/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 213–216 of 1732

File 53 of 430: the parts `rows22310R_213` … `rows22310R_216` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24470 tests: row 75 columns 59–62, row 75 columns 63–67, row 75 columns
68–73, row 75 columns 74–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_213 : rowsJ2 75 76 59 63 ≤ 169212112417728 := by decide +kernel

theorem rows22310R_214 : rowsJ2 75 76 63 68 ≤ 195659910186907 := by decide +kernel

theorem rows22310R_215 : rowsJ2 75 76 68 74 ≤ 207234774477775 := by decide +kernel

theorem rows22310R_216 : rowsJ2 75 76 74 400 ≤ 62229409940598 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_213
#print axioms SieveCert.rows22310R_216
