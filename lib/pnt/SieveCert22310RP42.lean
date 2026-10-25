/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 169–172 of 1732

File 42 of 430: the parts `rows22310R_169` … `rows22310R_172` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28364 tests: row 70 columns 55–58, row 70 columns 59–62, row 70 columns
63–66, row 70 columns 67–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_169 : rowsJ2 70 71 55 59 ≤ 118636670594912 := by decide +kernel

theorem rows22310R_170 : rowsJ2 70 71 59 63 ≤ 164364209568266 := by decide +kernel

theorem rows22310R_171 : rowsJ2 70 71 63 67 ≤ 174167502223487 := by decide +kernel

theorem rows22310R_172 : rowsJ2 70 71 67 400 ≤ 161169107893946 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_169
#print axioms SieveCert.rows22310R_172
