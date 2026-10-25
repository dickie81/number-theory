/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 145–148 of 1732

File 36 of 430: the parts `rows22310R_145` … `rows22310R_148` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24440 tests: row 67 columns 55–58, row 67 columns 59–62, row 67 columns
63–65, row 67 columns 66–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_145 : rowsJ2 67 68 55 59 ≤ 113885261173203 := by decide +kernel

theorem rows22310R_146 : rowsJ2 67 68 59 63 ≤ 153607966877040 := by decide +kernel

theorem rows22310R_147 : rowsJ2 67 68 63 66 ≤ 138529882374197 := by decide +kernel

theorem rows22310R_148 : rowsJ2 67 68 66 400 ≤ 88703661759817 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_145
#print axioms SieveCert.rows22310R_148
