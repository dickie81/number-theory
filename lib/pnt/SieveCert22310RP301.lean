/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1199–1202 of 1732

File 301 of 430: the parts `rows22310R_1199` … `rows22310R_1202` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26536 tests: row 148 columns 60–65, row 148 columns 66–69, row 148 columns
70–72, row 148 columns 73–75), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1199 : rowsJ2 148 149 60 66 ≤ 11013920387161 := by decide +kernel

theorem rows22310R_1200 : rowsJ2 148 149 66 70 ≤ 13304041460929 := by decide +kernel

theorem rows22310R_1201 : rowsJ2 148 149 70 73 ≤ 12045184890743 := by decide +kernel

theorem rows22310R_1202 : rowsJ2 148 149 73 76 ≤ 12852897585442 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1199
#print axioms SieveCert.rows22310R_1202
