/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 153–156 of 1732

File 38 of 430: the parts `rows22310R_153` … `rows22310R_156` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25960 tests: row 68 columns 55–58, row 68 columns 59–62, row 68 columns
63–66, row 68 columns 67–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_153 : rowsJ2 68 69 55 59 ≤ 115062084253083 := by decide +kernel

theorem rows22310R_154 : rowsJ2 68 69 59 63 ≤ 156862313827192 := by decide +kernel

theorem rows22310R_155 : rowsJ2 68 69 63 67 ≤ 181377142885228 := by decide +kernel

theorem rows22310R_156 : rowsJ2 68 69 67 400 ≤ 85381270100158 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_153
#print axioms SieveCert.rows22310R_156
