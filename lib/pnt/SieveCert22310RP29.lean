/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 116–119 of 1732

File 29 of 430: the parts `rows22310R_116` … `rows22310R_119` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24270 tests: row 63 columns 55–58, row 63 columns 59–62, row 63 columns
63–399, row 64 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_116 : rowsJ2 63 64 55 59 ≤ 113180425016150 := by decide +kernel

theorem rows22310R_117 : rowsJ2 63 64 59 63 ≤ 144470831159129 := by decide +kernel

theorem rows22310R_118 : rowsJ2 63 64 63 400 ≤ 42453017574247 := by decide +kernel

theorem rows22310R_119 : rowsJ2 64 65 0 35 ≤ 1089613932307260 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_116
#print axioms SieveCert.rows22310R_119
