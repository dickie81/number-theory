/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 122–125 of 561

File 32 of 143: the parts `rows22322R_122` … `rows22322R_125` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 26908 tests: row 70 columns 0–34, row 70 columns 35–49, row 70 columns 50–67,
row 70 columns 68–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_122 : rowsJ2 70 71 0 35 ≤ 615151605175292 := by decide +kernel

theorem rows22322R_123 : rowsJ2 70 71 35 50 ≤ 791201503829653 := by decide +kernel

theorem rows22322R_124 : rowsJ2 70 71 50 68 ≤ 378419160839823 := by decide +kernel

theorem rows22322R_125 : rowsJ2 70 71 68 300 ≤ 21376911864737 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_122
#print axioms SieveCert.rows22322R_125
