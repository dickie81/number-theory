/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 245–248 of 561

File 64 of 143: the parts `rows22322R_245` … `rows22322R_248` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 23679 tests: row 89 columns 76–80, row 89 columns 81–86, row 89 columns
87–299, row 90 columns 0–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_245 : rowsJ2 89 90 76 81 ≤ 7469192492001 := by decide +kernel

theorem rows22322R_246 : rowsJ2 89 90 81 87 ≤ 40696632013916 := by decide +kernel

theorem rows22322R_247 : rowsJ2 89 90 87 300 ≤ 207402158220580 := by decide +kernel

theorem rows22322R_248 : rowsJ2 90 91 0 52 ≤ 736606324610935 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_245
#print axioms SieveCert.rows22322R_248
