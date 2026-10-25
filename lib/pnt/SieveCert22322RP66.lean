/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 253–256 of 561

File 66 of 143: the parts `rows22322R_253` … `rows22322R_256` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 24897 tests: row 90 columns 75–79, row 90 columns 80–85, row 90 columns
86–299, row 91 columns 0–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_253 : rowsJ2 90 91 75 80 ≤ 4927250280310 := by decide +kernel

theorem rows22322R_254 : rowsJ2 90 91 80 86 ≤ 35442346610582 := by decide +kernel

theorem rows22322R_255 : rowsJ2 90 91 86 300 ≤ 350205563769742 := by decide +kernel

theorem rows22322R_256 : rowsJ2 91 92 0 53 ≤ 707378422252138 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_253
#print axioms SieveCert.rows22322R_256
