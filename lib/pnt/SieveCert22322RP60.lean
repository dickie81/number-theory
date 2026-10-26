/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 229–232 of 561

File 60 of 143: the parts `rows22322R_229` … `rows22322R_232` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 25290 tests: row 87 columns 75–79, row 87 columns 80–85, row 87 columns
86–299, row 88 columns 0–47), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_229 : rowsJ2 87 88 75 80 ≤ 5219489749175 := by decide +kernel

theorem rows22322R_230 : rowsJ2 87 88 80 86 ≤ 28956601887745 := by decide +kernel

theorem rows22322R_231 : rowsJ2 87 88 86 300 ≤ 19801788206625 := by decide +kernel

theorem rows22322R_232 : rowsJ2 88 89 0 48 ≤ 775007209958361 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_229
#print axioms SieveCert.rows22322R_232
