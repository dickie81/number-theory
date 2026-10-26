/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 225–228 of 561

File 59 of 143: the parts `rows22322R_225` … `rows22322R_228` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 28079 tests: row 87 columns 43–61, row 87 columns 62–66, row 87 columns
67–70, row 87 columns 71–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_225 : rowsJ2 87 88 43 62 ≤ 115255639729330 := by decide +kernel

theorem rows22322R_226 : rowsJ2 87 88 62 67 ≤ 1561025734915 := by decide +kernel

theorem rows22322R_227 : rowsJ2 87 88 67 71 ≤ 5232323394309 := by decide +kernel

theorem rows22322R_228 : rowsJ2 87 88 71 75 ≤ 3209909841217 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_225
#print axioms SieveCert.rows22322R_228
