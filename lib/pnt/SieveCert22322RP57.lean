/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 217–220 of 561

File 57 of 143: the parts `rows22322R_217` … `rows22322R_220` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 28173 tests: row 86 columns 40–61, row 86 columns 62–66, row 86 columns
67–70, row 86 columns 71–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_217 : rowsJ2 86 87 40 62 ≤ 207001597101949 := by decide +kernel

theorem rows22322R_218 : rowsJ2 86 87 62 67 ≤ 1574645621626 := by decide +kernel

theorem rows22322R_219 : rowsJ2 86 87 67 71 ≤ 6370047745951 := by decide +kernel

theorem rows22322R_220 : rowsJ2 86 87 71 75 ≤ 4421729178977 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_217
#print axioms SieveCert.rows22322R_220
