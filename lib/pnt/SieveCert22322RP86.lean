/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 330–332 of 561

File 86 of 143: the parts `rows22322R_330` … `rows22322R_332` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 22725 tests: row 101 columns 75–299, row 102 columns 0–52, row 102 columns
53–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_330 : rowsJ2 101 102 75 300 ≤ 843432764752341 := by decide +kernel

theorem rows22322R_331 : rowsJ2 102 103 0 53 ≤ 443496525684653 := by decide +kernel

theorem rows22322R_332 : rowsJ2 102 103 53 59 ≤ 7539356631080 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_330
#print axioms SieveCert.rows22322R_332
