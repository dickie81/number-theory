/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 483–486 of 561

File 125 of 143: the parts `rows22322R_483` … `rows22322R_486` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 24486 tests: row 136 columns 0–42, row 136 columns 43–52, row 136 columns
53–299, row 137 columns 0–41), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_483 : rowsJ2 136 137 0 43 ≤ 137073402276937 := by decide +kernel

theorem rows22322R_484 : rowsJ2 136 137 43 53 ≤ 119743639139350 := by decide +kernel

theorem rows22322R_485 : rowsJ2 136 137 53 300 ≤ 2871932596570792 := by decide +kernel

theorem rows22322R_486 : rowsJ2 137 138 0 42 ≤ 126077364766262 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_483
#print axioms SieveCert.rows22322R_486
