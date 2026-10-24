/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 285–288 of 549

File 74 of 140: the parts `rows22335R_285` … `rows22335R_288` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 24293 tests: row 95 columns 84–299, row 96 columns 0–52, row 96 columns
53–59, row 96 columns 60–64), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_285 : rowsJ2 95 96 84 300 ≤ 1282574708461909 := by decide +kernel

theorem rows22335R_286 : rowsJ2 96 97 0 53 ≤ 564897221770055 := by decide +kernel

theorem rows22335R_287 : rowsJ2 96 97 53 60 ≤ 0 := by decide +kernel

theorem rows22335R_288 : rowsJ2 96 97 60 65 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_285
#print axioms SieveCert.rows22335R_288
