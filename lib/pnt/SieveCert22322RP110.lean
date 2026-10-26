/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 422–425 of 561

File 110 of 143: the parts `rows22322R_422` … `rows22322R_425` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 23793 tests: row 118 columns 72–299, row 119 columns 0–47, row 119 columns
48–54, row 119 columns 55–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_422 : rowsJ2 118 119 72 300 ≤ 101482030171212 := by decide +kernel

theorem rows22322R_423 : rowsJ2 119 120 0 48 ≤ 198660526559427 := by decide +kernel

theorem rows22322R_424 : rowsJ2 119 120 48 55 ≤ 82380550127184 := by decide +kernel

theorem rows22322R_425 : rowsJ2 119 120 55 63 ≤ 43240813984445 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_422
#print axioms SieveCert.rows22322R_425
