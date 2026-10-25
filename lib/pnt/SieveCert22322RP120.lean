/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 462–465 of 561

File 120 of 143: the parts `rows22322R_462` … `rows22322R_465` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 29695 tests: row 129 columns 0–44, row 129 columns 45–52, row 129 columns
53–299, row 130 columns 0–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_462 : rowsJ2 129 130 0 45 ≤ 137249166266585 := by decide +kernel

theorem rows22322R_463 : rowsJ2 129 130 45 53 ≤ 107971433685143 := by decide +kernel

theorem rows22322R_464 : rowsJ2 129 130 53 300 ≤ 2089697275732618 := by decide +kernel

theorem rows22322R_465 : rowsJ2 130 131 0 45 ≤ 139102666805006 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_462
#print axioms SieveCert.rows22322R_465
