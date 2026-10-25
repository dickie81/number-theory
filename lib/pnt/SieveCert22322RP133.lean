/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 519–523 of 561

File 133 of 143: the parts `rows22322R_519` … `rows22322R_523` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (5 parts, 24366 tests: row 152 columns 85–299, row 153 columns 0–95, row 153 columns
96–299, rows 154–154, rows 155–155), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_519 : rowsJ2 152 153 85 300 ≤ 2900519662348350 := by decide +kernel

theorem rows22322R_520 : rowsJ2 153 154 0 96 ≤ 1495648396088551 := by decide +kernel

theorem rows22322R_521 : rowsJ2 153 154 96 300 ≤ 1767870635999725 := by decide +kernel

theorem rows22322R_522 : rows2 154 155 ≤ 3279629020725318 := by decide +kernel

theorem rows22322R_523 : rows2 155 156 ≤ 3294666764272752 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_519
#print axioms SieveCert.rows22322R_523
