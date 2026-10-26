/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 402–405 of 561

File 105 of 143: the parts `rows22322R_402` … `rows22322R_405` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 25701 tests: row 114 columns 70–299, row 115 columns 0–48, row 115 columns
49–54, row 115 columns 55–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_402 : rowsJ2 114 115 70 300 ≤ 1758276213413 := by decide +kernel

theorem rows22322R_403 : rowsJ2 115 116 0 49 ≤ 240019716177693 := by decide +kernel

theorem rows22322R_404 : rowsJ2 115 116 49 55 ≤ 59272218883703 := by decide +kernel

theorem rows22322R_405 : rowsJ2 115 116 55 61 ≤ 39890099170175 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_402
#print axioms SieveCert.rows22322R_405
