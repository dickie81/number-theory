/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 452–455 of 561

File 117 of 142: the parts `rows22325R_452` … `rows22325R_455` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 24358 tests: row 126 columns 46–52, row 126 columns 53–62, row 126 columns
63–299, row 127 columns 0–45), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_452 : rowsJ2 126 127 46 53 ≤ 96643579465024 := by decide +kernel

theorem rows22325R_453 : rowsJ2 126 127 53 63 ≤ 40871133041489 := by decide +kernel

theorem rows22325R_454 : rowsJ2 126 127 63 300 ≤ 1592526940435624 := by decide +kernel

theorem rows22325R_455 : rowsJ2 127 128 0 46 ≤ 148991761226189 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_452
#print axioms SieveCert.rows22325R_455
