/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 340–343 of 561

File 89 of 142: the parts `rows22325R_340` … `rows22325R_343` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 27030 tests: row 103 columns 64–69, row 103 columns 70–76, row 103 columns
77–299, row 104 columns 0–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_340 : rowsJ2 103 104 64 70 ≤ 0 := by decide +kernel

theorem rows22325R_341 : rowsJ2 103 104 70 77 ≤ 1095364769940 := by decide +kernel

theorem rows22325R_342 : rowsJ2 103 104 77 300 ≤ 707495845353348 := by decide +kernel

theorem rows22325R_343 : rowsJ2 104 105 0 52 ≤ 403542984032213 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_340
#print axioms SieveCert.rows22325R_343
