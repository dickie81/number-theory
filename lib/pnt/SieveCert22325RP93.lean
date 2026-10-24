/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 356–359 of 561

File 93 of 142: the parts `rows22325R_356` … `rows22325R_359` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 29001 tests: row 106 columns 52–57, row 106 columns 58–62, row 106 columns
63–68, row 106 columns 69–76), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_356 : rowsJ2 106 107 52 58 ≤ 24382128879918 := by decide +kernel

theorem rows22325R_357 : rowsJ2 106 107 58 63 ≤ 7406323526790 := by decide +kernel

theorem rows22325R_358 : rowsJ2 106 107 63 69 ≤ 0 := by decide +kernel

theorem rows22325R_359 : rowsJ2 106 107 69 77 ≤ 1275468496419 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_356
#print axioms SieveCert.rows22325R_359
