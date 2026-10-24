/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 432–435 of 561

File 112 of 142: the parts `rows22325R_432` … `rows22325R_435` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 27258 tests: row 121 columns 48–54, row 121 columns 55–62, row 121 columns
63–299, row 122 columns 0–46), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_432 : rowsJ2 121 122 48 55 ≤ 86634966488310 := by decide +kernel

theorem rows22325R_433 : rowsJ2 121 122 55 63 ≤ 38700941399397 := by decide +kernel

theorem rows22325R_434 : rowsJ2 121 122 63 300 ≤ 692656696294935 := by decide +kernel

theorem rows22325R_435 : rowsJ2 122 123 0 47 ≤ 170732204511940 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_432
#print axioms SieveCert.rows22325R_435
