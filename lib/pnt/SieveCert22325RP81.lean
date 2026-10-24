/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 310–313 of 561

File 81 of 142: the parts `rows22325R_310` … `rows22325R_313` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 23852 tests: row 98 columns 76–83, row 98 columns 84–299, row 99 columns
0–52, row 99 columns 53–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_310 : rowsJ2 98 99 76 84 ≤ 39775826300923 := by decide +kernel

theorem rows22325R_311 : rowsJ2 98 99 84 300 ≤ 1067910677893129 := by decide +kernel

theorem rows22325R_312 : rowsJ2 99 100 0 53 ≤ 501082470730036 := by decide +kernel

theorem rows22325R_313 : rowsJ2 99 100 53 60 ≤ 1200741708440 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_310
#print axioms SieveCert.rows22325R_313
