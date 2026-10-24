/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 299–302 of 561

File 78 of 142: the parts `rows22325R_299` … `rows22325R_302` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 29825 tests: row 97 columns 53–59, row 97 columns 60–64, row 97 columns
65–69, row 97 columns 70–75), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_299 : rowsJ2 97 98 53 60 ≤ 0 := by decide +kernel

theorem rows22325R_300 : rowsJ2 97 98 60 65 ≤ 0 := by decide +kernel

theorem rows22325R_301 : rowsJ2 97 98 65 70 ≤ 0 := by decide +kernel

theorem rows22325R_302 : rowsJ2 97 98 70 76 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_299
#print axioms SieveCert.rows22325R_302
