/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 322–325 of 561

File 84 of 142: the parts `rows22325R_322` … `rows22325R_325` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 28843 tests: row 100 columns 65–69, row 100 columns 70–75, row 100 columns
76–299, row 101 columns 0–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_322 : rowsJ2 100 101 65 70 ≤ 0 := by decide +kernel

theorem rows22325R_323 : rowsJ2 100 101 70 76 ≤ 0 := by decide +kernel

theorem rows22325R_324 : rowsJ2 100 101 76 300 ≤ 966382496897180 := by decide +kernel

theorem rows22325R_325 : rowsJ2 101 102 0 53 ≤ 461447491158756 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_322
#print axioms SieveCert.rows22325R_325
