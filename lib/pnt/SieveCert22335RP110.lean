/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 423–426 of 549

File 110 of 140: the parts `rows22335R_423` … `rows22335R_426` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 26310 tests: row 121 columns 55–63, row 121 columns 64–299, row 122 columns
0–46, row 122 columns 47–53), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_423 : rowsJ2 121 122 55 64 ≤ 33061627081749 := by decide +kernel

theorem rows22335R_424 : rowsJ2 121 122 64 300 ≤ 690205225108168 := by decide +kernel

theorem rows22335R_425 : rowsJ2 122 123 0 47 ≤ 170541053889958 := by decide +kernel

theorem rows22335R_426 : rowsJ2 122 123 47 54 ≤ 85121231334605 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_423
#print axioms SieveCert.rows22335R_426
