/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 343–346 of 549

File 89 of 140: the parts `rows22335R_343` … `rows22335R_346` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 28455 tests: row 105 columns 0–51, row 105 columns 52–57, row 105 columns
58–62, row 105 columns 63–68), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_343 : rowsJ2 105 106 0 52 ≤ 387185234896724 := by decide +kernel

theorem rows22335R_344 : rowsJ2 105 106 52 58 ≤ 20374794332253 := by decide +kernel

theorem rows22335R_345 : rowsJ2 105 106 58 63 ≤ 4395939969294 := by decide +kernel

theorem rows22335R_346 : rowsJ2 105 106 63 69 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_343
#print axioms SieveCert.rows22335R_346
