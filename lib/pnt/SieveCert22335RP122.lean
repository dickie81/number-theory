/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 471–474 of 549

File 122 of 140: the parts `rows22335R_471` … `rows22335R_474` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 24024 tests: row 136 columns 0–42, row 136 columns 43–52, row 136 columns
53–299, row 137 columns 0–41), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_471 : rowsJ2 136 137 0 43 ≤ 137352170578949 := by decide +kernel

theorem rows22335R_472 : rowsJ2 136 137 43 53 ≤ 103589182889405 := by decide +kernel

theorem rows22335R_473 : rowsJ2 136 137 53 300 ≤ 2792945257314798 := by decide +kernel

theorem rows22335R_474 : rowsJ2 137 138 0 42 ≤ 126589333952452 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_471
#print axioms SieveCert.rows22335R_474
