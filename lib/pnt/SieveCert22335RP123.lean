/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 475–479 of 549

File 123 of 140: the parts `rows22335R_475` … `rows22335R_479` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (5 parts, 24588 tests: row 137 columns 42–51, row 137 columns 52–299, row 138 columns
0–41, row 138 columns 42–109, row 138 columns 110–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most
its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_475 : rowsJ2 137 138 42 52 ≤ 114001953564133 := by decide +kernel

theorem rows22335R_476 : rowsJ2 137 138 52 300 ≤ 2793108574977586 := by decide +kernel

theorem rows22335R_477 : rowsJ2 138 139 0 42 ≤ 135348411731984 := by decide +kernel

theorem rows22335R_478 : rowsJ2 138 139 42 110 ≤ 1135896368726538 := by decide +kernel

theorem rows22335R_479 : rowsJ2 138 139 110 300 ≤ 1752872197836117 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_475
#print axioms SieveCert.rows22335R_479
