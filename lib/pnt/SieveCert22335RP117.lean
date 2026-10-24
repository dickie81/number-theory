/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 450–453 of 549

File 117 of 140: the parts `rows22335R_450` … `rows22335R_453` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29095 tests: row 129 columns 0–44, row 129 columns 45–52, row 129 columns
53–299, row 130 columns 0–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_450 : rowsJ2 129 130 0 45 ≤ 136692117215782 := by decide +kernel

theorem rows22335R_451 : rowsJ2 129 130 45 53 ≤ 98364588587703 := by decide +kernel

theorem rows22335R_452 : rowsJ2 129 130 53 300 ≤ 2080888161832876 := by decide +kernel

theorem rows22335R_453 : rowsJ2 130 131 0 45 ≤ 138629618691434 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_450
#print axioms SieveCert.rows22335R_453
