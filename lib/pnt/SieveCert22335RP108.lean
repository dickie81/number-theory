/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 415–418 of 549

File 108 of 140: the parts `rows22335R_415` … `rows22335R_418` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 28945 tests: row 119 columns 55–62, row 119 columns 63–299, row 120 columns
0–47, row 120 columns 48–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_415 : rowsJ2 119 120 55 63 ≤ 36984955666514 := by decide +kernel

theorem rows22335R_416 : rowsJ2 119 120 63 300 ≤ 304539144743425 := by decide +kernel

theorem rows22335R_417 : rowsJ2 120 121 0 48 ≤ 190902661342440 := by decide +kernel

theorem rows22335R_418 : rowsJ2 120 121 48 55 ≤ 80417559703520 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_415
#print axioms SieveCert.rows22335R_418
