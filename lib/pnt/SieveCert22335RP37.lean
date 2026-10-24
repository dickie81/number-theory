/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 140–143 of 549

File 37 of 140: the parts `rows22335R_140` … `rows22335R_143` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 26487 tests: row 74 columns 35–58, row 74 columns 59–67, row 74 columns
68–72, row 74 columns 73–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_140 : rowsJ2 74 75 35 59 ≤ 877656026967203 := by decide +kernel

theorem rows22335R_141 : rowsJ2 74 75 59 68 ≤ 65467979813295 := by decide +kernel

theorem rows22335R_142 : rowsJ2 74 75 68 73 ≤ 20079532491780 := by decide +kernel

theorem rows22335R_143 : rowsJ2 74 75 73 300 ≤ 14203017834254 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_140
#print axioms SieveCert.rows22335R_143
