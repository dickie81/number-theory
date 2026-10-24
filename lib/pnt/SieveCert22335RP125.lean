/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 484–487 of 549

File 125 of 140: the parts `rows22335R_484` … `rows22335R_487` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 27390 tests: row 141 columns 0–40, row 141 columns 41–299, row 142 columns
0–40, row 142 columns 41–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_484 : rowsJ2 141 142 0 41 ≤ 146683879387371 := by decide +kernel

theorem rows22335R_485 : rowsJ2 141 142 41 300 ≤ 2874691570644025 := by decide +kernel

theorem rows22335R_486 : rowsJ2 142 143 0 41 ≤ 157237884912117 := by decide +kernel

theorem rows22335R_487 : rowsJ2 142 143 41 300 ≤ 2869193428653280 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_484
#print axioms SieveCert.rows22335R_487
