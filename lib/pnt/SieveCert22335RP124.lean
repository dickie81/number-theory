/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 480–483 of 549

File 124 of 140: the parts `rows22335R_480` … `rows22335R_483` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29565 tests: row 139 columns 0–41, row 139 columns 42–299, row 140 columns
0–40, row 140 columns 41–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_480 : rowsJ2 139 140 0 42 ≤ 145738877855995 := by decide +kernel

theorem rows22335R_481 : rowsJ2 139 140 42 300 ≤ 2879955043594187 := by decide +kernel

theorem rows22335R_482 : rowsJ2 140 141 0 41 ≤ 135103834717112 := by decide +kernel

theorem rows22335R_483 : rowsJ2 140 141 41 300 ≤ 2892200176970416 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_480
#print axioms SieveCert.rows22335R_483
