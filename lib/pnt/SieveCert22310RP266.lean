/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1061–1064 of 1732

File 266 of 430: the parts `rows22310R_1061` … `rows22310R_1064` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 23149 tests: row 137 columns 101–104, row 137 columns 105–114, row 137
columns 115–399, row 138 columns 0–42), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1061 : rowsJ2 137 138 101 105 ≤ 4516215394572 := by decide +kernel

theorem rows22310R_1062 : rowsJ2 137 138 105 115 ≤ 347293905281793 := by decide +kernel

theorem rows22310R_1063 : rowsJ2 137 138 115 400 ≤ 250552612052724 := by decide +kernel

theorem rows22310R_1064 : rowsJ2 138 139 0 43 ≤ 266811781832881 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1061
#print axioms SieveCert.rows22310R_1064
