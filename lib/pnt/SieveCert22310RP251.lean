/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1002–1005 of 1732

File 251 of 430: the parts `rows22310R_1002` … `rows22310R_1005` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29057 tests: row 133 columns 104–107, row 133 columns 108–399, row 134
columns 0–36, row 134 columns 37–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22310R_1002 : rowsJ2 133 134 104 108 ≤ 9570188536400 := by decide +kernel

theorem rows22310R_1003 : rowsJ2 133 134 108 400 ≤ 745329812090649 := by decide +kernel

theorem rows22310R_1004 : rowsJ2 134 135 0 37 ≤ 204659346224452 := by decide +kernel

theorem rows22310R_1005 : rowsJ2 134 135 37 68 ≤ 153889118568012 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1002
#print axioms SieveCert.rows22310R_1005
