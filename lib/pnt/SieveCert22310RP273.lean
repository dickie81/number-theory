/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1089–1092 of 1732

File 273 of 430: the parts `rows22310R_1089` … `rows22310R_1092` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26070 tests: row 139 columns 98–101, row 139 columns 102–106, row 139 columns
107–399, row 140 columns 0–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1089 : rowsJ2 139 140 98 102 ≤ 438719134780 := by decide +kernel

theorem rows22310R_1090 : rowsJ2 139 140 102 107 ≤ 10764003596116 := by decide +kernel

theorem rows22310R_1091 : rowsJ2 139 140 107 400 ≤ 516647769297333 := by decide +kernel

theorem rows22310R_1092 : rowsJ2 140 141 0 58 ≤ 286712621427349 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1089
#print axioms SieveCert.rows22310R_1092
