/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1343–1346 of 1732

File 337 of 430: the parts `rows22310R_1343` … `rows22310R_1346` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27371 tests: row 160 columns 81–85, row 160 columns 86–91, row 160 columns
92–399, row 161 columns 0–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1343 : rowsJ2 160 161 81 86 ≤ 6590705495298 := by decide +kernel

theorem rows22310R_1344 : rowsJ2 160 161 86 92 ≤ 1595410111366 := by decide +kernel

theorem rows22310R_1345 : rowsJ2 160 161 92 400 ≤ 281987045776902 := by decide +kernel

theorem rows22310R_1346 : rowsJ2 161 162 0 57 ≤ 113528806451314 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1343
#print axioms SieveCert.rows22310R_1346
