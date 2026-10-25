/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1351–1354 of 1732

File 339 of 430: the parts `rows22310R_1351` … `rows22310R_1354` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29279 tests: row 161 columns 73–76, row 161 columns 77–80, row 161 columns
81–85, row 161 columns 86–91), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1351 : rowsJ2 161 162 73 77 ≤ 17788439741991 := by decide +kernel

theorem rows22310R_1352 : rowsJ2 161 162 77 81 ≤ 10686867591132 := by decide +kernel

theorem rows22310R_1353 : rowsJ2 161 162 81 86 ≤ 6027719358099 := by decide +kernel

theorem rows22310R_1354 : rowsJ2 161 162 86 92 ≤ 1312633284430 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1351
#print axioms SieveCert.rows22310R_1354
