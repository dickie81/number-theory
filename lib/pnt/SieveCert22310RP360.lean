/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1432–1435 of 1732

File 360 of 430: the parts `rows22310R_1432` … `rows22310R_1435` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25257 tests: row 170 columns 77–82, row 170 columns 83–399, row 171 columns
0–53, row 171 columns 54–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1432 : rowsJ2 170 171 77 83 ≤ 6531973993960 := by decide +kernel

theorem rows22310R_1433 : rowsJ2 170 171 83 400 ≤ 1301755719022640 := by decide +kernel

theorem rows22310R_1434 : rowsJ2 171 172 0 54 ≤ 66757098748101 := by decide +kernel

theorem rows22310R_1435 : rowsJ2 171 172 54 59 ≤ 24468497789761 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1432
#print axioms SieveCert.rows22310R_1435
