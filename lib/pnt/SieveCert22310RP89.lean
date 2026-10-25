/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 356–359 of 1732

File 89 of 430: the parts `rows22310R_356` … `rows22310R_359` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 23154 tests: row 92 columns 64–77, row 92 columns 78–87, row 92 columns
88–91, row 92 columns 92–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_356 : rowsJ2 92 93 64 78 ≤ 280976165453858 := by decide +kernel

theorem rows22310R_357 : rowsJ2 92 93 78 88 ≤ 106471907722436 := by decide +kernel

theorem rows22310R_358 : rowsJ2 92 93 88 92 ≤ 26146044421098 := by decide +kernel

theorem rows22310R_359 : rowsJ2 92 93 92 400 ≤ 5681437016696 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_356
#print axioms SieveCert.rows22310R_359
