/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 518–521 of 1732

File 131 of 430: the parts `rows22310R_518` … `rows22310R_521` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24241 tests: row 106 columns 90–91, row 106 columns 92–93, row 106 columns
94–95, row 106 columns 96–97), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_518 : rowsJ2 106 107 90 92 ≤ 1655667659263 := by decide +kernel

theorem rows22310R_519 : rowsJ2 106 107 92 94 ≤ 2742703734006 := by decide +kernel

theorem rows22310R_520 : rowsJ2 106 107 94 96 ≤ 4101782226241 := by decide +kernel

theorem rows22310R_521 : rowsJ2 106 107 96 98 ≤ 5167835085536 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_518
#print axioms SieveCert.rows22310R_521
