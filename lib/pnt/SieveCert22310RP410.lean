/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1630–1633 of 1732

File 410 of 430: the parts `rows22310R_1630` … `rows22310R_1633` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26719 tests: row 212 columns 0–38, row 212 columns 39–399, row 213 columns
0–38, row 213 columns 39–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1630 : rowsJ2 212 213 0 39 ≤ 38940299686719 := by decide +kernel

theorem rows22310R_1631 : rowsJ2 212 213 39 400 ≤ 2590518025205396 := by decide +kernel

theorem rows22310R_1632 : rowsJ2 213 214 0 39 ≤ 42913275989931 := by decide +kernel

theorem rows22310R_1633 : rowsJ2 213 214 39 400 ≤ 2669110165576076 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1630
#print axioms SieveCert.rows22310R_1633
