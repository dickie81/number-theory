/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1621–1625 of 1732

File 408 of 430: the parts `rows22310R_1621` … `rows22310R_1625` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (5 parts, 25386 tests: row 208 columns 40–109, row 208 columns 110–399, row 209 columns
0–39, row 209 columns 40–129, row 209 columns 130–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most
its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1621 : rowsJ2 208 209 40 110 ≤ 244912754895090 := by decide +kernel

theorem rows22310R_1622 : rowsJ2 208 209 110 400 ≤ 2121034326062590 := by decide +kernel

theorem rows22310R_1623 : rowsJ2 209 210 0 40 ≤ 37654050542619 := by decide +kernel

theorem rows22310R_1624 : rowsJ2 209 210 40 130 ≤ 1387028350756409 := by decide +kernel

theorem rows22310R_1625 : rowsJ2 209 210 130 400 ≤ 985191027319123 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1621
#print axioms SieveCert.rows22310R_1625
