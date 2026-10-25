/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1476–1479 of 1732

File 371 of 430: the parts `rows22310R_1476` … `rows22310R_1479` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26995 tests: row 176 columns 71–76, row 176 columns 77–399, row 177 columns
0–51, row 177 columns 52–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1476 : rowsJ2 176 177 71 77 ≤ 13254731728556 := by decide +kernel

theorem rows22310R_1477 : rowsJ2 176 177 77 400 ≤ 1815890043169139 := by decide +kernel

theorem rows22310R_1478 : rowsJ2 177 178 0 52 ≤ 49450258576713 := by decide +kernel

theorem rows22310R_1479 : rowsJ2 177 178 52 58 ≤ 37640999941555 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1476
#print axioms SieveCert.rows22310R_1479
