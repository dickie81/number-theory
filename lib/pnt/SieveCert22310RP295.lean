/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1175–1178 of 1732

File 295 of 430: the parts `rows22310R_1175` … `rows22310R_1178` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27483 tests: row 146 columns 71–73, row 146 columns 74–76, row 146 columns
77–79, row 146 columns 80–82), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1175 : rowsJ2 146 147 71 74 ≤ 10576645045462 := by decide +kernel

theorem rows22310R_1176 : rowsJ2 146 147 74 77 ≤ 10811238387461 := by decide +kernel

theorem rows22310R_1177 : rowsJ2 146 147 77 80 ≤ 8201640439291 := by decide +kernel

theorem rows22310R_1178 : rowsJ2 146 147 80 83 ≤ 4985680611712 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1175
#print axioms SieveCert.rows22310R_1178
