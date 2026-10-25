/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1511–1514 of 1732

File 380 of 430: the parts `rows22310R_1511` … `rows22310R_1514` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29043 tests: row 182 columns 50–55, row 182 columns 56–59, row 182 columns
60–64, row 182 columns 65–70), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1511 : rowsJ2 182 183 50 56 ≤ 42625752525675 := by decide +kernel

theorem rows22310R_1512 : rowsJ2 182 183 56 60 ≤ 41636329863136 := by decide +kernel

theorem rows22310R_1513 : rowsJ2 182 183 60 65 ≤ 38290893888100 := by decide +kernel

theorem rows22310R_1514 : rowsJ2 182 183 65 71 ≤ 23432488436485 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1511
#print axioms SieveCert.rows22310R_1514
