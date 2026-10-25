/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1428–1431 of 1732

File 359 of 430: the parts `rows22310R_1428` … `rows22310R_1431` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28797 tests: row 170 columns 60–63, row 170 columns 64–67, row 170 columns
68–71, row 170 columns 72–76), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1428 : rowsJ2 170 171 60 64 ≤ 31146781019406 := by decide +kernel

theorem rows22310R_1429 : rowsJ2 170 171 64 68 ≤ 33043268817650 := by decide +kernel

theorem rows22310R_1430 : rowsJ2 170 171 68 72 ≤ 21787670580220 := by decide +kernel

theorem rows22310R_1431 : rowsJ2 170 171 72 77 ≤ 15203585912086 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1428
#print axioms SieveCert.rows22310R_1431
