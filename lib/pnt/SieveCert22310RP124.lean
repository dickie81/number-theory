/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 491–494 of 1732

File 124 of 430: the parts `rows22310R_491` … `rows22310R_494` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26641 tests: row 104 columns 95–96, row 104 columns 97–98, row 104 columns
99–100, row 104 columns 101–102), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_491 : rowsJ2 104 105 95 97 ≤ 4946903509473 := by decide +kernel

theorem rows22310R_492 : rowsJ2 104 105 97 99 ≤ 6123463644492 := by decide +kernel

theorem rows22310R_493 : rowsJ2 104 105 99 101 ≤ 5591809650912 := by decide +kernel

theorem rows22310R_494 : rowsJ2 104 105 101 103 ≤ 5081139262653 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_491
#print axioms SieveCert.rows22310R_494
