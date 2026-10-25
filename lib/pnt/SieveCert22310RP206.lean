/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 822–825 of 1732

File 206 of 430: the parts `rows22310R_822` … `rows22310R_825` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27540 tests: row 123 columns 54–74, row 123 columns 75–78, row 123 columns
79–81, row 123 columns 82–84), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_822 : rowsJ2 123 124 54 75 ≤ 72649950269728 := by decide +kernel

theorem rows22310R_823 : rowsJ2 123 124 75 79 ≤ 0 := by decide +kernel

theorem rows22310R_824 : rowsJ2 123 124 79 82 ≤ 0 := by decide +kernel

theorem rows22310R_825 : rowsJ2 123 124 82 85 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_822
#print axioms SieveCert.rows22310R_825
