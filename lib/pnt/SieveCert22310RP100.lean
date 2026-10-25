/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 399–402 of 1732

File 100 of 430: the parts `rows22310R_399` … `rows22310R_402` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29886 tests: row 97 columns 44–49, row 97 columns 50–56, row 97 columns
57–68, row 97 columns 69–84), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_399 : rowsJ2 97 98 44 50 ≤ 169809795200870 := by decide +kernel

theorem rows22310R_400 : rowsJ2 97 98 50 57 ≤ 220451333489552 := by decide +kernel

theorem rows22310R_401 : rowsJ2 97 98 57 69 ≤ 273481673019725 := by decide +kernel

theorem rows22310R_402 : rowsJ2 97 98 69 85 ≤ 183386786265019 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_399
#print axioms SieveCert.rows22310R_402
