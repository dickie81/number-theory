/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1034–1037 of 1732

File 259 of 430: the parts `rows22310R_1034` … `rows22310R_1037` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29804 tests: row 136 columns 0–38, row 136 columns 39–67, row 136 columns
68–72, row 136 columns 73–76), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1034 : rowsJ2 136 137 0 39 ≤ 233689870082561 := by decide +kernel

theorem rows22310R_1035 : rowsJ2 136 137 39 68 ≤ 102288793535141 := by decide +kernel

theorem rows22310R_1036 : rowsJ2 136 137 68 73 ≤ 5539423022948 := by decide +kernel

theorem rows22310R_1037 : rowsJ2 136 137 73 77 ≤ 3035435145497 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1034
#print axioms SieveCert.rows22310R_1037
