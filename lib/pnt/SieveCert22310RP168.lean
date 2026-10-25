/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 667–670 of 1732

File 168 of 430: the parts `rows22310R_667` … `rows22310R_670` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29959 tests: row 115 columns 0–34, row 115 columns 35–44, row 115 columns
45–70, row 115 columns 71–78), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_667 : rowsJ2 115 116 0 35 ≤ 94969816730301 := by decide +kernel

theorem rows22310R_668 : rowsJ2 115 116 35 45 ≤ 233848835765438 := by decide +kernel

theorem rows22310R_669 : rowsJ2 115 116 45 71 ≤ 335298287926558 := by decide +kernel

theorem rows22310R_670 : rowsJ2 115 116 71 79 ≤ 13617831460293 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_667
#print axioms SieveCert.rows22310R_670
