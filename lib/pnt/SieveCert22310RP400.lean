/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1589–1592 of 1732

File 400 of 430: the parts `rows22310R_1589` … `rows22310R_1592` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24278 tests: row 198 columns 44–50, row 198 columns 51–118, row 198 columns
119–399, row 199 columns 0–42), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1589 : rowsJ2 198 199 44 51 ≤ 81069607018357 := by decide +kernel

theorem rows22310R_1590 : rowsJ2 198 199 51 119 ≤ 126082419800858 := by decide +kernel

theorem rows22310R_1591 : rowsJ2 198 199 119 400 ≤ 2066717315904699 := by decide +kernel

theorem rows22310R_1592 : rowsJ2 199 200 0 43 ≤ 30967092801231 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1589
#print axioms SieveCert.rows22310R_1592
