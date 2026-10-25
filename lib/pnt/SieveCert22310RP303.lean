/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1207–1210 of 1732

File 303 of 430: the parts `rows22310R_1207` … `rows22310R_1210` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 23862 tests: row 148 columns 89–92, row 148 columns 93–97, row 148 columns
98–103, row 148 columns 104–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1207 : rowsJ2 148 149 89 93 ≤ 122031434998 := by decide +kernel

theorem rows22310R_1208 : rowsJ2 148 149 93 98 ≤ 0 := by decide +kernel

theorem rows22310R_1209 : rowsJ2 148 149 98 104 ≤ 4336638551657 := by decide +kernel

theorem rows22310R_1210 : rowsJ2 148 149 104 400 ≤ 182502462741683 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1207
#print axioms SieveCert.rows22310R_1210
