/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1244–1247 of 1732

File 312 of 430: the parts `rows22310R_1244` … `rows22310R_1247` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26707 tests: row 151 columns 85–88, row 151 columns 89–93, row 151 columns
94–98, row 151 columns 99–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1244 : rowsJ2 151 152 85 89 ≤ 3211933748969 := by decide +kernel

theorem rows22310R_1245 : rowsJ2 151 152 89 94 ≤ 846595718942 := by decide +kernel

theorem rows22310R_1246 : rowsJ2 151 152 94 99 ≤ 0 := by decide +kernel

theorem rows22310R_1247 : rowsJ2 151 152 99 400 ≤ 122221507135734 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1244
#print axioms SieveCert.rows22310R_1247
