/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1219–1222 of 1732

File 306 of 430: the parts `rows22310R_1219` … `rows22310R_1222` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29592 tests: row 149 columns 85–88, row 149 columns 89–92, row 149 columns
93–97, row 149 columns 98–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1219 : rowsJ2 149 150 85 89 ≤ 2615640233598 := by decide +kernel

theorem rows22310R_1220 : rowsJ2 149 150 89 93 ≤ 337496924009 := by decide +kernel

theorem rows22310R_1221 : rowsJ2 149 150 93 98 ≤ 0 := by decide +kernel

theorem rows22310R_1222 : rowsJ2 149 150 98 400 ≤ 184158540246910 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1219
#print axioms SieveCert.rows22310R_1222
