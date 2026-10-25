/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 329–332 of 1732

File 82 of 430: the parts `rows22310R_329` … `rows22310R_332` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28854 tests: row 89 columns 44–49, row 89 columns 50–54, row 89 columns
55–60, row 89 columns 61–69), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_329 : rowsJ2 89 90 44 50 ≤ 112795263898596 := by decide +kernel

theorem rows22310R_330 : rowsJ2 89 90 50 55 ≤ 175438351265278 := by decide +kernel

theorem rows22310R_331 : rowsJ2 89 90 55 61 ≤ 204925230995183 := by decide +kernel

theorem rows22310R_332 : rowsJ2 89 90 61 70 ≤ 246342093679600 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_329
#print axioms SieveCert.rows22310R_332
