/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 257–260 of 1732

File 64 of 430: the parts `rows22310R_257` … `rows22310R_260` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29033 tests: row 80 columns 55–58, row 80 columns 59–63, row 80 columns
64–69, row 80 columns 70–78), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_257 : rowsJ2 80 81 55 59 ≤ 156043105802506 := by decide +kernel

theorem rows22310R_258 : rowsJ2 80 81 59 64 ≤ 192325255433522 := by decide +kernel

theorem rows22310R_259 : rowsJ2 80 81 64 70 ≤ 202618181235265 := by decide +kernel

theorem rows22310R_260 : rowsJ2 80 81 70 79 ≤ 244569979264101 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_257
#print axioms SieveCert.rows22310R_260
