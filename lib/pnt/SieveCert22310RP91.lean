/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 364–367 of 1732

File 91 of 430: the parts `rows22310R_364` … `rows22310R_367` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28740 tests: row 93 columns 56–63, row 93 columns 64–79, row 93 columns
80–87, row 93 columns 88–91), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_364 : rowsJ2 93 94 56 64 ≤ 231267125692621 := by decide +kernel

theorem rows22310R_365 : rowsJ2 93 94 64 80 ≤ 295128813307059 := by decide +kernel

theorem rows22310R_366 : rowsJ2 93 94 80 88 ≤ 73792017621359 := by decide +kernel

theorem rows22310R_367 : rowsJ2 93 94 88 92 ≤ 23697769877911 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_364
#print axioms SieveCert.rows22310R_367
