/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1499–1502 of 1732

File 377 of 430: the parts `rows22310R_1499` … `rows22310R_1502` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28595 tests: row 180 columns 50–55, row 180 columns 56–59, row 180 columns
60–64, row 180 columns 65–69), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1499 : rowsJ2 180 181 50 56 ≤ 37380185350948 := by decide +kernel

theorem rows22310R_1500 : rowsJ2 180 181 56 60 ≤ 39046538412227 := by decide +kernel

theorem rows22310R_1501 : rowsJ2 180 181 60 65 ≤ 41230788621710 := by decide +kernel

theorem rows22310R_1502 : rowsJ2 180 181 65 70 ≤ 23190093668672 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1499
#print axioms SieveCert.rows22310R_1502
