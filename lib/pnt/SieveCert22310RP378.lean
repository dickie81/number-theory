/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1503–1506 of 1732

File 378 of 430: the parts `rows22310R_1503` … `rows22310R_1506` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28661 tests: row 180 columns 70–399, row 181 columns 0–49, row 181 columns
50–55, row 181 columns 56–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1503 : rowsJ2 180 181 70 400 ≤ 2105320046703383 := by decide +kernel

theorem rows22310R_1504 : rowsJ2 181 182 0 50 ≤ 39069827821560 := by decide +kernel

theorem rows22310R_1505 : rowsJ2 181 182 50 56 ≤ 39982073703726 := by decide +kernel

theorem rows22310R_1506 : rowsJ2 181 182 56 60 ≤ 40332552930609 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1503
#print axioms SieveCert.rows22310R_1506
