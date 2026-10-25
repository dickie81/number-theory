/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 445–448 of 1732

File 112 of 430: the parts `rows22310R_445` … `rows22310R_448` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29262 tests: row 101 columns 51–60, row 101 columns 61–79, row 101 columns
80–85, row 101 columns 86–89), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_445 : rowsJ2 101 102 51 61 ≤ 256847186814112 := by decide +kernel

theorem rows22310R_446 : rowsJ2 101 102 61 80 ≤ 255760088639751 := by decide +kernel

theorem rows22310R_447 : rowsJ2 101 102 80 86 ≤ 28194243857834 := by decide +kernel

theorem rows22310R_448 : rowsJ2 101 102 86 90 ≤ 9389686760612 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_445
#print axioms SieveCert.rows22310R_448
