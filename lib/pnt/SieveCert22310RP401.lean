/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1593–1596 of 1732

File 401 of 430: the parts `rows22310R_1593` … `rows22310R_1596` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24295 tests: row 199 columns 43–49, row 199 columns 50–117, row 199 columns
118–399, row 200 columns 0–42), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1593 : rowsJ2 199 200 43 50 ≤ 79100277892458 := by decide +kernel

theorem rows22310R_1594 : rowsJ2 199 200 50 118 ≤ 132062887404685 := by decide +kernel

theorem rows22310R_1595 : rowsJ2 199 200 118 400 ≤ 2078439319001185 := by decide +kernel

theorem rows22310R_1596 : rowsJ2 200 201 0 43 ≤ 34170613510785 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1593
#print axioms SieveCert.rows22310R_1596
