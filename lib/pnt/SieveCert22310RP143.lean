/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 566–569 of 1732

File 143 of 430: the parts `rows22310R_566` … `rows22310R_569` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25527 tests: row 109 columns 87–89, row 109 columns 90–91, row 109 columns
92–93, row 109 columns 94–95), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_566 : rowsJ2 109 110 87 90 ≤ 1017156055429 := by decide +kernel

theorem rows22310R_567 : rowsJ2 109 110 90 92 ≤ 1623523049504 := by decide +kernel

theorem rows22310R_568 : rowsJ2 109 110 92 94 ≤ 2690172129123 := by decide +kernel

theorem rows22310R_569 : rowsJ2 109 110 94 96 ≤ 3780838461071 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_566
#print axioms SieveCert.rows22310R_569
