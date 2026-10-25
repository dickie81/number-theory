/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1101–1104 of 1732

File 276 of 430: the parts `rows22310R_1101` … `rows22310R_1104` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28704 tests: row 140 columns 90–92, row 140 columns 93–96, row 140 columns
97–100, row 140 columns 101–105), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1101 : rowsJ2 140 141 90 93 ≤ 0 := by decide +kernel

theorem rows22310R_1102 : rowsJ2 140 141 93 97 ≤ 0 := by decide +kernel

theorem rows22310R_1103 : rowsJ2 140 141 97 101 ≤ 0 := by decide +kernel

theorem rows22310R_1104 : rowsJ2 140 141 101 106 ≤ 8122139226598 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1101
#print axioms SieveCert.rows22310R_1104
