/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 930–933 of 1732

File 233 of 430: the parts `rows22310R_930` … `rows22310R_933` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24547 tests: row 129 columns 84–85, row 129 columns 86–87, row 129 columns
88–89, row 129 columns 90–92), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_930 : rowsJ2 129 130 84 86 ≤ 7053606132 := by decide +kernel

theorem rows22310R_931 : rowsJ2 129 130 86 88 ≤ 0 := by decide +kernel

theorem rows22310R_932 : rowsJ2 129 130 88 90 ≤ 0 := by decide +kernel

theorem rows22310R_933 : rowsJ2 129 130 90 93 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_930
#print axioms SieveCert.rows22310R_933
