/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1042–1045 of 1732

File 261 of 430: the parts `rows22310R_1042` … `rows22310R_1045` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27807 tests: row 136 columns 88–90, row 136 columns 91–93, row 136 columns
94–96, row 136 columns 97–100), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1042 : rowsJ2 136 137 88 91 ≤ 0 := by decide +kernel

theorem rows22310R_1043 : rowsJ2 136 137 91 94 ≤ 0 := by decide +kernel

theorem rows22310R_1044 : rowsJ2 136 137 94 97 ≤ 0 := by decide +kernel

theorem rows22310R_1045 : rowsJ2 136 137 97 101 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1042
#print axioms SieveCert.rows22310R_1045
