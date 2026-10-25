/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1069–1072 of 1732

File 268 of 430: the parts `rows22310R_1069` … `rows22310R_1072` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29645 tests: row 138 columns 79–81, row 138 columns 82–84, row 138 columns
85–87, row 138 columns 88–90), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1069 : rowsJ2 138 139 79 82 ≤ 316300147158 := by decide +kernel

theorem rows22310R_1070 : rowsJ2 138 139 82 85 ≤ 0 := by decide +kernel

theorem rows22310R_1071 : rowsJ2 138 139 85 88 ≤ 0 := by decide +kernel

theorem rows22310R_1072 : rowsJ2 138 139 88 91 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1069
#print axioms SieveCert.rows22310R_1072
