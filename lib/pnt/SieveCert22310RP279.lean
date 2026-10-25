/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1113–1116 of 1732

File 279 of 430: the parts `rows22310R_1113` … `rows22310R_1116` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27209 tests: row 141 columns 84–86, row 141 columns 87–89, row 141 columns
90–92, row 141 columns 93–96), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1113 : rowsJ2 141 142 84 87 ≤ 0 := by decide +kernel

theorem rows22310R_1114 : rowsJ2 141 142 87 90 ≤ 0 := by decide +kernel

theorem rows22310R_1115 : rowsJ2 141 142 90 93 ≤ 0 := by decide +kernel

theorem rows22310R_1116 : rowsJ2 141 142 93 97 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1113
#print axioms SieveCert.rows22310R_1116
