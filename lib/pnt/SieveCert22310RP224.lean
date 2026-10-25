/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 894–897 of 1732

File 224 of 430: the parts `rows22310R_894` … `rows22310R_897` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25252 tests: row 127 columns 78–80, row 127 columns 81–83, row 127 columns
84–85, row 127 columns 86–87), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_894 : rowsJ2 127 128 78 81 ≤ 0 := by decide +kernel

theorem rows22310R_895 : rowsJ2 127 128 81 84 ≤ 0 := by decide +kernel

theorem rows22310R_896 : rowsJ2 127 128 84 86 ≤ 28369885469 := by decide +kernel

theorem rows22310R_897 : rowsJ2 127 128 86 88 ≤ 71157304882 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_894
#print axioms SieveCert.rows22310R_897
