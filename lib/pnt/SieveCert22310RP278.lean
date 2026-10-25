/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1109–1112 of 1732

File 278 of 430: the parts `rows22310R_1109` … `rows22310R_1112` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28096 tests: row 141 columns 72–74, row 141 columns 75–77, row 141 columns
78–80, row 141 columns 81–83), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1109 : rowsJ2 141 142 72 75 ≤ 6490121882987 := by decide +kernel

theorem rows22310R_1110 : rowsJ2 141 142 75 78 ≤ 5720691991539 := by decide +kernel

theorem rows22310R_1111 : rowsJ2 141 142 78 81 ≤ 3756622719069 := by decide +kernel

theorem rows22310R_1112 : rowsJ2 141 142 81 84 ≤ 868517408581 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1109
#print axioms SieveCert.rows22310R_1112
