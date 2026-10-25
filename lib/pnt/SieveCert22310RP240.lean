/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 958–961 of 1732

File 240 of 430: the parts `rows22310R_958` … `rows22310R_961` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28860 tests: row 131 columns 36–67, row 131 columns 68–73, row 131 columns
74–77, row 131 columns 78–80), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_958 : rowsJ2 131 132 36 68 ≤ 217792395738193 := by decide +kernel

theorem rows22310R_959 : rowsJ2 131 132 68 74 ≤ 1698619006475 := by decide +kernel

theorem rows22310R_960 : rowsJ2 131 132 74 78 ≤ 0 := by decide +kernel

theorem rows22310R_961 : rowsJ2 131 132 78 81 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_958
#print axioms SieveCert.rows22310R_961
