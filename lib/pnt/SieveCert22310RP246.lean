/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 982–985 of 1732

File 246 of 430: the parts `rows22310R_982` … `rows22310R_985` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27048 tests: row 132 columns 90–92, row 132 columns 93–95, row 132 columns
96–98, row 132 columns 99–101), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_982 : rowsJ2 132 133 90 93 ≤ 0 := by decide +kernel

theorem rows22310R_983 : rowsJ2 132 133 93 96 ≤ 0 := by decide +kernel

theorem rows22310R_984 : rowsJ2 132 133 96 99 ≤ 0 := by decide +kernel

theorem rows22310R_985 : rowsJ2 132 133 99 102 ≤ 313403286906 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_982
#print axioms SieveCert.rows22310R_985
