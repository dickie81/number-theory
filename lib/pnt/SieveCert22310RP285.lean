/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1136–1139 of 1732

File 285 of 430: the parts `rows22310R_1136` … `rows22310R_1139` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27593 tests: row 143 columns 71–73, row 143 columns 74–76, row 143 columns
77–79, row 143 columns 80–82), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1136 : rowsJ2 143 144 71 74 ≤ 8067765346036 := by decide +kernel

theorem rows22310R_1137 : rowsJ2 143 144 74 77 ≤ 7889121320929 := by decide +kernel

theorem rows22310R_1138 : rowsJ2 143 144 77 80 ≤ 6339423849475 := by decide +kernel

theorem rows22310R_1139 : rowsJ2 143 144 80 83 ≤ 3268087323730 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1136
#print axioms SieveCert.rows22310R_1139
