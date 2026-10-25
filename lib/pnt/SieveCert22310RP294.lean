/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1171–1174 of 1732

File 294 of 430: the parts `rows22310R_1171` … `rows22310R_1174` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27863 tests: row 145 columns 102–399, row 146 columns 0–59, row 146 columns
60–66, row 146 columns 67–70), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1171 : rowsJ2 145 146 102 400 ≤ 314903963785839 := by decide +kernel

theorem rows22310R_1172 : rowsJ2 146 147 0 60 ≤ 227074869453646 := by decide +kernel

theorem rows22310R_1173 : rowsJ2 146 147 60 67 ≤ 11536620759794 := by decide +kernel

theorem rows22310R_1174 : rowsJ2 146 147 67 71 ≤ 12213579943599 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1171
#print axioms SieveCert.rows22310R_1174
