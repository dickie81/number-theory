/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1159–1162 of 1732

File 291 of 430: the parts `rows22310R_1159` … `rows22310R_1162` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27850 tests: row 145 columns 0–59, row 145 columns 60–66, row 145 columns
67–70, row 145 columns 71–73), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1159 : rowsJ2 145 146 0 60 ≤ 235951722665232 := by decide +kernel

theorem rows22310R_1160 : rowsJ2 145 146 60 67 ≤ 10453931018785 := by decide +kernel

theorem rows22310R_1161 : rowsJ2 145 146 67 71 ≤ 11276698424426 := by decide +kernel

theorem rows22310R_1162 : rowsJ2 145 146 71 74 ≤ 9717437639512 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1159
#print axioms SieveCert.rows22310R_1162
