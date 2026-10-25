/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1132–1135 of 1732

File 284 of 430: the parts `rows22310R_1132` … `rows22310R_1135` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28270 tests: row 142 columns 103–399, row 143 columns 0–59, row 143 columns
60–66, row 143 columns 67–70), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1132 : rowsJ2 142 143 103 400 ≤ 388408776675591 := by decide +kernel

theorem rows22310R_1133 : rowsJ2 143 144 0 60 ≤ 255427456807362 := by decide +kernel

theorem rows22310R_1134 : rowsJ2 143 144 60 67 ≤ 8424809753808 := by decide +kernel

theorem rows22310R_1135 : rowsJ2 143 144 67 71 ≤ 9488942785400 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1132
#print axioms SieveCert.rows22310R_1135
