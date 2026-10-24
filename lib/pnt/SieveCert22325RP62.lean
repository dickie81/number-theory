/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 237–240 of 561

File 62 of 142: the parts `rows22325R_237` … `rows22325R_240` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 24175 tests: row 88 columns 76–80, row 88 columns 81–86, row 88 columns
87–299, row 89 columns 0–50), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_237 : rowsJ2 88 89 76 81 ≤ 7075057698844 := by decide +kernel

theorem rows22325R_238 : rowsJ2 88 89 81 87 ≤ 37848033239006 := by decide +kernel

theorem rows22325R_239 : rowsJ2 88 89 87 300 ≤ 24441310466767 := by decide +kernel

theorem rows22325R_240 : rowsJ2 89 90 0 51 ≤ 757448242724360 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_237
#print axioms SieveCert.rows22325R_240
