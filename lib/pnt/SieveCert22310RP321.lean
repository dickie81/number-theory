/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1280–1283 of 1732

File 321 of 430: the parts `rows22310R_1280` … `rows22310R_1283` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28475 tests: row 154 columns 86–90, row 154 columns 91–95, row 154 columns
96–399, row 155 columns 0–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1280 : rowsJ2 154 155 86 91 ≤ 3086493972839 := by decide +kernel

theorem rows22310R_1281 : rowsJ2 154 155 91 96 ≤ 439885187296 := by decide +kernel

theorem rows22310R_1282 : rowsJ2 154 155 96 400 ≤ 790621498513 := by decide +kernel

theorem rows22310R_1283 : rowsJ2 155 156 0 58 ≤ 151793729598602 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1280
#print axioms SieveCert.rows22310R_1283
