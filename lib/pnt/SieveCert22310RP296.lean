/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1179–1182 of 1732

File 296 of 430: the parts `rows22310R_1179` … `rows22310R_1182` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29440 tests: row 146 columns 83–85, row 146 columns 86–89, row 146 columns
90–93, row 146 columns 94–98), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1179 : rowsJ2 146 147 83 86 ≤ 2435040968906 := by decide +kernel

theorem rows22310R_1180 : rowsJ2 146 147 86 90 ≤ 522636952811 := by decide +kernel

theorem rows22310R_1181 : rowsJ2 146 147 90 94 ≤ 0 := by decide +kernel

theorem rows22310R_1182 : rowsJ2 146 147 94 99 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1179
#print axioms SieveCert.rows22310R_1182
