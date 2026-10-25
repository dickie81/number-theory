/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1311–1314 of 1732

File 329 of 430: the parts `rows22310R_1311` … `rows22310R_1314` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29279 tests: row 157 columns 77–80, row 157 columns 81–84, row 157 columns
85–89, row 157 columns 90–95), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1311 : rowsJ2 157 158 77 81 ≤ 12297115679390 := by decide +kernel

theorem rows22310R_1312 : rowsJ2 157 158 81 85 ≤ 6911677480645 := by decide +kernel

theorem rows22310R_1313 : rowsJ2 157 158 85 90 ≤ 3426989933314 := by decide +kernel

theorem rows22310R_1314 : rowsJ2 157 158 90 96 ≤ 410962573270 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1311
#print axioms SieveCert.rows22310R_1314
