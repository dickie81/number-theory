/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1488–1491 of 1732

File 374 of 430: the parts `rows22310R_1488` … `rows22310R_1491` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 23630 tests: row 178 columns 61–64, row 178 columns 65–69, row 178 columns
70–75, row 178 columns 76–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1488 : rowsJ2 178 179 61 65 ≤ 33602804990698 := by decide +kernel

theorem rows22310R_1489 : rowsJ2 178 179 65 70 ≤ 25585678512026 := by decide +kernel

theorem rows22310R_1490 : rowsJ2 178 179 70 76 ≤ 13641195424297 := by decide +kernel

theorem rows22310R_1491 : rowsJ2 178 179 76 400 ≤ 1977814413411047 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1488
#print axioms SieveCert.rows22310R_1491
