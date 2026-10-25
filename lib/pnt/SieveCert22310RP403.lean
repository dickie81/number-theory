/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1600–1603 of 1732

File 403 of 430: the parts `rows22310R_1600` … `rows22310R_1603` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29098 tests: row 201 columns 43–49, row 201 columns 50–399, row 202 columns
0–41, row 202 columns 42–48), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1600 : rowsJ2 201 202 43 50 ≤ 87835398335216 := by decide +kernel

theorem rows22310R_1601 : rowsJ2 201 202 50 400 ≤ 2214124852316455 := by decide +kernel

theorem rows22310R_1602 : rowsJ2 202 203 0 42 ≤ 31959352401447 := by decide +kernel

theorem rows22310R_1603 : rowsJ2 202 203 42 49 ≤ 86942405974031 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1600
#print axioms SieveCert.rows22310R_1603
