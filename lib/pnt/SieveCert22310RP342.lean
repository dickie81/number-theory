/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1363–1366 of 1732

File 342 of 430: the parts `rows22310R_1363` … `rows22310R_1366` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25383 tests: row 162 columns 80–84, row 162 columns 85–90, row 162 columns
91–399, row 163 columns 0–55), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1363 : rowsJ2 162 163 80 85 ≤ 6772787429664 := by decide +kernel

theorem rows22310R_1364 : rowsJ2 162 163 85 91 ≤ 1636563807500 := by decide +kernel

theorem rows22310R_1365 : rowsJ2 162 163 91 400 ≤ 499848166501882 := by decide +kernel

theorem rows22310R_1366 : rowsJ2 163 164 0 56 ≤ 101226087246009 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1363
#print axioms SieveCert.rows22310R_1366
