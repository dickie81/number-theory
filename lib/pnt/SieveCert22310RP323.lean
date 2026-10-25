/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1288–1291 of 1732

File 323 of 430: the parts `rows22310R_1288` … `rows22310R_1291` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29440 tests: row 155 columns 74–76, row 155 columns 77–80, row 155 columns
81–84, row 155 columns 85–89), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1288 : rowsJ2 155 156 74 77 ≤ 14019892142270 := by decide +kernel

theorem rows22310R_1289 : rowsJ2 155 156 77 81 ≤ 12637567354595 := by decide +kernel

theorem rows22310R_1290 : rowsJ2 155 156 81 85 ≤ 7261710411552 := by decide +kernel

theorem rows22310R_1291 : rowsJ2 155 156 85 90 ≤ 3874645465600 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1288
#print axioms SieveCert.rows22310R_1291
