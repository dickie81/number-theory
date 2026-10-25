/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1235–1239 of 1732

File 310 of 430: the parts `rows22310R_1235` … `rows22310R_1239` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (5 parts, 28270 tests: row 150 columns 103–399, row 151 columns 0–58, row 151 columns
59–64, row 151 columns 65–68, row 151 columns 69–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1235 : rowsJ2 150 151 103 400 ≤ 121806381445164 := by decide +kernel

theorem rows22310R_1236 : rowsJ2 151 152 0 59 ≤ 182802670872019 := by decide +kernel

theorem rows22310R_1237 : rowsJ2 151 152 59 65 ≤ 12431270418518 := by decide +kernel

theorem rows22310R_1238 : rowsJ2 151 152 65 69 ≤ 15251825173292 := by decide +kernel

theorem rows22310R_1239 : rowsJ2 151 152 69 72 ≤ 14306794053402 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1235
#print axioms SieveCert.rows22310R_1239
