/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1280–1289 of 5066

File 123 of 387: the parts `rows22240R_1280` … `rows22240R_1289` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (10 parts, work 88109 in units of a depth-4 test: row 68 columns 45–45, row 68 columns
46–46, row 68 columns 47–47, row 68 columns 48–48, row 68 columns 49–49, row 68 columns 50–50, row 68 columns 51–51,
row 68 columns 52–52, row 68 columns 53–53, row 68 columns 54–54), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1280 : rowsJ2 68 69 45 46 ≤ 190325009186 := by decide +kernel

theorem rows22240R_1281 : rowsJ2 68 69 46 47 ≤ 371160439224 := by decide +kernel

theorem rows22240R_1282 : rowsJ2 68 69 47 48 ≤ 792458409900 := by decide +kernel

theorem rows22240R_1283 : rowsJ2 68 69 48 49 ≤ 1513991597554 := by decide +kernel

theorem rows22240R_1284 : rowsJ2 68 69 49 50 ≤ 2334773741510 := by decide +kernel

theorem rows22240R_1285 : rowsJ2 68 69 50 51 ≤ 3185781162229 := by decide +kernel

theorem rows22240R_1286 : rowsJ2 68 69 51 52 ≤ 4143359467407 := by decide +kernel

theorem rows22240R_1287 : rowsJ2 68 69 52 53 ≤ 5190593924401 := by decide +kernel

theorem rows22240R_1288 : rowsJ2 68 69 53 54 ≤ 6015982192509 := by decide +kernel

theorem rows22240R_1289 : rowsJ2 68 69 54 55 ≤ 6666532729358 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1280
#print axioms SieveCert.rows22240R_1289
