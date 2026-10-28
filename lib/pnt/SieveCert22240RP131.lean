/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1373–1384 of 5066

File 131 of 387: the parts `rows22240R_1373` … `rows22240R_1384` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 91652 in units of a depth-4 test: row 70 columns 42–42, row 70 columns
43–43, row 70 columns 44–44, row 70 columns 45–45, row 70 columns 46–46, row 70 columns 47–47, row 70 columns 48–48,
row 70 columns 49–49, row 70 columns 50–50, row 70 columns 51–51, row 70 columns 52–52, row 70 columns 53–53), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1373 : rowsJ2 70 71 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_1374 : rowsJ2 70 71 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_1375 : rowsJ2 70 71 44 45 ≤ 63964865444 := by decide +kernel

theorem rows22240R_1376 : rowsJ2 70 71 45 46 ≤ 187061546357 := by decide +kernel

theorem rows22240R_1377 : rowsJ2 70 71 46 47 ≤ 364796229380 := by decide +kernel

theorem rows22240R_1378 : rowsJ2 70 71 47 48 ≤ 778870292523 := by decide +kernel

theorem rows22240R_1379 : rowsJ2 70 71 48 49 ≤ 1488031502645 := by decide +kernel

theorem rows22240R_1380 : rowsJ2 70 71 49 50 ≤ 2294739868122 := by decide +kernel

theorem rows22240R_1381 : rowsJ2 70 71 50 51 ≤ 3131155243910 := by decide +kernel

theorem rows22240R_1382 : rowsJ2 70 71 51 52 ≤ 3925323199875 := by decide +kernel

theorem rows22240R_1383 : rowsJ2 70 71 52 53 ≤ 4804380743053 := by decide +kernel

theorem rows22240R_1384 : rowsJ2 70 71 53 54 ≤ 5460330573474 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1373
#print axioms SieveCert.rows22240R_1384
