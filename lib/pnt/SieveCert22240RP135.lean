/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1423–1433 of 5066

File 135 of 387: the parts `rows22240R_1423` … `rows22240R_1433` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 88042 in units of a depth-4 test: row 71 columns 43–43, row 71 columns
44–44, row 71 columns 45–45, row 71 columns 46–46, row 71 columns 47–47, row 71 columns 48–48, row 71 columns 49–49,
row 71 columns 50–50, row 71 columns 51–51, row 71 columns 52–52, row 71 columns 53–53), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1423 : rowsJ2 71 72 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_1424 : rowsJ2 71 72 44 45 ≤ 63421131316 := by decide +kernel

theorem rows22240R_1425 : rowsJ2 71 72 45 46 ≤ 185471427373 := by decide +kernel

theorem rows22240R_1426 : rowsJ2 71 72 46 47 ≤ 361695274529 := by decide +kernel

theorem rows22240R_1427 : rowsJ2 71 72 47 48 ≤ 772249495985 := by decide +kernel

theorem rows22240R_1428 : rowsJ2 71 72 48 49 ≤ 1475382472484 := by decide +kernel

theorem rows22240R_1429 : rowsJ2 71 72 49 50 ≤ 2275233403547 := by decide +kernel

theorem rows22240R_1430 : rowsJ2 71 72 50 51 ≤ 3055460899024 := by decide +kernel

theorem rows22240R_1431 : rowsJ2 71 72 51 52 ≤ 3792228339712 := by decide +kernel

theorem rows22240R_1432 : rowsJ2 71 72 52 53 ≤ 4561845461007 := by decide +kernel

theorem rows22240R_1433 : rowsJ2 71 72 53 54 ≤ 5157450475273 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1423
#print axioms SieveCert.rows22240R_1433
