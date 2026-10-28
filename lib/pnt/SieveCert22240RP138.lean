/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1455–1471 of 5066

File 138 of 387: the parts `rows22240R_1455` … `rows22240R_1471` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 96280 in units of a depth-4 test: row 72 columns 22–22, row 72 columns
23–23, row 72 columns 24–24, row 72 columns 25–25, row 72 columns 26–26, row 72 columns 27–27, row 72 columns 28–28,
row 72 columns 29–29, row 72 columns 30–30, row 72 columns 31–31, row 72 columns 32–32, row 72 columns 33–33, row 72
columns 34–35, row 72 columns 36–37, row 72 columns 38–39, row 72 columns 40–41, row 72 columns 42–42), each a sum
of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1455 : rowsJ2 72 73 22 23 ≤ 0 := by decide +kernel

theorem rows22240R_1456 : rowsJ2 72 73 23 24 ≤ 0 := by decide +kernel

theorem rows22240R_1457 : rowsJ2 72 73 24 25 ≤ 0 := by decide +kernel

theorem rows22240R_1458 : rowsJ2 72 73 25 26 ≤ 0 := by decide +kernel

theorem rows22240R_1459 : rowsJ2 72 73 26 27 ≤ 0 := by decide +kernel

theorem rows22240R_1460 : rowsJ2 72 73 27 28 ≤ 0 := by decide +kernel

theorem rows22240R_1461 : rowsJ2 72 73 28 29 ≤ 0 := by decide +kernel

theorem rows22240R_1462 : rowsJ2 72 73 29 30 ≤ 0 := by decide +kernel

theorem rows22240R_1463 : rowsJ2 72 73 30 31 ≤ 0 := by decide +kernel

theorem rows22240R_1464 : rowsJ2 72 73 31 32 ≤ 0 := by decide +kernel

theorem rows22240R_1465 : rowsJ2 72 73 32 33 ≤ 0 := by decide +kernel

theorem rows22240R_1466 : rowsJ2 72 73 33 34 ≤ 0 := by decide +kernel

theorem rows22240R_1467 : rowsJ2 72 73 34 36 ≤ 0 := by decide +kernel

theorem rows22240R_1468 : rowsJ2 72 73 36 38 ≤ 0 := by decide +kernel

theorem rows22240R_1469 : rowsJ2 72 73 38 40 ≤ 0 := by decide +kernel

theorem rows22240R_1470 : rowsJ2 72 73 40 42 ≤ 0 := by decide +kernel

theorem rows22240R_1471 : rowsJ2 72 73 42 43 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1455
#print axioms SieveCert.rows22240R_1471
