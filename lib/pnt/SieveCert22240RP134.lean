/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1406–1422 of 5066

File 134 of 387: the parts `rows22240R_1406` … `rows22240R_1422` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 96158 in units of a depth-4 test: row 71 columns 23–23, row 71 columns
24–24, row 71 columns 25–25, row 71 columns 26–26, row 71 columns 27–27, row 71 columns 28–28, row 71 columns 29–29,
row 71 columns 30–30, row 71 columns 31–31, row 71 columns 32–32, row 71 columns 33–33, row 71 columns 34–34, row 71
columns 35–36, row 71 columns 37–38, row 71 columns 39–40, row 71 columns 41–41, row 71 columns 42–42), each a sum
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

theorem rows22240R_1406 : rowsJ2 71 72 23 24 ≤ 0 := by decide +kernel

theorem rows22240R_1407 : rowsJ2 71 72 24 25 ≤ 0 := by decide +kernel

theorem rows22240R_1408 : rowsJ2 71 72 25 26 ≤ 0 := by decide +kernel

theorem rows22240R_1409 : rowsJ2 71 72 26 27 ≤ 0 := by decide +kernel

theorem rows22240R_1410 : rowsJ2 71 72 27 28 ≤ 0 := by decide +kernel

theorem rows22240R_1411 : rowsJ2 71 72 28 29 ≤ 0 := by decide +kernel

theorem rows22240R_1412 : rowsJ2 71 72 29 30 ≤ 0 := by decide +kernel

theorem rows22240R_1413 : rowsJ2 71 72 30 31 ≤ 0 := by decide +kernel

theorem rows22240R_1414 : rowsJ2 71 72 31 32 ≤ 0 := by decide +kernel

theorem rows22240R_1415 : rowsJ2 71 72 32 33 ≤ 0 := by decide +kernel

theorem rows22240R_1416 : rowsJ2 71 72 33 34 ≤ 0 := by decide +kernel

theorem rows22240R_1417 : rowsJ2 71 72 34 35 ≤ 0 := by decide +kernel

theorem rows22240R_1418 : rowsJ2 71 72 35 37 ≤ 0 := by decide +kernel

theorem rows22240R_1419 : rowsJ2 71 72 37 39 ≤ 0 := by decide +kernel

theorem rows22240R_1420 : rowsJ2 71 72 39 41 ≤ 0 := by decide +kernel

theorem rows22240R_1421 : rowsJ2 71 72 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_1422 : rowsJ2 71 72 42 43 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1406
#print axioms SieveCert.rows22240R_1422
