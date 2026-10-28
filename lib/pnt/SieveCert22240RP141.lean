/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1492–1506 of 5066

File 141 of 387: the parts `rows22240R_1492` … `rows22240R_1506` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 99166 in units of a depth-4 test: row 72 columns 63–63, row 72 columns
64–64, row 72 columns 65–65, row 72 columns 66–66, row 72 columns 67–67, row 72 columns 68–68, row 72 columns 69–69,
row 72 columns 70–70, row 72 columns 71–71, row 72 columns 72–339, row 73 columns 0–17, row 73 columns 18–20, row 73
columns 21–21, row 73 columns 22–22, row 73 columns 23–23), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1492 : rowsJ2 72 73 63 64 ≤ 2818876655313 := by decide +kernel

theorem rows22240R_1493 : rowsJ2 72 73 64 65 ≤ 2590008243194 := by decide +kernel

theorem rows22240R_1494 : rowsJ2 72 73 65 66 ≤ 2299762009609 := by decide +kernel

theorem rows22240R_1495 : rowsJ2 72 73 66 67 ≤ 2066585593378 := by decide +kernel

theorem rows22240R_1496 : rowsJ2 72 73 67 68 ≤ 1770687974618 := by decide +kernel

theorem rows22240R_1497 : rowsJ2 72 73 68 69 ≤ 1532562905456 := by decide +kernel

theorem rows22240R_1498 : rowsJ2 72 73 69 70 ≤ 1230298270031 := by decide +kernel

theorem rows22240R_1499 : rowsJ2 72 73 70 71 ≤ 986557539390 := by decide +kernel

theorem rows22240R_1500 : rowsJ2 72 73 71 72 ≤ 744310191937 := by decide +kernel

theorem rows22240R_1501 : rowsJ2 72 73 72 340 ≤ 561091200414 := by decide +kernel

theorem rows22240R_1502 : rowsJ2 73 74 0 18 ≤ 1034723305798 := by decide +kernel

theorem rows22240R_1503 : rowsJ2 73 74 18 21 ≤ 1781250869 := by decide +kernel

theorem rows22240R_1504 : rowsJ2 73 74 21 22 ≤ 4659087384 := by decide +kernel

theorem rows22240R_1505 : rowsJ2 73 74 22 23 ≤ 6570252627 := by decide +kernel

theorem rows22240R_1506 : rowsJ2 73 74 23 24 ≤ 5609316784 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1492
#print axioms SieveCert.rows22240R_1506
