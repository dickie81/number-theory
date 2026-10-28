/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1545–1561 of 5066

File 145 of 387: the parts `rows22240R_1545` … `rows22240R_1561` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 97288 in units of a depth-4 test: row 73 columns 66–66, row 73 columns
67–67, row 73 columns 68–68, row 73 columns 69–69, row 73 columns 70–70, row 73 columns 71–71, row 73 columns 72–72,
row 73 columns 73–339, row 74 columns 0–17, row 74 columns 18–20, row 74 columns 21–21, row 74 columns 22–22, row 74
columns 23–23, row 74 columns 24–24, row 74 columns 25–25, row 74 columns 26–26, row 74 columns 27–27), each a sum
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

theorem rows22240R_1545 : rowsJ2 73 74 66 67 ≤ 1578701841522 := by decide +kernel

theorem rows22240R_1546 : rowsJ2 73 74 67 68 ≤ 1339831493200 := by decide +kernel

theorem rows22240R_1547 : rowsJ2 73 74 68 69 ≤ 1102651305465 := by decide +kernel

theorem rows22240R_1548 : rowsJ2 73 74 69 70 ≤ 858399433777 := by decide +kernel

theorem rows22240R_1549 : rowsJ2 73 74 70 71 ≤ 615650545267 := by decide +kernel

theorem rows22240R_1550 : rowsJ2 73 74 71 72 ≤ 431941924321 := by decide +kernel

theorem rows22240R_1551 : rowsJ2 73 74 72 73 ≤ 249248191237 := by decide +kernel

theorem rows22240R_1552 : rowsJ2 73 74 73 340 ≤ 126209785895 := by decide +kernel

theorem rows22240R_1553 : rowsJ2 74 75 0 18 ≤ 905158891465 := by decide +kernel

theorem rows22240R_1554 : rowsJ2 74 75 18 21 ≤ 4457111419 := by decide +kernel

theorem rows22240R_1555 : rowsJ2 74 75 21 22 ≤ 10271414879 := by decide +kernel

theorem rows22240R_1556 : rowsJ2 74 75 22 23 ≤ 11196275940 := by decide +kernel

theorem rows22240R_1557 : rowsJ2 74 75 23 24 ≤ 11209749071 := by decide +kernel

theorem rows22240R_1558 : rowsJ2 74 75 24 25 ≤ 9356542482 := by decide +kernel

theorem rows22240R_1559 : rowsJ2 74 75 25 26 ≤ 7530898647 := by decide +kernel

theorem rows22240R_1560 : rowsJ2 74 75 26 27 ≤ 5673151257 := by decide +kernel

theorem rows22240R_1561 : rowsJ2 74 75 27 28 ≤ 3839543585 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1545
#print axioms SieveCert.rows22240R_1561
