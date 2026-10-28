/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1599–1616 of 5066

File 149 of 387: the parts `rows22240R_1599` … `rows22240R_1616` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (18 parts, work 96112 in units of a depth-4 test: row 74 columns 70–70, row 74 columns
71–71, row 74 columns 72–72, row 74 columns 73–73, row 74 columns 74–339, row 75 columns 0–17, row 75 columns 18–20,
row 75 columns 21–21, row 75 columns 22–22, row 75 columns 23–23, row 75 columns 24–24, row 75 columns 25–25, row 75
columns 26–26, row 75 columns 27–27, row 75 columns 28–28, row 75 columns 29–29, row 75 columns 30–31, row 75
columns 32–33), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1599 : rowsJ2 74 75 70 71 ≤ 368596452934 := by decide +kernel

theorem rows22240R_1600 : rowsJ2 74 75 71 72 ≤ 185632977884 := by decide +kernel

theorem rows22240R_1601 : rowsJ2 74 75 72 73 ≤ 62341027845 := by decide +kernel

theorem rows22240R_1602 : rowsJ2 74 75 73 74 ≤ 0 := by decide +kernel

theorem rows22240R_1603 : rowsJ2 74 75 74 340 ≤ 0 := by decide +kernel

theorem rows22240R_1604 : rowsJ2 75 76 0 18 ≤ 783009545068 := by decide +kernel

theorem rows22240R_1605 : rowsJ2 75 76 18 21 ≤ 10045118967 := by decide +kernel

theorem rows22240R_1606 : rowsJ2 75 76 21 22 ≤ 11977369268 := by decide +kernel

theorem rows22240R_1607 : rowsJ2 75 76 22 23 ≤ 12955779005 := by decide +kernel

theorem rows22240R_1608 : rowsJ2 75 76 23 24 ≤ 11169032529 := by decide +kernel

theorem rows22240R_1609 : rowsJ2 75 76 24 25 ≤ 9333011517 := by decide +kernel

theorem rows22240R_1610 : rowsJ2 75 76 25 26 ≤ 6585656357 := by decide +kernel

theorem rows22240R_1611 : rowsJ2 75 76 26 27 ≤ 4742747707 := by decide +kernel

theorem rows22240R_1612 : rowsJ2 75 76 27 28 ≤ 2893274021 := by decide +kernel

theorem rows22240R_1613 : rowsJ2 75 76 28 29 ≤ 1938346769 := by decide +kernel

theorem rows22240R_1614 : rowsJ2 75 76 29 30 ≤ 963933771 := by decide +kernel

theorem rows22240R_1615 : rowsJ2 75 76 30 32 ≤ 0 := by decide +kernel

theorem rows22240R_1616 : rowsJ2 75 76 32 34 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1599
#print axioms SieveCert.rows22240R_1616
