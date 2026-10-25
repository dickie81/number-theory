/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1637–1651 of 5796

File 164 of 465: the parts `rows22250R_1637` … `rows22250R_1651` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 96442 tests: row 75 columns 69–69, row 75 columns 70–70, row 75 columns
71–71, row 75 columns 72–72, row 75 columns 73–73, row 75 columns 74–74, row 75 columns 75–359, row 76 columns 0–18,
row 76 columns 19–20, row 76 columns 21–21, row 76 columns 22–22, row 76 columns 23–23, row 76 columns 24–24, row 76
columns 25–25, row 76 columns 26–26), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1637 : rowsJ2 75 76 69 70 ≤ 1872280745816 := by decide +kernel

theorem rows22250R_1638 : rowsJ2 75 76 70 71 ≤ 1685930609173 := by decide +kernel

theorem rows22250R_1639 : rowsJ2 75 76 71 72 ≤ 1494596658452 := by decide +kernel

theorem rows22250R_1640 : rowsJ2 75 76 72 73 ≤ 1304607229734 := by decide +kernel

theorem rows22250R_1641 : rowsJ2 75 76 73 74 ≤ 1109324135119 := by decide +kernel

theorem rows22250R_1642 : rowsJ2 75 76 74 75 ≤ 915254373039 := by decide +kernel

theorem rows22250R_1643 : rowsJ2 75 76 75 360 ≤ 715566647503 := by decide +kernel

theorem rows22250R_1644 : rowsJ2 76 77 0 19 ≤ 525990598241 := by decide +kernel

theorem rows22250R_1645 : rowsJ2 76 77 19 21 ≤ 0 := by decide +kernel

theorem rows22250R_1646 : rowsJ2 76 77 21 22 ≤ 0 := by decide +kernel

theorem rows22250R_1647 : rowsJ2 76 77 22 23 ≤ 0 := by decide +kernel

theorem rows22250R_1648 : rowsJ2 76 77 23 24 ≤ 0 := by decide +kernel

theorem rows22250R_1649 : rowsJ2 76 77 24 25 ≤ 0 := by decide +kernel

theorem rows22250R_1650 : rowsJ2 76 77 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1651 : rowsJ2 76 77 26 27 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1637
#print axioms SieveCert.rows22250R_1651
