/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1631–1646 of 4715

File 142 of 351: the parts `rows22250R_1631` … `rows22250R_1646` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 99568 in units of a depth-4 test: row 76 columns 65–65, row 76 columns
66–66, row 76 columns 67–67, row 76 columns 68–68, row 76 columns 69–70, row 76 columns 71–72, row 76 columns 73–74,
row 76 columns 75–339, row 77 columns 0–17, row 77 columns 18–19, row 77 columns 20–21, row 77 columns 22–23, row 77
columns 24–25, row 77 columns 26–27, row 77 columns 28–29, row 77 columns 30–32), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1631 : rowsJ2 76 77 65 66 ≤ 373339914211 := by decide +kernel

theorem rows22250R_1632 : rowsJ2 76 77 66 67 ≤ 187942508806 := by decide +kernel

theorem rows22250R_1633 : rowsJ2 76 77 67 68 ≤ 63090269015 := by decide +kernel

theorem rows22250R_1634 : rowsJ2 76 77 68 69 ≤ 0 := by decide +kernel

theorem rows22250R_1635 : rowsJ2 76 77 69 71 ≤ 0 := by decide +kernel

theorem rows22250R_1636 : rowsJ2 76 77 71 73 ≤ 0 := by decide +kernel

theorem rows22250R_1637 : rowsJ2 76 77 73 75 ≤ 0 := by decide +kernel

theorem rows22250R_1638 : rowsJ2 76 77 75 340 ≤ 129418249772 := by decide +kernel

theorem rows22250R_1639 : rowsJ2 77 78 0 18 ≤ 222613260165 := by decide +kernel

theorem rows22250R_1640 : rowsJ2 77 78 18 20 ≤ 14207151040 := by decide +kernel

theorem rows22250R_1641 : rowsJ2 77 78 20 22 ≤ 10426304981 := by decide +kernel

theorem rows22250R_1642 : rowsJ2 77 78 22 24 ≤ 3222475266 := by decide +kernel

theorem rows22250R_1643 : rowsJ2 77 78 24 26 ≤ 0 := by decide +kernel

theorem rows22250R_1644 : rowsJ2 77 78 26 28 ≤ 0 := by decide +kernel

theorem rows22250R_1645 : rowsJ2 77 78 28 30 ≤ 0 := by decide +kernel

theorem rows22250R_1646 : rowsJ2 77 78 30 33 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1631
#print axioms SieveCert.rows22250R_1646
