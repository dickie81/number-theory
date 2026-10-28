/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1713–1728 of 4715

File 148 of 351: the parts `rows22250R_1713` … `rows22250R_1728` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 95249 in units of a depth-4 test: row 78 columns 62–62, row 78 columns
63–63, row 78 columns 64–64, row 78 columns 65–65, row 78 columns 66–66, row 78 columns 67–68, row 78 columns 69–70,
row 78 columns 71–72, row 78 columns 73–75, row 78 columns 76–77, row 78 columns 78–339, row 79 columns 0–17, row 79
columns 18–19, row 79 columns 20–21, row 79 columns 22–23, row 79 columns 24–25), each a sum of refined costs
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

theorem rows22250R_1713 : rowsJ2 78 79 62 63 ≤ 305950453948 := by decide +kernel

theorem rows22250R_1714 : rowsJ2 78 79 63 64 ≤ 246135275591 := by decide +kernel

theorem rows22250R_1715 : rowsJ2 78 79 64 65 ≤ 124508955267 := by decide +kernel

theorem rows22250R_1716 : rowsJ2 78 79 65 66 ≤ 63189356936 := by decide +kernel

theorem rows22250R_1717 : rowsJ2 78 79 66 67 ≤ 0 := by decide +kernel

theorem rows22250R_1718 : rowsJ2 78 79 67 69 ≤ 0 := by decide +kernel

theorem rows22250R_1719 : rowsJ2 78 79 69 71 ≤ 0 := by decide +kernel

theorem rows22250R_1720 : rowsJ2 78 79 71 73 ≤ 0 := by decide +kernel

theorem rows22250R_1721 : rowsJ2 78 79 73 76 ≤ 18273779754 := by decide +kernel

theorem rows22250R_1722 : rowsJ2 78 79 76 78 ≤ 399006380189 := by decide +kernel

theorem rows22250R_1723 : rowsJ2 78 79 78 340 ≤ 1410886179892 := by decide +kernel

theorem rows22250R_1724 : rowsJ2 79 80 0 18 ≤ 129385466546 := by decide +kernel

theorem rows22250R_1725 : rowsJ2 79 80 18 20 ≤ 15229481515 := by decide +kernel

theorem rows22250R_1726 : rowsJ2 79 80 20 22 ≤ 6129691140 := by decide +kernel

theorem rows22250R_1727 : rowsJ2 79 80 22 24 ≤ 0 := by decide +kernel

theorem rows22250R_1728 : rowsJ2 79 80 24 26 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1713
#print axioms SieveCert.rows22250R_1728
