/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1640–1655 of 5066

File 152 of 387: the parts `rows22240R_1640` … `rows22240R_1655` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 99126 in units of a depth-4 test: row 75 columns 61–61, row 75 columns
62–62, row 75 columns 63–63, row 75 columns 64–64, row 75 columns 65–65, row 75 columns 66–66, row 75 columns 67–67,
row 75 columns 68–68, row 75 columns 69–69, row 75 columns 70–70, row 75 columns 71–71, row 75 columns 72–72, row 75
columns 73–74, row 75 columns 75–339, row 76 columns 0–17, row 76 columns 18–19), each a sum of refined costs
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

theorem rows22240R_1640 : rowsJ2 75 76 61 62 ≤ 1774940764781 := by decide +kernel

theorem rows22240R_1641 : rowsJ2 75 76 62 63 ≤ 1606554213943 := by decide +kernel

theorem rows22240R_1642 : rowsJ2 75 76 63 64 ≤ 1433707095223 := by decide +kernel

theorem rows22240R_1643 : rowsJ2 75 76 64 65 ≤ 1262332725109 := by decide +kernel

theorem rows22240R_1644 : rowsJ2 75 76 65 66 ≤ 1086193717019 := by decide +kernel

theorem rows22240R_1645 : rowsJ2 75 76 66 67 ≤ 911392647844 := by decide +kernel

theorem rows22240R_1646 : rowsJ2 75 76 67 68 ≤ 731509497502 := by decide +kernel

theorem rows22240R_1647 : rowsJ2 75 76 68 69 ≤ 552825866069 := by decide +kernel

theorem rows22240R_1648 : rowsJ2 75 76 69 70 ≤ 368727477269 := by decide +kernel

theorem rows22240R_1649 : rowsJ2 75 76 70 71 ≤ 185685314572 := by decide +kernel

theorem rows22240R_1650 : rowsJ2 75 76 71 72 ≤ 62354097934 := by decide +kernel

theorem rows22240R_1651 : rowsJ2 75 76 72 73 ≤ 0 := by decide +kernel

theorem rows22240R_1652 : rowsJ2 75 76 73 75 ≤ 0 := by decide +kernel

theorem rows22240R_1653 : rowsJ2 75 76 75 340 ≤ 0 := by decide +kernel

theorem rows22240R_1654 : rowsJ2 76 77 0 18 ≤ 676233286708 := by decide +kernel

theorem rows22240R_1655 : rowsJ2 76 77 18 20 ≤ 3596760866 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1640
#print axioms SieveCert.rows22240R_1655
