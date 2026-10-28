/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1792–1808 of 5066

File 163 of 387: the parts `rows22240R_1792` … `rows22240R_1808` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 97822 in units of a depth-4 test: row 78 columns 66–66, row 78 columns
67–67, row 78 columns 68–68, row 78 columns 69–69, row 78 columns 70–71, row 78 columns 72–73, row 78 columns 74–75,
row 78 columns 76–77, row 78 columns 78–339, row 79 columns 0–17, row 79 columns 18–19, row 79 columns 20–21, row 79
columns 22–22, row 79 columns 23–23, row 79 columns 24–24, row 79 columns 25–26, row 79 columns 27–28), each a sum
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

theorem rows22240R_1792 : rowsJ2 78 79 66 67 ≤ 243087474343 := by decide +kernel

theorem rows22240R_1793 : rowsJ2 78 79 67 68 ≤ 123004707635 := by decide +kernel

theorem rows22240R_1794 : rowsJ2 78 79 68 69 ≤ 62445742246 := by decide +kernel

theorem rows22240R_1795 : rowsJ2 78 79 69 70 ≤ 0 := by decide +kernel

theorem rows22240R_1796 : rowsJ2 78 79 70 72 ≤ 0 := by decide +kernel

theorem rows22240R_1797 : rowsJ2 78 79 72 74 ≤ 0 := by decide +kernel

theorem rows22240R_1798 : rowsJ2 78 79 74 76 ≤ 0 := by decide +kernel

theorem rows22240R_1799 : rowsJ2 78 79 76 78 ≤ 1794435480033 := by decide +kernel

theorem rows22240R_1800 : rowsJ2 78 79 78 340 ≤ 2810600457091 := by decide +kernel

theorem rows22240R_1801 : rowsJ2 79 80 0 18 ≤ 402079511438 := by decide +kernel

theorem rows22240R_1802 : rowsJ2 79 80 18 20 ≤ 13728588026 := by decide +kernel

theorem rows22240R_1803 : rowsJ2 79 80 20 22 ≤ 27588017334 := by decide +kernel

theorem rows22240R_1804 : rowsJ2 79 80 22 23 ≤ 9226105179 := by decide +kernel

theorem rows22240R_1805 : rowsJ2 79 80 23 24 ≤ 6456922379 := by decide +kernel

theorem rows22240R_1806 : rowsJ2 79 80 24 25 ≤ 3725981019 := by decide +kernel

theorem rows22240R_1807 : rowsJ2 79 80 25 27 ≤ 1851532368 := by decide +kernel

theorem rows22240R_1808 : rowsJ2 79 80 27 29 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1792
#print axioms SieveCert.rows22240R_1808
