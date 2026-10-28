/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1729–1742 of 4715

File 149 of 351: the parts `rows22250R_1729` … `rows22250R_1742` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 98536 in units of a depth-4 test: row 79 columns 26–28, row 79 columns
29–31, row 79 columns 32–35, row 79 columns 36–38, row 79 columns 39–40, row 79 columns 41–41, row 79 columns 42–42,
row 79 columns 43–43, row 79 columns 44–44, row 79 columns 45–45, row 79 columns 46–46, row 79 columns 47–47, row 79
columns 48–48, row 79 columns 49–49), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_1729 : rowsJ2 79 80 26 29 ≤ 0 := by decide +kernel

theorem rows22250R_1730 : rowsJ2 79 80 29 32 ≤ 0 := by decide +kernel

theorem rows22250R_1731 : rowsJ2 79 80 32 36 ≤ 865757756896 := by decide +kernel

theorem rows22250R_1732 : rowsJ2 79 80 36 39 ≤ 3282958467285 := by decide +kernel

theorem rows22250R_1733 : rowsJ2 79 80 39 41 ≤ 0 := by decide +kernel

theorem rows22250R_1734 : rowsJ2 79 80 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_1735 : rowsJ2 79 80 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1736 : rowsJ2 79 80 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1737 : rowsJ2 79 80 44 45 ≤ 58544568443 := by decide +kernel

theorem rows22250R_1738 : rowsJ2 79 80 45 46 ≤ 229787568549 := by decide +kernel

theorem rows22250R_1739 : rowsJ2 79 80 46 47 ≤ 685536438582 := by decide +kernel

theorem rows22250R_1740 : rowsJ2 79 80 47 48 ≤ 1150628767742 := by decide +kernel

theorem rows22250R_1741 : rowsJ2 79 80 48 49 ≤ 1382850796393 := by decide +kernel

theorem rows22250R_1742 : rowsJ2 79 80 49 50 ≤ 1446430400316 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1729
#print axioms SieveCert.rows22250R_1742
