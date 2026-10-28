/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1785–1798 of 4715

File 153 of 351: the parts `rows22250R_1785` … `rows22250R_1798` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 99878 in units of a depth-4 test: row 80 columns 50–50, row 80 columns
51–51, row 80 columns 52–52, row 80 columns 53–53, row 80 columns 54–54, row 80 columns 55–55, row 80 columns 56–56,
row 80 columns 57–57, row 80 columns 58–58, row 80 columns 59–59, row 80 columns 60–60, row 80 columns 61–61, row 80
columns 62–62, row 80 columns 63–63), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_1785 : rowsJ2 80 81 50 51 ≤ 1045174473909 := by decide +kernel

theorem rows22250R_1786 : rowsJ2 80 81 51 52 ≤ 931243186346 := by decide +kernel

theorem rows22250R_1787 : rowsJ2 80 81 52 53 ≤ 758851438753 := by decide +kernel

theorem rows22250R_1788 : rowsJ2 80 81 53 54 ≤ 643416177347 := by decide +kernel

theorem rows22250R_1789 : rowsJ2 80 81 54 55 ≤ 468540920608 := by decide +kernel

theorem rows22250R_1790 : rowsJ2 80 81 55 56 ≤ 351255482935 := by decide +kernel

theorem rows22250R_1791 : rowsJ2 80 81 56 57 ≤ 235000274645 := by decide +kernel

theorem rows22250R_1792 : rowsJ2 80 81 57 58 ≤ 176564174926 := by decide +kernel

theorem rows22250R_1793 : rowsJ2 80 81 58 59 ≤ 118616351875 := by decide +kernel

theorem rows22250R_1794 : rowsJ2 80 81 59 60 ≤ 118855517300 := by decide +kernel

theorem rows22250R_1795 : rowsJ2 80 81 60 61 ≤ 59909012402 := by decide +kernel

theorem rows22250R_1796 : rowsJ2 80 81 61 62 ≤ 60052488215 := by decide +kernel

theorem rows22250R_1797 : rowsJ2 80 81 62 63 ≤ 0 := by decide +kernel

theorem rows22250R_1798 : rowsJ2 80 81 63 64 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1785
#print axioms SieveCert.rows22250R_1798
