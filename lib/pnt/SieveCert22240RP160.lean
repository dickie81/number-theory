/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1752–1768 of 5066

File 160 of 387: the parts `rows22240R_1752` … `rows22240R_1768` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 95956 in units of a depth-4 test: row 77 columns 77–339, row 78 columns
0–17, row 78 columns 18–19, row 78 columns 20–21, row 78 columns 22–22, row 78 columns 23–23, row 78 columns 24–24,
row 78 columns 25–25, row 78 columns 26–26, row 78 columns 27–28, row 78 columns 29–30, row 78 columns 31–32, row 78
columns 33–35, row 78 columns 36–37, row 78 columns 38–39, row 78 columns 40–41, row 78 columns 42–42), each a sum
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

theorem rows22240R_1752 : rowsJ2 77 78 77 340 ≤ 1716461525376 := by decide +kernel

theorem rows22240R_1753 : rowsJ2 78 79 0 18 ≤ 485116905949 := by decide +kernel

theorem rows22240R_1754 : rowsJ2 78 79 18 20 ≤ 10023016316 := by decide +kernel

theorem rows22240R_1755 : rowsJ2 78 79 20 22 ≤ 30996399182 := by decide +kernel

theorem rows22240R_1756 : rowsJ2 78 79 22 23 ≤ 12781212563 := by decide +kernel

theorem rows22240R_1757 : rowsJ2 78 79 23 24 ≤ 9166575550 := by decide +kernel

theorem rows22240R_1758 : rowsJ2 78 79 24 25 ≤ 6416583688 := by decide +kernel

theorem rows22240R_1759 : rowsJ2 78 79 25 26 ≤ 3703445798 := by decide +kernel

theorem rows22240R_1760 : rowsJ2 78 79 26 27 ≤ 1840692770 := by decide +kernel

theorem rows22240R_1761 : rowsJ2 78 79 27 29 ≤ 0 := by decide +kernel

theorem rows22240R_1762 : rowsJ2 78 79 29 31 ≤ 0 := by decide +kernel

theorem rows22240R_1763 : rowsJ2 78 79 31 33 ≤ 0 := by decide +kernel

theorem rows22240R_1764 : rowsJ2 78 79 33 36 ≤ 283168573095 := by decide +kernel

theorem rows22240R_1765 : rowsJ2 78 79 36 38 ≤ 1562536806876 := by decide +kernel

theorem rows22240R_1766 : rowsJ2 78 79 38 40 ≤ 712113795540 := by decide +kernel

theorem rows22240R_1767 : rowsJ2 78 79 40 42 ≤ 0 := by decide +kernel

theorem rows22240R_1768 : rowsJ2 78 79 42 43 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1752
#print axioms SieveCert.rows22240R_1768
