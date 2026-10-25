/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1771–1784 of 4715

File 152 of 351: the parts `rows22250R_1771` … `rows22250R_1784` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 93280 tests: row 80 columns 28–30, row 80 columns 31–34, row 80 columns
35–37, row 80 columns 38–39, row 80 columns 40–40, row 80 columns 41–41, row 80 columns 42–42, row 80 columns 43–43,
row 80 columns 44–44, row 80 columns 45–45, row 80 columns 46–46, row 80 columns 47–47, row 80 columns 48–48, row 80
columns 49–49), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1771 : rowsJ2 80 81 28 31 ≤ 0 := by decide +kernel

theorem rows22250R_1772 : rowsJ2 80 81 31 35 ≤ 680903646643 := by decide +kernel

theorem rows22250R_1773 : rowsJ2 80 81 35 38 ≤ 4237317268250 := by decide +kernel

theorem rows22250R_1774 : rowsJ2 80 81 38 40 ≤ 3309917768095 := by decide +kernel

theorem rows22250R_1775 : rowsJ2 80 81 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_1776 : rowsJ2 80 81 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_1777 : rowsJ2 80 81 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1778 : rowsJ2 80 81 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1779 : rowsJ2 80 81 44 45 ≤ 58083704243 := by decide +kernel

theorem rows22250R_1780 : rowsJ2 80 81 45 46 ≤ 227978675486 := by decide +kernel

theorem rows22250R_1781 : rowsJ2 80 81 46 47 ≤ 626892128407 := by decide +kernel

theorem rows22250R_1782 : rowsJ2 80 81 47 48 ≤ 1033301819862 := by decide +kernel

theorem rows22250R_1783 : rowsJ2 80 81 48 49 ≤ 1152891928898 := by decide +kernel

theorem rows22250R_1784 : rowsJ2 80 81 49 50 ≤ 1156280303219 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1771
#print axioms SieveCert.rows22250R_1784
