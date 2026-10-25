/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1688–1700 of 4715

File 146 of 351: the parts `rows22250R_1688` … `rows22250R_1700` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 93070 tests: row 78 columns 28–30, row 78 columns 31–34, row 78 columns
35–37, row 78 columns 38–39, row 78 columns 40–41, row 78 columns 42–42, row 78 columns 43–43, row 78 columns 44–44,
row 78 columns 45–45, row 78 columns 46–46, row 78 columns 47–47, row 78 columns 48–48, row 78 columns 49–49), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1688 : rowsJ2 78 79 28 31 ≤ 0 := by decide +kernel

theorem rows22250R_1689 : rowsJ2 78 79 31 35 ≤ 196371153483 := by decide +kernel

theorem rows22250R_1690 : rowsJ2 78 79 35 38 ≤ 1206248282826 := by decide +kernel

theorem rows22250R_1691 : rowsJ2 78 79 38 40 ≤ 0 := by decide +kernel

theorem rows22250R_1692 : rowsJ2 78 79 40 42 ≤ 0 := by decide +kernel

theorem rows22250R_1693 : rowsJ2 78 79 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1694 : rowsJ2 78 79 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1695 : rowsJ2 78 79 44 45 ≤ 59012804573 := by decide +kernel

theorem rows22250R_1696 : rowsJ2 78 79 45 46 ≤ 231625396461 := by decide +kernel

theorem rows22250R_1697 : rowsJ2 78 79 46 47 ≤ 691019320051 := by decide +kernel

theorem rows22250R_1698 : rowsJ2 78 79 47 48 ≤ 1267467597792 := by decide +kernel

theorem rows22250R_1699 : rowsJ2 78 79 48 49 ≤ 1558113387724 := by decide +kernel

theorem rows22250R_1700 : rowsJ2 78 79 49 50 ≤ 1734961888777 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1688
#print axioms SieveCert.rows22250R_1700
