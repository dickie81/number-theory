/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1766–1778 of 5796

File 174 of 465: the parts `rows22250R_1766` … `rows22250R_1778` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 90424 tests: row 78 columns 37–38, row 78 columns 39–40, row 78 columns
41–42, row 78 columns 43–43, row 78 columns 44–44, row 78 columns 45–45, row 78 columns 46–46, row 78 columns 47–47,
row 78 columns 48–48, row 78 columns 49–49, row 78 columns 50–50, row 78 columns 51–51, row 78 columns 52–52), each
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

theorem rows22250R_1766 : rowsJ2 78 79 37 39 ≤ 0 := by decide +kernel

theorem rows22250R_1767 : rowsJ2 78 79 39 41 ≤ 0 := by decide +kernel

theorem rows22250R_1768 : rowsJ2 78 79 41 43 ≤ 0 := by decide +kernel

theorem rows22250R_1769 : rowsJ2 78 79 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1770 : rowsJ2 78 79 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_1771 : rowsJ2 78 79 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_1772 : rowsJ2 78 79 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_1773 : rowsJ2 78 79 47 48 ≤ 96633679654 := by decide +kernel

theorem rows22250R_1774 : rowsJ2 78 79 48 49 ≤ 433096589286 := by decide +kernel

theorem rows22250R_1775 : rowsJ2 78 79 49 50 ≤ 806482427545 := by decide +kernel

theorem rows22250R_1776 : rowsJ2 78 79 50 51 ≤ 1212973411477 := by decide +kernel

theorem rows22250R_1777 : rowsJ2 78 79 51 52 ≤ 1705405967495 := by decide +kernel

theorem rows22250R_1778 : rowsJ2 78 79 52 53 ≤ 2260006535457 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1766
#print axioms SieveCert.rows22250R_1778
