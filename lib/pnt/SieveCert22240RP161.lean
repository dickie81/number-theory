/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1769–1779 of 5066

File 161 of 387: the parts `rows22240R_1769` … `rows22240R_1779` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 93157 in units of a depth-4 test: row 78 columns 43–43, row 78 columns
44–44, row 78 columns 45–45, row 78 columns 46–46, row 78 columns 47–47, row 78 columns 48–48, row 78 columns 49–49,
row 78 columns 50–50, row 78 columns 51–51, row 78 columns 52–52, row 78 columns 53–53), each a sum of refined costs
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

theorem rows22240R_1769 : rowsJ2 78 79 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_1770 : rowsJ2 78 79 44 45 ≤ 59859292874 := by decide +kernel

theorem rows22240R_1771 : rowsJ2 78 79 45 46 ≤ 175055037027 := by decide +kernel

theorem rows22240R_1772 : rowsJ2 78 79 46 47 ≤ 341381853649 := by decide +kernel

theorem rows22240R_1773 : rowsJ2 78 79 47 48 ≤ 728878652792 := by decide +kernel

theorem rows22240R_1774 : rowsJ2 78 79 48 49 ≤ 1290714901057 := by decide +kernel

theorem rows22240R_1775 : rowsJ2 78 79 49 50 ≤ 1691203570396 := by decide +kernel

theorem rows22240R_1776 : rowsJ2 78 79 50 51 ≤ 1921149445133 := by decide +kernel

theorem rows22240R_1777 : rowsJ2 78 79 51 52 ≤ 2045367696557 := by decide +kernel

theorem rows22240R_1778 : rowsJ2 78 79 52 53 ≤ 2233453600784 := by decide +kernel

theorem rows22240R_1779 : rowsJ2 78 79 53 54 ≤ 2010802476514 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1769
#print axioms SieveCert.rows22240R_1779
