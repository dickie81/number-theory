/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1714–1727 of 5066

File 157 of 387: the parts `rows22240R_1714` … `rows22240R_1727` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 90876 in units of a depth-4 test: row 77 columns 30–31, row 77 columns
32–33, row 77 columns 34–36, row 77 columns 37–38, row 77 columns 39–40, row 77 columns 41–41, row 77 columns 42–42,
row 77 columns 43–43, row 77 columns 44–44, row 77 columns 45–45, row 77 columns 46–46, row 77 columns 47–47, row 77
columns 48–48, row 77 columns 49–49), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1714 : rowsJ2 77 78 30 32 ≤ 0 := by decide +kernel

theorem rows22240R_1715 : rowsJ2 77 78 32 34 ≤ 0 := by decide +kernel

theorem rows22240R_1716 : rowsJ2 77 78 34 37 ≤ 466905205764 := by decide +kernel

theorem rows22240R_1717 : rowsJ2 77 78 37 39 ≤ 369602566679 := by decide +kernel

theorem rows22240R_1718 : rowsJ2 77 78 39 41 ≤ 0 := by decide +kernel

theorem rows22240R_1719 : rowsJ2 77 78 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_1720 : rowsJ2 77 78 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_1721 : rowsJ2 77 78 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_1722 : rowsJ2 77 78 44 45 ≤ 60343433862 := by decide +kernel

theorem rows22240R_1723 : rowsJ2 77 78 45 46 ≤ 176470879324 := by decide +kernel

theorem rows22240R_1724 : rowsJ2 77 78 46 47 ≤ 344142944539 := by decide +kernel

theorem rows22240R_1725 : rowsJ2 77 78 47 48 ≤ 734773811502 := by decide +kernel

theorem rows22240R_1726 : rowsJ2 77 78 48 49 ≤ 1353014757572 := by decide +kernel

theorem rows22240R_1727 : rowsJ2 77 78 49 50 ≤ 1862203018341 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1714
#print axioms SieveCert.rows22240R_1727
