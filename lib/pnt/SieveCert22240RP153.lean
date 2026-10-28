/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1656–1673 of 5066

File 153 of 387: the parts `rows22240R_1656` … `rows22240R_1673` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (18 parts, work 97819 in units of a depth-4 test: row 76 columns 20–21, row 76 columns
22–22, row 76 columns 23–23, row 76 columns 24–24, row 76 columns 25–25, row 76 columns 26–26, row 76 columns 27–27,
row 76 columns 28–28, row 76 columns 29–30, row 76 columns 31–32, row 76 columns 33–34, row 76 columns 35–36, row 76
columns 37–38, row 76 columns 39–40, row 76 columns 41–41, row 76 columns 42–42, row 76 columns 43–43, row 76
columns 44–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1656 : rowsJ2 76 77 20 22 ≤ 24692424115 := by decide +kernel

theorem rows22240R_1657 : rowsJ2 76 77 22 23 ≤ 13849572588 := by decide +kernel

theorem rows22240R_1658 : rowsJ2 76 77 23 24 ≤ 11131674949 := by decide +kernel

theorem rows22240R_1659 : rowsJ2 76 77 24 25 ≤ 8368379162 := by decide +kernel

theorem rows22240R_1660 : rowsJ2 76 77 25 26 ≤ 5643162702 := by decide +kernel

theorem rows22240R_1661 : rowsJ2 76 77 26 27 ≤ 3784339233 := by decide +kernel

theorem rows22240R_1662 : rowsJ2 76 77 27 28 ≤ 1948649801 := by decide +kernel

theorem rows22240R_1663 : rowsJ2 76 77 28 29 ≤ 968883467 := by decide +kernel

theorem rows22240R_1664 : rowsJ2 76 77 29 31 ≤ 0 := by decide +kernel

theorem rows22240R_1665 : rowsJ2 76 77 31 33 ≤ 0 := by decide +kernel

theorem rows22240R_1666 : rowsJ2 76 77 33 35 ≤ 0 := by decide +kernel

theorem rows22240R_1667 : rowsJ2 76 77 35 37 ≤ 0 := by decide +kernel

theorem rows22240R_1668 : rowsJ2 76 77 37 39 ≤ 0 := by decide +kernel

theorem rows22240R_1669 : rowsJ2 76 77 39 41 ≤ 0 := by decide +kernel

theorem rows22240R_1670 : rowsJ2 76 77 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_1671 : rowsJ2 76 77 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_1672 : rowsJ2 76 77 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_1673 : rowsJ2 76 77 44 45 ≤ 60835470289 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1656
#print axioms SieveCert.rows22240R_1673
