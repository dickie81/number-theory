/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1849–1864 of 5066

File 167 of 387: the parts `rows22240R_1849` … `rows22240R_1864` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 97576 in units of a depth-4 test: row 80 columns 18–19, row 80 columns
20–21, row 80 columns 22–22, row 80 columns 23–24, row 80 columns 25–26, row 80 columns 27–28, row 80 columns 29–30,
row 80 columns 31–33, row 80 columns 34–36, row 80 columns 37–38, row 80 columns 39–40, row 80 columns 41–41, row 80
columns 42–42, row 80 columns 43–43, row 80 columns 44–44, row 80 columns 45–45), each a sum of refined costs
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

theorem rows22240R_1849 : rowsJ2 80 81 18 20 ≤ 15673860821 := by decide +kernel

theorem rows22240R_1850 : rowsJ2 80 81 20 22 ≤ 22245493208 := by decide +kernel

theorem rows22240R_1851 : rowsJ2 80 81 22 23 ≤ 6499266700 := by decide +kernel

theorem rows22240R_1852 : rowsJ2 80 81 23 25 ≤ 5612559269 := by decide +kernel

theorem rows22240R_1853 : rowsJ2 80 81 25 27 ≤ 0 := by decide +kernel

theorem rows22240R_1854 : rowsJ2 80 81 27 29 ≤ 0 := by decide +kernel

theorem rows22240R_1855 : rowsJ2 80 81 29 31 ≤ 0 := by decide +kernel

theorem rows22240R_1856 : rowsJ2 80 81 31 34 ≤ 0 := by decide +kernel

theorem rows22240R_1857 : rowsJ2 80 81 34 37 ≤ 2235157278125 := by decide +kernel

theorem rows22240R_1858 : rowsJ2 80 81 37 39 ≤ 4195754461025 := by decide +kernel

theorem rows22240R_1859 : rowsJ2 80 81 39 41 ≤ 3450425773279 := by decide +kernel

theorem rows22240R_1860 : rowsJ2 80 81 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_1861 : rowsJ2 80 81 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_1862 : rowsJ2 80 81 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_1863 : rowsJ2 80 81 44 45 ≤ 58913949039 := by decide +kernel

theorem rows22240R_1864 : rowsJ2 80 81 45 46 ≤ 172290433704 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1849
#print axioms SieveCert.rows22240R_1864
