/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 79–96 of 5066

File 6 of 387: the parts `rows22240R_79` … `rows22240R_96` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (18 parts, work 99889 in units of a depth-4 test: row 27 columns 19–19, row 27 columns
20–20, row 27 columns 21–21, row 27 columns 22–22, row 27 columns 23–23, row 27 columns 24–24, row 27 columns 25–25,
row 27 columns 26–26, row 27 columns 27–339, row 28 columns 0–13, row 28 columns 14–16, row 28 columns 17–18, row 28
columns 19–19, row 28 columns 20–20, row 28 columns 21–21, row 28 columns 22–22, row 28 columns 23–23, row 28
columns 24–24), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22240R_79 : rowsJ2 27 28 19 20 ≤ 1147627734805 := by decide +kernel

theorem rows22240R_80 : rowsJ2 27 28 20 21 ≤ 1360814625907 := by decide +kernel

theorem rows22240R_81 : rowsJ2 27 28 21 22 ≤ 1540834283021 := by decide +kernel

theorem rows22240R_82 : rowsJ2 27 28 22 23 ≤ 1680381730690 := by decide +kernel

theorem rows22240R_83 : rowsJ2 27 28 23 24 ≤ 1774725872047 := by decide +kernel

theorem rows22240R_84 : rowsJ2 27 28 24 25 ≤ 1813011954732 := by decide +kernel

theorem rows22240R_85 : rowsJ2 27 28 25 26 ≤ 1829071153740 := by decide +kernel

theorem rows22240R_86 : rowsJ2 27 28 26 27 ≤ 1823135287470 := by decide +kernel

theorem rows22240R_87 : rowsJ2 27 28 27 340 ≤ 1795565757466 := by decide +kernel

theorem rows22240R_88 : rowsJ2 28 29 0 14 ≤ 1580146508934 := by decide +kernel

theorem rows22240R_89 : rowsJ2 28 29 14 17 ≤ 931219894757 := by decide +kernel

theorem rows22240R_90 : rowsJ2 28 29 17 19 ≤ 1640719587490 := by decide +kernel

theorem rows22240R_91 : rowsJ2 28 29 19 20 ≤ 1173909124715 := by decide +kernel

theorem rows22240R_92 : rowsJ2 28 29 20 21 ≤ 1368192109448 := by decide +kernel

theorem rows22240R_93 : rowsJ2 28 29 21 22 ≤ 1530763373219 := by decide +kernel

theorem rows22240R_94 : rowsJ2 28 29 22 23 ≤ 1654912168749 := by decide +kernel

theorem rows22240R_95 : rowsJ2 28 29 23 24 ≤ 1722120418118 := by decide +kernel

theorem rows22240R_96 : rowsJ2 28 29 24 25 ≤ 1750349253184 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_79
#print axioms SieveCert.rows22240R_96
