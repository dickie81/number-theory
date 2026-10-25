/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1858–1870 of 4715

File 158 of 351: the parts `rows22250R_1858` … `rows22250R_1870` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 92932 tests: row 82 columns 38–39, row 82 columns 40–40, row 82 columns
41–41, row 82 columns 42–42, row 82 columns 43–43, row 82 columns 44–44, row 82 columns 45–45, row 82 columns 46–46,
row 82 columns 47–47, row 82 columns 48–48, row 82 columns 49–49, row 82 columns 50–50, row 82 columns 51–51), each
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

theorem rows22250R_1858 : rowsJ2 82 83 38 40 ≤ 8582474402327 := by decide +kernel

theorem rows22250R_1859 : rowsJ2 82 83 40 41 ≤ 3513000960551 := by decide +kernel

theorem rows22250R_1860 : rowsJ2 82 83 41 42 ≤ 2037819190531 := by decide +kernel

theorem rows22250R_1861 : rowsJ2 82 83 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1862 : rowsJ2 82 83 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1863 : rowsJ2 82 83 44 45 ≤ 57183406049 := by decide +kernel

theorem rows22250R_1864 : rowsJ2 82 83 45 46 ≤ 224445002958 := by decide +kernel

theorem rows22250R_1865 : rowsJ2 82 83 46 47 ≤ 454706415151 := by decide +kernel

theorem rows22250R_1866 : rowsJ2 82 83 47 48 ≤ 688588568721 := by decide +kernel

theorem rows22250R_1867 : rowsJ2 82 83 48 49 ≤ 634186598356 := by decide +kernel

theorem rows22250R_1868 : rowsJ2 82 83 49 50 ≤ 577836424728 := by decide +kernel

theorem rows22250R_1869 : rowsJ2 82 83 50 51 ≤ 464167190507 := by decide +kernel

theorem rows22250R_1870 : rowsJ2 82 83 51 52 ≤ 407174315994 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1858
#print axioms SieveCert.rows22250R_1870
