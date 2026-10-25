/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1886–1900 of 4715

File 160 of 351: the parts `rows22250R_1886` … `rows22250R_1900` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 99039 tests: row 82 columns 72–75, row 82 columns 76–78, row 82 columns
79–79, row 82 columns 80–80, row 82 columns 81–81, row 82 columns 82–339, row 83 columns 0–16, row 83 columns 17–19,
row 83 columns 20–21, row 83 columns 22–24, row 83 columns 25–28, row 83 columns 29–33, row 83 columns 34–36, row 83
columns 37–38, row 83 columns 39–40), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1886 : rowsJ2 82 83 72 76 ≤ 17707292091 := by decide +kernel

theorem rows22250R_1887 : rowsJ2 82 83 76 79 ≤ 1261785717057 := by decide +kernel

theorem rows22250R_1888 : rowsJ2 82 83 79 80 ≤ 1216673624971 := by decide +kernel

theorem rows22250R_1889 : rowsJ2 82 83 80 81 ≤ 1615329587741 := by decide +kernel

theorem rows22250R_1890 : rowsJ2 82 83 81 82 ≤ 1858353460129 := by decide +kernel

theorem rows22250R_1891 : rowsJ2 82 83 82 340 ≤ 2346243865455 := by decide +kernel

theorem rows22250R_1892 : rowsJ2 83 84 0 17 ≤ 24576635374 := by decide +kernel

theorem rows22250R_1893 : rowsJ2 83 84 17 20 ≤ 2094324790 := by decide +kernel

theorem rows22250R_1894 : rowsJ2 83 84 20 22 ≤ 0 := by decide +kernel

theorem rows22250R_1895 : rowsJ2 83 84 22 25 ≤ 0 := by decide +kernel

theorem rows22250R_1896 : rowsJ2 83 84 25 29 ≤ 0 := by decide +kernel

theorem rows22250R_1897 : rowsJ2 83 84 29 34 ≤ 390894819831 := by decide +kernel

theorem rows22250R_1898 : rowsJ2 83 84 34 37 ≤ 4862648050375 := by decide +kernel

theorem rows22250R_1899 : rowsJ2 83 84 37 39 ≤ 8764502466903 := by decide +kernel

theorem rows22250R_1900 : rowsJ2 83 84 39 41 ≤ 11399409379316 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1886
#print axioms SieveCert.rows22250R_1900
