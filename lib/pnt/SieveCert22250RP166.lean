/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1974–1987 of 4715

File 166 of 351: the parts `rows22250R_1974` … `rows22250R_1987` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 92805 in units of a depth-4 test: row 84 columns 84–339, row 85 columns
0–16, row 85 columns 17–19, row 85 columns 20–22, row 85 columns 23–26, row 85 columns 27–31, row 85 columns 32–35,
row 85 columns 36–37, row 85 columns 38–39, row 85 columns 40–40, row 85 columns 41–41, row 85 columns 42–42, row 85
columns 43–43, row 85 columns 44–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_1974 : rowsJ2 84 85 84 340 ≤ 3971088834318 := by decide +kernel

theorem rows22250R_1975 : rowsJ2 85 86 0 17 ≤ 5673075678 := by decide +kernel

theorem rows22250R_1976 : rowsJ2 85 86 17 20 ≤ 0 := by decide +kernel

theorem rows22250R_1977 : rowsJ2 85 86 20 23 ≤ 0 := by decide +kernel

theorem rows22250R_1978 : rowsJ2 85 86 23 27 ≤ 0 := by decide +kernel

theorem rows22250R_1979 : rowsJ2 85 86 27 32 ≤ 0 := by decide +kernel

theorem rows22250R_1980 : rowsJ2 85 86 32 36 ≤ 3908529211841 := by decide +kernel

theorem rows22250R_1981 : rowsJ2 85 86 36 38 ≤ 7941811870168 := by decide +kernel

theorem rows22250R_1982 : rowsJ2 85 86 38 40 ≤ 12474734015803 := by decide +kernel

theorem rows22250R_1983 : rowsJ2 85 86 40 41 ≤ 8149319514319 := by decide +kernel

theorem rows22250R_1984 : rowsJ2 85 86 41 42 ≤ 9484166620513 := by decide +kernel

theorem rows22250R_1985 : rowsJ2 85 86 42 43 ≤ 8481426207387 := by decide +kernel

theorem rows22250R_1986 : rowsJ2 85 86 43 44 ≤ 6384729874653 := by decide +kernel

theorem rows22250R_1987 : rowsJ2 85 86 44 45 ≤ 3792709632114 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1974
#print axioms SieveCert.rows22250R_1987
