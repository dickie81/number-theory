/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1175–1188 of 4715

File 107 of 351: the parts `rows22250R_1175` … `rows22250R_1188` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 95551 in units of a depth-4 test: row 66 columns 63–63, row 66 columns
64–64, row 66 columns 65–65, row 66 columns 66–339, row 67 columns 0–17, row 67 columns 18–20, row 67 columns 21–21,
row 67 columns 22–22, row 67 columns 23–23, row 67 columns 24–24, row 67 columns 25–25, row 67 columns 26–26, row 67
columns 27–27, row 67 columns 28–28), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_1175 : rowsJ2 66 67 63 64 ≤ 6377199768802 := by decide +kernel

theorem rows22250R_1176 : rowsJ2 66 67 64 65 ≤ 5900334084124 := by decide +kernel

theorem rows22250R_1177 : rowsJ2 66 67 65 66 ≤ 5481473411674 := by decide +kernel

theorem rows22250R_1178 : rowsJ2 66 67 66 340 ≤ 4996313097551 := by decide +kernel

theorem rows22250R_1179 : rowsJ2 67 68 0 18 ≤ 1283556319714 := by decide +kernel

theorem rows22250R_1180 : rowsJ2 67 68 18 21 ≤ 4750481952 := by decide +kernel

theorem rows22250R_1181 : rowsJ2 67 68 21 22 ≤ 0 := by decide +kernel

theorem rows22250R_1182 : rowsJ2 67 68 22 23 ≤ 0 := by decide +kernel

theorem rows22250R_1183 : rowsJ2 67 68 23 24 ≤ 0 := by decide +kernel

theorem rows22250R_1184 : rowsJ2 67 68 24 25 ≤ 0 := by decide +kernel

theorem rows22250R_1185 : rowsJ2 67 68 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1186 : rowsJ2 67 68 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1187 : rowsJ2 67 68 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1188 : rowsJ2 67 68 28 29 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1175
#print axioms SieveCert.rows22250R_1188
