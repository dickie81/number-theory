/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1311–1326 of 4715

File 118 of 351: the parts `rows22250R_1311` … `rows22250R_1326` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 99328 in units of a depth-4 test: row 69 columns 64–64, row 69 columns
65–65, row 69 columns 66–66, row 69 columns 67–67, row 69 columns 68–68, row 69 columns 69–339, row 70 columns 0–17,
row 70 columns 18–20, row 70 columns 21–21, row 70 columns 22–22, row 70 columns 23–23, row 70 columns 24–24, row 70
columns 25–25, row 70 columns 26–26, row 70 columns 27–27, row 70 columns 28–28), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1311 : rowsJ2 69 70 64 65 ≤ 3680706055932 := by decide +kernel

theorem rows22250R_1312 : rowsJ2 69 70 65 66 ≤ 3323098871738 := by decide +kernel

theorem rows22250R_1313 : rowsJ2 69 70 66 67 ≤ 2955511437451 := by decide +kernel

theorem rows22250R_1314 : rowsJ2 69 70 67 68 ≤ 2590764196281 := by decide +kernel

theorem rows22250R_1315 : rowsJ2 69 70 68 69 ≤ 2284989721092 := by decide +kernel

theorem rows22250R_1316 : rowsJ2 69 70 69 340 ≤ 1981433125749 := by decide +kernel

theorem rows22250R_1317 : rowsJ2 70 71 0 18 ≤ 854977972570 := by decide +kernel

theorem rows22250R_1318 : rowsJ2 70 71 18 21 ≤ 0 := by decide +kernel

theorem rows22250R_1319 : rowsJ2 70 71 21 22 ≤ 0 := by decide +kernel

theorem rows22250R_1320 : rowsJ2 70 71 22 23 ≤ 0 := by decide +kernel

theorem rows22250R_1321 : rowsJ2 70 71 23 24 ≤ 0 := by decide +kernel

theorem rows22250R_1322 : rowsJ2 70 71 24 25 ≤ 0 := by decide +kernel

theorem rows22250R_1323 : rowsJ2 70 71 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1324 : rowsJ2 70 71 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1325 : rowsJ2 70 71 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1326 : rowsJ2 70 71 28 29 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1311
#print axioms SieveCert.rows22250R_1326
