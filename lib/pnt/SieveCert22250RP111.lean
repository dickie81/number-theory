/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1223–1239 of 4715

File 111 of 351: the parts `rows22250R_1223` … `rows22250R_1239` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, work 97109 in units of a depth-4 test: row 67 columns 66–66, row 67 columns
67–339, row 68 columns 0–17, row 68 columns 18–20, row 68 columns 21–21, row 68 columns 22–22, row 68 columns 23–23,
row 68 columns 24–24, row 68 columns 25–25, row 68 columns 26–26, row 68 columns 27–27, row 68 columns 28–28, row 68
columns 29–29, row 68 columns 30–30, row 68 columns 31–31, row 68 columns 32–32, row 68 columns 33–33), each a sum
of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1223 : rowsJ2 67 68 66 67 ≤ 4292548894453 := by decide +kernel

theorem rows22250R_1224 : rowsJ2 67 68 67 340 ≤ 3868318152552 := by decide +kernel

theorem rows22250R_1225 : rowsJ2 68 69 0 18 ≤ 1130801947895 := by decide +kernel

theorem rows22250R_1226 : rowsJ2 68 69 18 21 ≤ 0 := by decide +kernel

theorem rows22250R_1227 : rowsJ2 68 69 21 22 ≤ 0 := by decide +kernel

theorem rows22250R_1228 : rowsJ2 68 69 22 23 ≤ 0 := by decide +kernel

theorem rows22250R_1229 : rowsJ2 68 69 23 24 ≤ 0 := by decide +kernel

theorem rows22250R_1230 : rowsJ2 68 69 24 25 ≤ 0 := by decide +kernel

theorem rows22250R_1231 : rowsJ2 68 69 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1232 : rowsJ2 68 69 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1233 : rowsJ2 68 69 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1234 : rowsJ2 68 69 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1235 : rowsJ2 68 69 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1236 : rowsJ2 68 69 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1237 : rowsJ2 68 69 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_1238 : rowsJ2 68 69 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1239 : rowsJ2 68 69 33 34 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1223
#print axioms SieveCert.rows22250R_1239
