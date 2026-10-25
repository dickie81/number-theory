/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1234–1246 of 5796

File 128 of 465: the parts `rows22250R_1234` … `rows22250R_1246` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 97839 tests: row 67 columns 67–359, row 68 columns 0–17, row 68 columns
18–21, row 68 columns 22–22, row 68 columns 23–23, row 68 columns 24–24, row 68 columns 25–25, row 68 columns 26–26,
row 68 columns 27–27, row 68 columns 28–28, row 68 columns 29–29, row 68 columns 30–30, row 68 columns 31–31), each
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

theorem rows22250R_1234 : rowsJ2 67 68 67 360 ≤ 7833074278430 := by decide +kernel

theorem rows22250R_1235 : rowsJ2 68 69 0 18 ≤ 1416941183350 := by decide +kernel

theorem rows22250R_1236 : rowsJ2 68 69 18 22 ≤ 70028607075 := by decide +kernel

theorem rows22250R_1237 : rowsJ2 68 69 22 23 ≤ 3313913934 := by decide +kernel

theorem rows22250R_1238 : rowsJ2 68 69 23 24 ≤ 0 := by decide +kernel

theorem rows22250R_1239 : rowsJ2 68 69 24 25 ≤ 0 := by decide +kernel

theorem rows22250R_1240 : rowsJ2 68 69 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1241 : rowsJ2 68 69 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1242 : rowsJ2 68 69 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1243 : rowsJ2 68 69 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1244 : rowsJ2 68 69 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1245 : rowsJ2 68 69 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1246 : rowsJ2 68 69 31 32 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1234
#print axioms SieveCert.rows22250R_1246
