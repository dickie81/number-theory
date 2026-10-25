/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1289–1302 of 5796

File 133 of 465: the parts `rows22250R_1289` … `rows22250R_1302` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 97075 tests: row 69 columns 25–25, row 69 columns 26–26, row 69 columns
27–27, row 69 columns 28–28, row 69 columns 29–29, row 69 columns 30–30, row 69 columns 31–31, row 69 columns 32–32,
row 69 columns 33–33, row 69 columns 34–34, row 69 columns 35–35, row 69 columns 36–36, row 69 columns 37–37, row 69
columns 38–38), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1289 : rowsJ2 69 70 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1290 : rowsJ2 69 70 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1291 : rowsJ2 69 70 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1292 : rowsJ2 69 70 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1293 : rowsJ2 69 70 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1294 : rowsJ2 69 70 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1295 : rowsJ2 69 70 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_1296 : rowsJ2 69 70 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1297 : rowsJ2 69 70 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_1298 : rowsJ2 69 70 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_1299 : rowsJ2 69 70 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_1300 : rowsJ2 69 70 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_1301 : rowsJ2 69 70 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_1302 : rowsJ2 69 70 38 39 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1289
#print axioms SieveCert.rows22250R_1302
