/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1387–1402 of 5796

File 142 of 465: the parts `rows22250R_1387` … `rows22250R_1402` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 98514 tests: row 71 columns 22–22, row 71 columns 23–23, row 71 columns
24–24, row 71 columns 25–25, row 71 columns 26–26, row 71 columns 27–27, row 71 columns 28–28, row 71 columns 29–29,
row 71 columns 30–30, row 71 columns 31–31, row 71 columns 32–32, row 71 columns 33–33, row 71 columns 34–34, row 71
columns 35–35, row 71 columns 36–36, row 71 columns 37–37), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1387 : rowsJ2 71 72 22 23 ≤ 0 := by decide +kernel

theorem rows22250R_1388 : rowsJ2 71 72 23 24 ≤ 0 := by decide +kernel

theorem rows22250R_1389 : rowsJ2 71 72 24 25 ≤ 0 := by decide +kernel

theorem rows22250R_1390 : rowsJ2 71 72 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1391 : rowsJ2 71 72 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1392 : rowsJ2 71 72 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1393 : rowsJ2 71 72 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1394 : rowsJ2 71 72 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1395 : rowsJ2 71 72 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1396 : rowsJ2 71 72 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_1397 : rowsJ2 71 72 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1398 : rowsJ2 71 72 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_1399 : rowsJ2 71 72 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_1400 : rowsJ2 71 72 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_1401 : rowsJ2 71 72 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_1402 : rowsJ2 71 72 37 38 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1387
#print axioms SieveCert.rows22250R_1402
