/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1488–1503 of 5796

File 151 of 465: the parts `rows22250R_1488` … `rows22250R_1503` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 97478 tests: row 73 columns 0–18, row 73 columns 19–20, row 73 columns
21–22, row 73 columns 23–23, row 73 columns 24–24, row 73 columns 25–25, row 73 columns 26–26, row 73 columns 27–27,
row 73 columns 28–28, row 73 columns 29–29, row 73 columns 30–30, row 73 columns 31–31, row 73 columns 32–32, row 73
columns 33–33, row 73 columns 34–34, row 73 columns 35–35), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22250R_1488 : rowsJ2 73 74 0 19 ≤ 806693535276 := by decide +kernel

theorem rows22250R_1489 : rowsJ2 73 74 19 21 ≤ 0 := by decide +kernel

theorem rows22250R_1490 : rowsJ2 73 74 21 23 ≤ 0 := by decide +kernel

theorem rows22250R_1491 : rowsJ2 73 74 23 24 ≤ 0 := by decide +kernel

theorem rows22250R_1492 : rowsJ2 73 74 24 25 ≤ 0 := by decide +kernel

theorem rows22250R_1493 : rowsJ2 73 74 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1494 : rowsJ2 73 74 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1495 : rowsJ2 73 74 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1496 : rowsJ2 73 74 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1497 : rowsJ2 73 74 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1498 : rowsJ2 73 74 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1499 : rowsJ2 73 74 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_1500 : rowsJ2 73 74 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1501 : rowsJ2 73 74 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_1502 : rowsJ2 73 74 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_1503 : rowsJ2 73 74 35 36 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1488
#print axioms SieveCert.rows22250R_1503
