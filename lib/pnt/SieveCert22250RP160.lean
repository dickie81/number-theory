/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1590–1606 of 5796

File 160 of 465: the parts `rows22250R_1590` … `rows22250R_1606` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 93998 tests: row 74 columns 74–359, row 75 columns 0–18, row 75 columns
19–20, row 75 columns 21–21, row 75 columns 22–22, row 75 columns 23–23, row 75 columns 24–24, row 75 columns 25–25,
row 75 columns 26–26, row 75 columns 27–27, row 75 columns 28–28, row 75 columns 29–29, row 75 columns 30–30, row 75
columns 31–31, row 75 columns 32–32, row 75 columns 33–33, row 75 columns 34–34), each a sum of refined costs
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

theorem rows22250R_1590 : rowsJ2 74 75 74 360 ≤ 1216943000915 := by decide +kernel

theorem rows22250R_1591 : rowsJ2 75 76 0 19 ≤ 609502290277 := by decide +kernel

theorem rows22250R_1592 : rowsJ2 75 76 19 21 ≤ 0 := by decide +kernel

theorem rows22250R_1593 : rowsJ2 75 76 21 22 ≤ 0 := by decide +kernel

theorem rows22250R_1594 : rowsJ2 75 76 22 23 ≤ 0 := by decide +kernel

theorem rows22250R_1595 : rowsJ2 75 76 23 24 ≤ 0 := by decide +kernel

theorem rows22250R_1596 : rowsJ2 75 76 24 25 ≤ 0 := by decide +kernel

theorem rows22250R_1597 : rowsJ2 75 76 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1598 : rowsJ2 75 76 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1599 : rowsJ2 75 76 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1600 : rowsJ2 75 76 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1601 : rowsJ2 75 76 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1602 : rowsJ2 75 76 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1603 : rowsJ2 75 76 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_1604 : rowsJ2 75 76 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1605 : rowsJ2 75 76 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_1606 : rowsJ2 75 76 34 35 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1590
#print axioms SieveCert.rows22250R_1606
