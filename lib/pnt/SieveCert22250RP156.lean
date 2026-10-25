/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1547–1562 of 5796

File 156 of 465: the parts `rows22250R_1547` … `rows22250R_1562` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 94046 tests: row 74 columns 27–27, row 74 columns 28–28, row 74 columns
29–29, row 74 columns 30–30, row 74 columns 31–31, row 74 columns 32–32, row 74 columns 33–33, row 74 columns 34–34,
row 74 columns 35–35, row 74 columns 36–37, row 74 columns 38–39, row 74 columns 40–41, row 74 columns 42–43, row 74
columns 44–44, row 74 columns 45–45, row 74 columns 46–46), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22250R_1547 : rowsJ2 74 75 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1548 : rowsJ2 74 75 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1549 : rowsJ2 74 75 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1550 : rowsJ2 74 75 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1551 : rowsJ2 74 75 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_1552 : rowsJ2 74 75 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1553 : rowsJ2 74 75 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_1554 : rowsJ2 74 75 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_1555 : rowsJ2 74 75 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_1556 : rowsJ2 74 75 36 38 ≤ 0 := by decide +kernel

theorem rows22250R_1557 : rowsJ2 74 75 38 40 ≤ 0 := by decide +kernel

theorem rows22250R_1558 : rowsJ2 74 75 40 42 ≤ 0 := by decide +kernel

theorem rows22250R_1559 : rowsJ2 74 75 42 44 ≤ 0 := by decide +kernel

theorem rows22250R_1560 : rowsJ2 74 75 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_1561 : rowsJ2 74 75 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_1562 : rowsJ2 74 75 46 47 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1547
#print axioms SieveCert.rows22250R_1562
