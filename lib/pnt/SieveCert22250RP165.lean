/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1652–1668 of 5796

File 165 of 465: the parts `rows22250R_1652` … `rows22250R_1668` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 99163 tests: row 76 columns 27–27, row 76 columns 28–28, row 76 columns
29–29, row 76 columns 30–30, row 76 columns 31–31, row 76 columns 32–32, row 76 columns 33–33, row 76 columns 34–35,
row 76 columns 36–37, row 76 columns 38–39, row 76 columns 40–41, row 76 columns 42–43, row 76 columns 44–44, row 76
columns 45–45, row 76 columns 46–46, row 76 columns 47–47, row 76 columns 48–48), each a sum of refined costs
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

theorem rows22250R_1652 : rowsJ2 76 77 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1653 : rowsJ2 76 77 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1654 : rowsJ2 76 77 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1655 : rowsJ2 76 77 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1656 : rowsJ2 76 77 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_1657 : rowsJ2 76 77 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1658 : rowsJ2 76 77 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_1659 : rowsJ2 76 77 34 36 ≤ 0 := by decide +kernel

theorem rows22250R_1660 : rowsJ2 76 77 36 38 ≤ 0 := by decide +kernel

theorem rows22250R_1661 : rowsJ2 76 77 38 40 ≤ 0 := by decide +kernel

theorem rows22250R_1662 : rowsJ2 76 77 40 42 ≤ 0 := by decide +kernel

theorem rows22250R_1663 : rowsJ2 76 77 42 44 ≤ 0 := by decide +kernel

theorem rows22250R_1664 : rowsJ2 76 77 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_1665 : rowsJ2 76 77 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_1666 : rowsJ2 76 77 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_1667 : rowsJ2 76 77 47 48 ≤ 98170001515 := by decide +kernel

theorem rows22250R_1668 : rowsJ2 76 77 48 49 ≤ 439982136439 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1652
#print axioms SieveCert.rows22250R_1668
