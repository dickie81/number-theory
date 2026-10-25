/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1607–1620 of 5796

File 161 of 465: the parts `rows22250R_1607` … `rows22250R_1620` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 96953 tests: row 75 columns 35–36, row 75 columns 37–38, row 75 columns
39–40, row 75 columns 41–42, row 75 columns 43–43, row 75 columns 44–44, row 75 columns 45–45, row 75 columns 46–46,
row 75 columns 47–47, row 75 columns 48–48, row 75 columns 49–49, row 75 columns 50–50, row 75 columns 51–51, row 75
columns 52–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22250R_1607 : rowsJ2 75 76 35 37 ≤ 0 := by decide +kernel

theorem rows22250R_1608 : rowsJ2 75 76 37 39 ≤ 0 := by decide +kernel

theorem rows22250R_1609 : rowsJ2 75 76 39 41 ≤ 0 := by decide +kernel

theorem rows22250R_1610 : rowsJ2 75 76 41 43 ≤ 0 := by decide +kernel

theorem rows22250R_1611 : rowsJ2 75 76 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1612 : rowsJ2 75 76 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_1613 : rowsJ2 75 76 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_1614 : rowsJ2 75 76 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_1615 : rowsJ2 75 76 47 48 ≤ 98956628038 := by decide +kernel

theorem rows22250R_1616 : rowsJ2 75 76 48 49 ≤ 443507669828 := by decide +kernel

theorem rows22250R_1617 : rowsJ2 75 76 49 50 ≤ 825869219587 := by decide +kernel

theorem rows22250R_1618 : rowsJ2 75 76 50 51 ≤ 1242131719797 := by decide +kernel

theorem rows22250R_1619 : rowsJ2 75 76 51 52 ≤ 1788044521070 := by decide +kernel

theorem rows22250R_1620 : rowsJ2 75 76 52 53 ≤ 2522610216225 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1607
#print axioms SieveCert.rows22250R_1620
