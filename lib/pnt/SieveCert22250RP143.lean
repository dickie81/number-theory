/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1647–1659 of 4715

File 143 of 351: the parts `rows22250R_1647` … `rows22250R_1659` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 90855 in units of a depth-4 test: row 77 columns 33–35, row 77 columns
36–38, row 77 columns 39–40, row 77 columns 41–41, row 77 columns 42–42, row 77 columns 43–43, row 77 columns 44–44,
row 77 columns 45–45, row 77 columns 46–46, row 77 columns 47–47, row 77 columns 48–48, row 77 columns 49–49, row 77
columns 50–50), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22250R_1647 : rowsJ2 77 78 33 36 ≤ 0 := by decide +kernel

theorem rows22250R_1648 : rowsJ2 77 78 36 39 ≤ 0 := by decide +kernel

theorem rows22250R_1649 : rowsJ2 77 78 39 41 ≤ 0 := by decide +kernel

theorem rows22250R_1650 : rowsJ2 77 78 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_1651 : rowsJ2 77 78 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1652 : rowsJ2 77 78 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1653 : rowsJ2 77 78 44 45 ≤ 59488590942 := by decide +kernel

theorem rows22250R_1654 : rowsJ2 77 78 45 46 ≤ 233492859075 := by decide +kernel

theorem rows22250R_1655 : rowsJ2 77 78 46 47 ≤ 696590612171 := by decide +kernel

theorem rows22250R_1656 : rowsJ2 77 78 47 48 ≤ 1331068362144 := by decide +kernel

theorem rows22250R_1657 : rowsJ2 77 78 48 49 ≤ 1732623889198 := by decide +kernel

theorem rows22250R_1658 : rowsJ2 77 78 49 50 ≤ 1968636524583 := by decide +kernel

theorem rows22250R_1659 : rowsJ2 77 78 50 51 ≤ 2211529301282 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1647
#print axioms SieveCert.rows22250R_1659
