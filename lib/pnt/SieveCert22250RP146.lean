/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1433–1445 of 5796

File 146 of 465: the parts `rows22250R_1433` … `rows22250R_1445` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 99707 tests: row 71 columns 68–68, row 71 columns 69–69, row 71 columns
70–70, row 71 columns 71–359, row 72 columns 0–18, row 72 columns 19–21, row 72 columns 22–22, row 72 columns 23–23,
row 72 columns 24–24, row 72 columns 25–25, row 72 columns 26–26, row 72 columns 27–27, row 72 columns 28–28), each
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

theorem rows22250R_1433 : rowsJ2 71 72 68 69 ≤ 4253427015184 := by decide +kernel

theorem rows22250R_1434 : rowsJ2 71 72 69 70 ≤ 3973003044774 := by decide +kernel

theorem rows22250R_1435 : rowsJ2 71 72 70 71 ≤ 3695019183030 := by decide +kernel

theorem rows22250R_1436 : rowsJ2 71 72 71 360 ≤ 3409883867881 := by decide +kernel

theorem rows22250R_1437 : rowsJ2 72 73 0 19 ≤ 919411160232 := by decide +kernel

theorem rows22250R_1438 : rowsJ2 72 73 19 22 ≤ 0 := by decide +kernel

theorem rows22250R_1439 : rowsJ2 72 73 22 23 ≤ 0 := by decide +kernel

theorem rows22250R_1440 : rowsJ2 72 73 23 24 ≤ 0 := by decide +kernel

theorem rows22250R_1441 : rowsJ2 72 73 24 25 ≤ 0 := by decide +kernel

theorem rows22250R_1442 : rowsJ2 72 73 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1443 : rowsJ2 72 73 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1444 : rowsJ2 72 73 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1445 : rowsJ2 72 73 28 29 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1433
#print axioms SieveCert.rows22250R_1445
