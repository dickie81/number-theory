/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1591–1605 of 4715

File 139 of 351: the parts `rows22250R_1591` … `rows22250R_1605` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 95439 in units of a depth-4 test: row 75 columns 69–69, row 75 columns
70–71, row 75 columns 72–73, row 75 columns 74–339, row 76 columns 0–17, row 76 columns 18–19, row 76 columns 20–21,
row 76 columns 22–22, row 76 columns 23–24, row 76 columns 25–26, row 76 columns 27–28, row 76 columns 29–30, row 76
columns 31–33, row 76 columns 34–36, row 76 columns 37–38), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22250R_1591 : rowsJ2 75 76 69 70 ≤ 0 := by decide +kernel

theorem rows22250R_1592 : rowsJ2 75 76 70 72 ≤ 0 := by decide +kernel

theorem rows22250R_1593 : rowsJ2 75 76 72 74 ≤ 0 := by decide +kernel

theorem rows22250R_1594 : rowsJ2 75 76 74 340 ≤ 18723016622 := by decide +kernel

theorem rows22250R_1595 : rowsJ2 76 77 0 18 ≤ 284300680402 := by decide +kernel

theorem rows22250R_1596 : rowsJ2 76 77 18 20 ≤ 11088920532 := by decide +kernel

theorem rows22250R_1597 : rowsJ2 76 77 20 22 ≤ 12529462796 := by decide +kernel

theorem rows22250R_1598 : rowsJ2 76 77 22 23 ≤ 3196750394 := by decide +kernel

theorem rows22250R_1599 : rowsJ2 76 77 23 25 ≤ 3202495913 := by decide +kernel

theorem rows22250R_1600 : rowsJ2 76 77 25 27 ≤ 0 := by decide +kernel

theorem rows22250R_1601 : rowsJ2 76 77 27 29 ≤ 0 := by decide +kernel

theorem rows22250R_1602 : rowsJ2 76 77 29 31 ≤ 0 := by decide +kernel

theorem rows22250R_1603 : rowsJ2 76 77 31 34 ≤ 0 := by decide +kernel

theorem rows22250R_1604 : rowsJ2 76 77 34 37 ≤ 0 := by decide +kernel

theorem rows22250R_1605 : rowsJ2 76 77 37 39 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1591
#print axioms SieveCert.rows22250R_1605
