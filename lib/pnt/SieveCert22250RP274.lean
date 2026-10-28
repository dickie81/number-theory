/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3560–3575 of 4715

File 274 of 351: the parts `rows22250R_3560` … `rows22250R_3575` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 99243 in units of a depth-4 test: row 133 columns 73–73, row 133
columns 74–74, row 133 columns 75–76, row 133 columns 77–78, row 133 columns 79–82, row 133 columns 83–86, row 133
columns 87–339, row 134 columns 0–23, row 134 columns 24–35, row 134 columns 36–52, row 134 columns 53–54, row 134
columns 55–56, row 134 columns 57–57, row 134 columns 58–58, row 134 columns 59–59, row 134 columns 60–60), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22250R_3560 : rowsJ2 133 134 73 74 ≤ 3900528640864 := by decide +kernel

theorem rows22250R_3561 : rowsJ2 133 134 74 75 ≤ 3318026766658 := by decide +kernel

theorem rows22250R_3562 : rowsJ2 133 134 75 77 ≤ 5109147382737 := by decide +kernel

theorem rows22250R_3563 : rowsJ2 133 134 77 79 ≤ 3382933470454 := by decide +kernel

theorem rows22250R_3564 : rowsJ2 133 134 79 83 ≤ 4034232169053 := by decide +kernel

theorem rows22250R_3565 : rowsJ2 133 134 83 87 ≤ 16832060129132 := by decide +kernel

theorem rows22250R_3566 : rowsJ2 133 134 87 340 ≤ 620355467215954 := by decide +kernel

theorem rows22250R_3567 : rowsJ2 134 135 0 24 ≤ 5742197573660 := by decide +kernel

theorem rows22250R_3568 : rowsJ2 134 135 24 36 ≤ 6050855506013 := by decide +kernel

theorem rows22250R_3569 : rowsJ2 134 135 36 53 ≤ 5880325340766 := by decide +kernel

theorem rows22250R_3570 : rowsJ2 134 135 53 55 ≤ 5396565384173 := by decide +kernel

theorem rows22250R_3571 : rowsJ2 134 135 55 57 ≤ 7819375797269 := by decide +kernel

theorem rows22250R_3572 : rowsJ2 134 135 57 58 ≤ 4932440168943 := by decide +kernel

theorem rows22250R_3573 : rowsJ2 134 135 58 59 ≤ 5671400991149 := by decide +kernel

theorem rows22250R_3574 : rowsJ2 134 135 59 60 ≤ 6451081793048 := by decide +kernel

theorem rows22250R_3575 : rowsJ2 134 135 60 61 ≤ 7248607015386 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3560
#print axioms SieveCert.rows22250R_3575
