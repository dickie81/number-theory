/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3645–3658 of 4715

File 280 of 351: the parts `rows22250R_3645` … `rows22250R_3658` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 95256 in units of a depth-4 test: row 136 columns 74–75, row 136
columns 76–78, row 136 columns 79–83, row 136 columns 84–339, row 137 columns 0–23, row 137 columns 24–48, row 137
columns 49–52, row 137 columns 53–54, row 137 columns 55–55, row 137 columns 56–56, row 137 columns 57–57, row 137
columns 58–58, row 137 columns 59–59, row 137 columns 60–60), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22250R_3645 : rowsJ2 136 137 74 76 ≤ 5466140385972 := by decide +kernel

theorem rows22250R_3646 : rowsJ2 136 137 76 79 ≤ 4712019400141 := by decide +kernel

theorem rows22250R_3647 : rowsJ2 136 137 79 84 ≤ 5562091185924 := by decide +kernel

theorem rows22250R_3648 : rowsJ2 136 137 84 340 ≤ 459692631610011 := by decide +kernel

theorem rows22250R_3649 : rowsJ2 137 138 0 24 ≤ 5879981316663 := by decide +kernel

theorem rows22250R_3650 : rowsJ2 137 138 24 49 ≤ 3421004145436 := by decide +kernel

theorem rows22250R_3651 : rowsJ2 137 138 49 53 ≤ 8192610288819 := by decide +kernel

theorem rows22250R_3652 : rowsJ2 137 138 53 55 ≤ 7538819587255 := by decide +kernel

theorem rows22250R_3653 : rowsJ2 137 138 55 56 ≤ 4804499049170 := by decide +kernel

theorem rows22250R_3654 : rowsJ2 137 138 56 57 ≤ 5555332768009 := by decide +kernel

theorem rows22250R_3655 : rowsJ2 137 138 57 58 ≤ 6349426462714 := by decide +kernel

theorem rows22250R_3656 : rowsJ2 137 138 58 59 ≤ 7185090434196 := by decide +kernel

theorem rows22250R_3657 : rowsJ2 137 138 59 60 ≤ 8060765269044 := by decide +kernel

theorem rows22250R_3658 : rowsJ2 137 138 60 61 ≤ 8954035483968 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3645
#print axioms SieveCert.rows22250R_3658
