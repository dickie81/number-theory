/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3985–3999 of 5066

File 315 of 387: the parts `rows22240R_3985` … `rows22240R_3999` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 96548 in units of a depth-4 test: row 138 columns 69–69, row 138
columns 70–70, row 138 columns 71–71, row 138 columns 72–72, row 138 columns 73–73, row 138 columns 74–75, row 138
columns 76–77, row 138 columns 78–81, row 138 columns 82–339, row 139 columns 0–23, row 139 columns 24–46, row 139
columns 47–51, row 139 columns 52–53, row 139 columns 54–54, row 139 columns 55–55), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3985 : rowsJ2 138 139 69 70 ≤ 7232089434111 := by decide +kernel

theorem rows22240R_3986 : rowsJ2 138 139 70 71 ≤ 6369266193771 := by decide +kernel

theorem rows22240R_3987 : rowsJ2 138 139 71 72 ≤ 5552235112991 := by decide +kernel

theorem rows22240R_3988 : rowsJ2 138 139 72 73 ≤ 4800923041545 := by decide +kernel

theorem rows22240R_3989 : rowsJ2 138 139 73 74 ≤ 4092199383365 := by decide +kernel

theorem rows22240R_3990 : rowsJ2 138 139 74 76 ≤ 6286824970679 := by decide +kernel

theorem rows22240R_3991 : rowsJ2 138 139 76 78 ≤ 4103894921158 := by decide +kernel

theorem rows22240R_3992 : rowsJ2 138 139 78 82 ≤ 4763113360340 := by decide +kernel

theorem rows22240R_3993 : rowsJ2 138 139 82 340 ≤ 779677262933560 := by decide +kernel

theorem rows22240R_3994 : rowsJ2 139 140 0 24 ≤ 5953870170025 := by decide +kernel

theorem rows22240R_3995 : rowsJ2 139 140 24 47 ≤ 3278890935649 := by decide +kernel

theorem rows22240R_3996 : rowsJ2 139 140 47 52 ≤ 8119062989178 := by decide +kernel

theorem rows22240R_3997 : rowsJ2 139 140 52 54 ≤ 7035290116636 := by decide +kernel

theorem rows22240R_3998 : rowsJ2 139 140 54 55 ≤ 4540468177651 := by decide +kernel

theorem rows22240R_3999 : rowsJ2 139 140 55 56 ≤ 5285901270169 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3985
#print axioms SieveCert.rows22240R_3999
