/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3671–3685 of 4715

File 282 of 351: the parts `rows22250R_3671` … `rows22250R_3685` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 98836 tests: row 137 columns 73–74, row 137 columns 75–76, row 137 columns
77–80, row 137 columns 81–339, row 138 columns 0–23, row 138 columns 24–48, row 138 columns 49–51, row 138 columns
52–53, row 138 columns 54–54, row 138 columns 55–55, row 138 columns 56–56, row 138 columns 57–57, row 138 columns
58–58, row 138 columns 59–59, row 138 columns 60–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3671 : rowsJ2 137 138 73 75 ≤ 6225488562064 := by decide +kernel

theorem rows22250R_3672 : rowsJ2 137 138 75 77 ≤ 4107849731800 := by decide +kernel

theorem rows22250R_3673 : rowsJ2 137 138 77 81 ≤ 3551284965695 := by decide +kernel

theorem rows22250R_3674 : rowsJ2 137 138 81 340 ≤ 630120088758345 := by decide +kernel

theorem rows22250R_3675 : rowsJ2 138 139 0 24 ≤ 5113975156111 := by decide +kernel

theorem rows22250R_3676 : rowsJ2 138 139 24 49 ≤ 3282087418298 := by decide +kernel

theorem rows22250R_3677 : rowsJ2 138 139 49 52 ≤ 6165801573246 := by decide +kernel

theorem rows22250R_3678 : rowsJ2 138 139 52 54 ≤ 6983791406355 := by decide +kernel

theorem rows22250R_3679 : rowsJ2 138 139 54 55 ≤ 4507189265067 := by decide +kernel

theorem rows22250R_3680 : rowsJ2 138 139 55 56 ≤ 5247014513027 := by decide +kernel

theorem rows22250R_3681 : rowsJ2 138 139 56 57 ≤ 6031608441413 := by decide +kernel

theorem rows22250R_3682 : rowsJ2 138 139 57 58 ≤ 6859184076409 := by decide +kernel

theorem rows22250R_3683 : rowsJ2 138 139 58 59 ≤ 7728091557192 := by decide +kernel

theorem rows22250R_3684 : rowsJ2 138 139 59 60 ≤ 8636810849009 := by decide +kernel

theorem rows22250R_3685 : rowsJ2 138 139 60 61 ≤ 9563078892980 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3671
#print axioms SieveCert.rows22250R_3685
