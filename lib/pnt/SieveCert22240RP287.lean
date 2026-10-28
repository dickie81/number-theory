/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3593–3607 of 5066

File 287 of 387: the parts `rows22240R_3593` … `rows22240R_3607` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 96053 in units of a depth-4 test: row 125 columns 65–65, row 125
columns 66–66, row 125 columns 67–67, row 125 columns 68–68, row 125 columns 69–69, row 125 columns 70–70, row 125
columns 71–71, row 125 columns 72–72, row 125 columns 73–73, row 125 columns 74–74, row 125 columns 75–75, row 125
columns 76–77, row 125 columns 78–80, row 125 columns 81–83, row 125 columns 84–86), each a sum of refined costs
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

theorem rows22240R_3593 : rowsJ2 125 126 65 66 ≤ 5287158834678 := by decide +kernel

theorem rows22240R_3594 : rowsJ2 125 126 66 67 ≤ 5546934835439 := by decide +kernel

theorem rows22240R_3595 : rowsJ2 125 126 67 68 ≤ 5733286203204 := by decide +kernel

theorem rows22240R_3596 : rowsJ2 125 126 68 69 ≤ 5867868092357 := by decide +kernel

theorem rows22240R_3597 : rowsJ2 125 126 69 70 ≤ 5926790244965 := by decide +kernel

theorem rows22240R_3598 : rowsJ2 125 126 70 71 ≤ 5931592945525 := by decide +kernel

theorem rows22240R_3599 : rowsJ2 125 126 71 72 ≤ 5506184656321 := by decide +kernel

theorem rows22240R_3600 : rowsJ2 125 126 72 73 ≤ 4764682239715 := by decide +kernel

theorem rows22240R_3601 : rowsJ2 125 126 73 74 ≤ 4064564047199 := by decide +kernel

theorem rows22240R_3602 : rowsJ2 125 126 74 75 ≤ 3427884217262 := by decide +kernel

theorem rows22240R_3603 : rowsJ2 125 126 75 76 ≤ 2829658982393 := by decide +kernel

theorem rows22240R_3604 : rowsJ2 125 126 76 78 ≤ 4083376610560 := by decide +kernel

theorem rows22240R_3605 : rowsJ2 125 126 78 81 ≤ 2874272547104 := by decide +kernel

theorem rows22240R_3606 : rowsJ2 125 126 81 84 ≤ 3842748306967 := by decide +kernel

theorem rows22240R_3607 : rowsJ2 125 126 84 87 ≤ 11129558298439 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3593
#print axioms SieveCert.rows22240R_3607
