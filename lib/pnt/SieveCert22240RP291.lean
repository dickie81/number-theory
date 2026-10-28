/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3652–3665 of 5066

File 291 of 387: the parts `rows22240R_3652` … `rows22240R_3665` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 95814 in units of a depth-4 test: row 127 columns 65–65, row 127
columns 66–66, row 127 columns 67–67, row 127 columns 68–68, row 127 columns 69–69, row 127 columns 70–70, row 127
columns 71–71, row 127 columns 72–72, row 127 columns 73–73, row 127 columns 74–74, row 127 columns 75–75, row 127
columns 76–77, row 127 columns 78–79, row 127 columns 80–82), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3652 : rowsJ2 127 128 65 66 ≤ 6248541225683 := by decide +kernel

theorem rows22240R_3653 : rowsJ2 127 128 66 67 ≤ 6567501732978 := by decide +kernel

theorem rows22240R_3654 : rowsJ2 127 128 67 68 ≤ 6813927257588 := by decide +kernel

theorem rows22240R_3655 : rowsJ2 127 128 68 69 ≤ 7009252087545 := by decide +kernel

theorem rows22240R_3656 : rowsJ2 127 128 69 70 ≤ 7129916389178 := by decide +kernel

theorem rows22240R_3657 : rowsJ2 127 128 70 71 ≤ 6751741903760 := by decide +kernel

theorem rows22240R_3658 : rowsJ2 127 128 71 72 ≤ 5942236744375 := by decide +kernel

theorem rows22240R_3659 : rowsJ2 127 128 72 73 ≤ 5198886791340 := by decide +kernel

theorem rows22240R_3660 : rowsJ2 127 128 73 74 ≤ 4497126061629 := by decide +kernel

theorem rows22240R_3661 : rowsJ2 127 128 74 75 ≤ 3858740480445 := by decide +kernel

theorem rows22240R_3662 : rowsJ2 127 128 75 76 ≤ 3259021164215 := by decide +kernel

theorem rows22240R_3663 : rowsJ2 127 128 76 78 ≤ 4937658458483 := by decide +kernel

theorem rows22240R_3664 : rowsJ2 127 128 78 80 ≤ 3136455439803 := by decide +kernel

theorem rows22240R_3665 : rowsJ2 127 128 80 83 ≤ 4056364483311 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3652
#print axioms SieveCert.rows22240R_3665
