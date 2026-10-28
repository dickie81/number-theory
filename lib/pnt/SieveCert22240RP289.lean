/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3622–3636 of 5066

File 289 of 387: the parts `rows22240R_3622` … `rows22240R_3636` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 98335 in units of a depth-4 test: row 126 columns 65–65, row 126
columns 66–66, row 126 columns 67–67, row 126 columns 68–68, row 126 columns 69–69, row 126 columns 70–70, row 126
columns 71–71, row 126 columns 72–72, row 126 columns 73–73, row 126 columns 74–74, row 126 columns 75–75, row 126
columns 76–77, row 126 columns 78–79, row 126 columns 80–82, row 126 columns 83–85), each a sum of refined costs
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

theorem rows22240R_3622 : rowsJ2 126 127 65 66 ≤ 5764803932636 := by decide +kernel

theorem rows22240R_3623 : rowsJ2 126 127 66 67 ≤ 6053947241780 := by decide +kernel

theorem rows22240R_3624 : rowsJ2 126 127 67 68 ≤ 6270108301089 := by decide +kernel

theorem rows22240R_3625 : rowsJ2 126 127 68 69 ≤ 6434824821714 := by decide +kernel

theorem rows22240R_3626 : rowsJ2 126 127 69 70 ≤ 6524381173898 := by decide +kernel

theorem rows22240R_3627 : rowsJ2 126 127 70 71 ≤ 6560226784735 := by decide +kernel

theorem rows22240R_3628 : rowsJ2 126 127 71 72 ≤ 5751532273842 := by decide +kernel

theorem rows22240R_3629 : rowsJ2 126 127 72 73 ≤ 5009028409833 := by decide +kernel

theorem rows22240R_3630 : rowsJ2 126 127 73 74 ≤ 4308012914720 := by decide +kernel

theorem rows22240R_3631 : rowsJ2 126 127 74 75 ≤ 3670405058193 := by decide +kernel

theorem rows22240R_3632 : rowsJ2 126 127 75 76 ≤ 3071359180619 := by decide +kernel

theorem rows22240R_3633 : rowsJ2 126 127 76 78 ≤ 4564339255644 := by decide +kernel

theorem rows22240R_3634 : rowsJ2 126 127 78 80 ≤ 2765498426294 := by decide +kernel

theorem rows22240R_3635 : rowsJ2 126 127 80 83 ≤ 3403878052074 := by decide +kernel

theorem rows22240R_3636 : rowsJ2 126 127 83 86 ≤ 8871597848715 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3622
#print axioms SieveCert.rows22240R_3636
