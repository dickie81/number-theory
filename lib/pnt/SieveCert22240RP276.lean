/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3418–3434 of 5066

File 276 of 387: the parts `rows22240R_3418` … `rows22240R_3434` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 96661 in units of a depth-4 test: row 119 columns 62–63, row 119
columns 64–64, row 119 columns 65–65, row 119 columns 66–66, row 119 columns 67–67, row 119 columns 68–68, row 119
columns 69–69, row 119 columns 70–70, row 119 columns 71–72, row 119 columns 73–74, row 119 columns 75–77, row 119
columns 78–80, row 119 columns 81–83, row 119 columns 84–86, row 119 columns 87–88, row 119 columns 89–90, row 119
columns 91–92), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3418 : rowsJ2 119 120 62 64 ≤ 4764528168880 := by decide +kernel

theorem rows22240R_3419 : rowsJ2 119 120 64 65 ≤ 2728655399451 := by decide +kernel

theorem rows22240R_3420 : rowsJ2 119 120 65 66 ≤ 2869060053098 := by decide +kernel

theorem rows22240R_3421 : rowsJ2 119 120 66 67 ≤ 2957918812505 := by decide +kernel

theorem rows22240R_3422 : rowsJ2 119 120 67 68 ≤ 2970882733022 := by decide +kernel

theorem rows22240R_3423 : rowsJ2 119 120 68 69 ≤ 2930308083514 := by decide +kernel

theorem rows22240R_3424 : rowsJ2 119 120 69 70 ≤ 2811197986168 := by decide +kernel

theorem rows22240R_3425 : rowsJ2 119 120 70 71 ≤ 2635729988902 := by decide +kernel

theorem rows22240R_3426 : rowsJ2 119 120 71 73 ≤ 4439092214359 := by decide +kernel

theorem rows22240R_3427 : rowsJ2 119 120 73 75 ≤ 2781121460736 := by decide +kernel

theorem rows22240R_3428 : rowsJ2 119 120 75 78 ≤ 531422675650 := by decide +kernel

theorem rows22240R_3429 : rowsJ2 119 120 78 81 ≤ 0 := by decide +kernel

theorem rows22240R_3430 : rowsJ2 119 120 81 84 ≤ 2259018655451 := by decide +kernel

theorem rows22240R_3431 : rowsJ2 119 120 84 87 ≤ 7515255696469 := by decide +kernel

theorem rows22240R_3432 : rowsJ2 119 120 87 89 ≤ 9144956401406 := by decide +kernel

theorem rows22240R_3433 : rowsJ2 119 120 89 91 ≤ 13381271465647 := by decide +kernel

theorem rows22240R_3434 : rowsJ2 119 120 91 93 ≤ 18472083070340 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3418
#print axioms SieveCert.rows22240R_3434
