/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3451–3466 of 5066

File 278 of 387: the parts `rows22240R_3451` … `rows22240R_3466` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 99707 in units of a depth-4 test: row 120 columns 68–68, row 120
columns 69–69, row 120 columns 70–70, row 120 columns 71–71, row 120 columns 72–72, row 120 columns 73–74, row 120
columns 75–77, row 120 columns 78–81, row 120 columns 82–84, row 120 columns 85–87, row 120 columns 88–89, row 120
columns 90–91, row 120 columns 92–93, row 120 columns 94–339, row 121 columns 0–25, row 121 columns 26–29), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3451 : rowsJ2 120 121 68 69 ≤ 3379116080183 := by decide +kernel

theorem rows22240R_3452 : rowsJ2 120 121 69 70 ≤ 3288986947806 := by decide +kernel

theorem rows22240R_3453 : rowsJ2 120 121 70 71 ≤ 3142852573141 := by decide +kernel

theorem rows22240R_3454 : rowsJ2 120 121 71 72 ≤ 2915235843504 := by decide +kernel

theorem rows22240R_3455 : rowsJ2 120 121 72 73 ≤ 2628093116523 := by decide +kernel

theorem rows22240R_3456 : rowsJ2 120 121 73 75 ≤ 3878894578140 := by decide +kernel

theorem rows22240R_3457 : rowsJ2 120 121 75 78 ≤ 1527286976209 := by decide +kernel

theorem rows22240R_3458 : rowsJ2 120 121 78 82 ≤ 369429377255 := by decide +kernel

theorem rows22240R_3459 : rowsJ2 120 121 82 85 ≤ 4087871835525 := by decide +kernel

theorem rows22240R_3460 : rowsJ2 120 121 85 88 ≤ 10523335612118 := by decide +kernel

theorem rows22240R_3461 : rowsJ2 120 121 88 90 ≤ 11877309257102 := by decide +kernel

theorem rows22240R_3462 : rowsJ2 120 121 90 92 ≤ 16755273396996 := by decide +kernel

theorem rows22240R_3463 : rowsJ2 120 121 92 94 ≤ 22547844069857 := by decide +kernel

theorem rows22240R_3464 : rowsJ2 120 121 94 340 ≤ 1319391365887862 := by decide +kernel

theorem rows22240R_3465 : rowsJ2 121 122 0 26 ≤ 838250747356 := by decide +kernel

theorem rows22240R_3466 : rowsJ2 121 122 26 30 ≤ 15622685501530 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3451
#print axioms SieveCert.rows22240R_3466
