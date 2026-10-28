/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3484–3498 of 5066

File 280 of 387: the parts `rows22240R_3484` … `rows22240R_3498` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 95483 in units of a depth-4 test: row 121 columns 73–73, row 121
columns 74–75, row 121 columns 76–78, row 121 columns 79–82, row 121 columns 83–85, row 121 columns 86–88, row 121
columns 89–90, row 121 columns 91–92, row 121 columns 93–98, row 121 columns 99–339, row 122 columns 0–25, row 122
columns 26–28, row 122 columns 29–30, row 122 columns 31–33, row 122 columns 34–37), each a sum of refined costs
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

theorem rows22240R_3484 : rowsJ2 121 122 73 74 ≤ 2698525308463 := by decide +kernel

theorem rows22240R_3485 : rowsJ2 121 122 74 76 ≤ 3536987985651 := by decide +kernel

theorem rows22240R_3486 : rowsJ2 121 122 76 79 ≤ 1376892386392 := by decide +kernel

theorem rows22240R_3487 : rowsJ2 121 122 79 83 ≤ 1245137020856 := by decide +kernel

theorem rows22240R_3488 : rowsJ2 121 122 83 86 ≤ 6352742755462 := by decide +kernel

theorem rows22240R_3489 : rowsJ2 121 122 86 89 ≤ 14053643150804 := by decide +kernel

theorem rows22240R_3490 : rowsJ2 121 122 89 91 ≤ 15015124373726 := by decide +kernel

theorem rows22240R_3491 : rowsJ2 121 122 91 93 ≤ 20588558222888 := by decide +kernel

theorem rows22240R_3492 : rowsJ2 121 122 93 99 ≤ 415271525619003 := by decide +kernel

theorem rows22240R_3493 : rowsJ2 121 122 99 340 ≤ 811066248846424 := by decide +kernel

theorem rows22240R_3494 : rowsJ2 122 123 0 26 ≤ 1332506096299 := by decide +kernel

theorem rows22240R_3495 : rowsJ2 122 123 26 29 ≤ 10627583240484 := by decide +kernel

theorem rows22240R_3496 : rowsJ2 122 123 29 31 ≤ 15513010253116 := by decide +kernel

theorem rows22240R_3497 : rowsJ2 122 123 31 34 ≤ 20244367939749 := by decide +kernel

theorem rows22240R_3498 : rowsJ2 122 123 34 38 ≤ 15344838151018 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3484
#print axioms SieveCert.rows22240R_3498
