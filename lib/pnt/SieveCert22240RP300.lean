/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3780–3794 of 5066

File 300 of 387: the parts `rows22240R_3780` … `rows22240R_3794` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 99136 in units of a depth-4 test: row 131 columns 72–72, row 131
columns 73–73, row 131 columns 74–74, row 131 columns 75–75, row 131 columns 76–76, row 131 columns 77–78, row 131
columns 79–80, row 131 columns 81–83, row 131 columns 84–86, row 131 columns 87–339, row 132 columns 0–24, row 132
columns 25–29, row 132 columns 30–48, row 132 columns 49–54, row 132 columns 55–56), each a sum of refined costs
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

theorem rows22240R_3780 : rowsJ2 131 132 72 73 ≤ 5587810139055 := by decide +kernel

theorem rows22240R_3781 : rowsJ2 131 132 73 74 ≤ 4883210959419 := by decide +kernel

theorem rows22240R_3782 : rowsJ2 131 132 74 75 ≤ 4241848621232 := by decide +kernel

theorem rows22240R_3783 : rowsJ2 131 132 75 76 ≤ 3639556098033 := by decide +kernel

theorem rows22240R_3784 : rowsJ2 131 132 76 77 ≤ 3098049093331 := by decide +kernel

theorem rows22240R_3785 : rowsJ2 131 132 77 79 ≤ 4739546192714 := by decide +kernel

theorem rows22240R_3786 : rowsJ2 131 132 79 81 ≤ 3112830390166 := by decide +kernel

theorem rows22240R_3787 : rowsJ2 131 132 81 84 ≤ 7618221962183 := by decide +kernel

theorem rows22240R_3788 : rowsJ2 131 132 84 87 ≤ 16363667793693 := by decide +kernel

theorem rows22240R_3789 : rowsJ2 131 132 87 340 ≤ 715017160488588 := by decide +kernel

theorem rows22240R_3790 : rowsJ2 132 133 0 25 ≤ 5323538008894 := by decide +kernel

theorem rows22240R_3791 : rowsJ2 132 133 25 30 ≤ 15735319852630 := by decide +kernel

theorem rows22240R_3792 : rowsJ2 132 133 30 49 ≤ 4018521828550 := by decide +kernel

theorem rows22240R_3793 : rowsJ2 132 133 49 55 ≤ 6647076890897 := by decide +kernel

theorem rows22240R_3794 : rowsJ2 132 133 55 57 ≤ 5757416241892 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3780
#print axioms SieveCert.rows22240R_3794
