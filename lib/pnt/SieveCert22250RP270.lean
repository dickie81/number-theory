/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3503–3518 of 4715

File 270 of 351: the parts `rows22250R_3503` … `rows22250R_3518` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 98025 in units of a depth-4 test: row 131 columns 72–72, row 131
columns 73–73, row 131 columns 74–74, row 131 columns 75–76, row 131 columns 77–78, row 131 columns 79–81, row 131
columns 82–85, row 131 columns 86–339, row 132 columns 0–23, row 132 columns 24–30, row 132 columns 31–51, row 132
columns 52–54, row 132 columns 55–56, row 132 columns 57–57, row 132 columns 58–58, row 132 columns 59–59), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3503 : rowsJ2 131 132 72 73 ≤ 4537556901938 := by decide +kernel

theorem rows22250R_3504 : rowsJ2 131 132 73 74 ≤ 3917101290099 := by decide +kernel

theorem rows22250R_3505 : rowsJ2 131 132 74 75 ≤ 3335739591879 := by decide +kernel

theorem rows22250R_3506 : rowsJ2 131 132 75 77 ≤ 5147968805619 := by decide +kernel

theorem rows22250R_3507 : rowsJ2 131 132 77 79 ≤ 3425689146683 := by decide +kernel

theorem rows22250R_3508 : rowsJ2 131 132 79 82 ≤ 2708098338130 := by decide +kernel

theorem rows22250R_3509 : rowsJ2 131 132 82 86 ≤ 10857658046194 := by decide +kernel

theorem rows22250R_3510 : rowsJ2 131 132 86 340 ≤ 722264078778266 := by decide +kernel

theorem rows22250R_3511 : rowsJ2 132 133 0 24 ≤ 4398315604652 := by decide +kernel

theorem rows22250R_3512 : rowsJ2 132 133 24 31 ≤ 11538689473378 := by decide +kernel

theorem rows22250R_3513 : rowsJ2 132 133 31 52 ≤ 2578915794319 := by decide +kernel

theorem rows22250R_3514 : rowsJ2 132 133 52 55 ≤ 5613033555884 := by decide +kernel

theorem rows22250R_3515 : rowsJ2 132 133 55 57 ≤ 6364344282660 := by decide +kernel

theorem rows22250R_3516 : rowsJ2 132 133 57 58 ≤ 4109843097030 := by decide +kernel

theorem rows22250R_3517 : rowsJ2 132 133 58 59 ≤ 4786290541946 := by decide +kernel

theorem rows22250R_3518 : rowsJ2 132 133 59 60 ≤ 5504021990534 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3503
#print axioms SieveCert.rows22250R_3518
