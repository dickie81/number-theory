/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3589–3603 of 4715

File 276 of 351: the parts `rows22250R_3589` … `rows22250R_3603` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 95325 tests: row 134 columns 74–75, row 134 columns 76–77, row 134 columns
78–80, row 134 columns 81–85, row 134 columns 86–339, row 135 columns 0–23, row 135 columns 24–46, row 135 columns
47–52, row 135 columns 53–54, row 135 columns 55–55, row 135 columns 56–56, row 135 columns 57–57, row 135 columns
58–58, row 135 columns 59–59, row 135 columns 60–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_3589 : rowsJ2 134 135 74 76 ≤ 5965590508688 := by decide +kernel

theorem rows22250R_3590 : rowsJ2 134 135 76 78 ≤ 4048259118795 := by decide +kernel

theorem rows22250R_3591 : rowsJ2 134 135 78 81 ≤ 3289810167157 := by decide +kernel

theorem rows22250R_3592 : rowsJ2 134 135 81 86 ≤ 12820965551339 := by decide +kernel

theorem rows22250R_3593 : rowsJ2 134 135 86 340 ≤ 538428832972036 := by decide +kernel

theorem rows22250R_3594 : rowsJ2 135 136 0 24 ≤ 6239791501004 := by decide +kernel

theorem rows22250R_3595 : rowsJ2 135 136 24 47 ≤ 4201367279493 := by decide +kernel

theorem rows22250R_3596 : rowsJ2 135 136 47 53 ≤ 7023357177664 := by decide +kernel

theorem rows22250R_3597 : rowsJ2 135 136 53 55 ≤ 6077328293635 := by decide +kernel

theorem rows22250R_3598 : rowsJ2 135 136 55 56 ≤ 3973205049233 := by decide +kernel

theorem rows22250R_3599 : rowsJ2 135 136 56 57 ≤ 4657950723235 := by decide +kernel

theorem rows22250R_3600 : rowsJ2 135 136 57 58 ≤ 5386565442634 := by decide +kernel

theorem rows22250R_3601 : rowsJ2 135 136 58 59 ≤ 6157281893913 := by decide +kernel

theorem rows22250R_3602 : rowsJ2 135 136 59 60 ≤ 6968464143470 := by decide +kernel

theorem rows22250R_3603 : rowsJ2 135 136 60 61 ≤ 7797390545101 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3589
#print axioms SieveCert.rows22250R_3603
