/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 858–869 of 5066

File 86 of 387: the parts `rows22240R_858` … `rows22240R_869` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 95218 in units of a depth-4 test: row 58 columns 58–339, row 59 columns
0–15, row 59 columns 16–20, row 59 columns 21–22, row 59 columns 23–23, row 59 columns 24–24, row 59 columns 25–25,
row 59 columns 26–26, row 59 columns 27–27, row 59 columns 28–28, row 59 columns 29–29, row 59 columns 30–30), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22240R_858 : rowsJ2 58 59 58 340 ≤ 14203255846942 := by decide +kernel

theorem rows22240R_859 : rowsJ2 59 60 0 16 ≤ 2793096717844 := by decide +kernel

theorem rows22240R_860 : rowsJ2 59 60 16 21 ≤ 1196926142374 := by decide +kernel

theorem rows22240R_861 : rowsJ2 59 60 21 23 ≤ 269733946266 := by decide +kernel

theorem rows22240R_862 : rowsJ2 59 60 23 24 ≤ 101863746589 := by decide +kernel

theorem rows22240R_863 : rowsJ2 59 60 24 25 ≤ 81444618012 := by decide +kernel

theorem rows22240R_864 : rowsJ2 59 60 25 26 ≤ 65041790049 := by decide +kernel

theorem rows22240R_865 : rowsJ2 59 60 26 27 ≤ 48796036466 := by decide +kernel

theorem rows22240R_866 : rowsJ2 59 60 27 28 ≤ 36547157479 := by decide +kernel

theorem rows22240R_867 : rowsJ2 59 60 28 29 ≤ 24396139526 := by decide +kernel

theorem rows22240R_868 : rowsJ2 59 60 29 30 ≤ 16243236748 := by decide +kernel

theorem rows22240R_869 : rowsJ2 59 60 30 31 ≤ 8142526752 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_858
#print axioms SieveCert.rows22240R_869
