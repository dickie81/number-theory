/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 901–912 of 5066

File 90 of 387: the parts `rows22240R_901` … `rows22240R_912` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 95095 in units of a depth-4 test: row 60 columns 21–22, row 60 columns
23–23, row 60 columns 24–24, row 60 columns 25–25, row 60 columns 26–26, row 60 columns 27–27, row 60 columns 28–28,
row 60 columns 29–29, row 60 columns 30–30, row 60 columns 31–31, row 60 columns 32–32, row 60 columns 33–33), each
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

theorem rows22240R_901 : rowsJ2 60 61 21 23 ≤ 225537710701 := by decide +kernel

theorem rows22240R_902 : rowsJ2 60 61 23 24 ≤ 81839470724 := by decide +kernel

theorem rows22240R_903 : rowsJ2 60 61 24 25 ≤ 65344020039 := by decide +kernel

theorem rows22240R_904 : rowsJ2 60 61 25 26 ≤ 49013223737 := by decide +kernel

theorem rows22240R_905 : rowsJ2 60 61 26 27 ≤ 36702867663 := by decide +kernel

theorem rows22240R_906 : rowsJ2 60 61 27 28 ≤ 24495561294 := by decide +kernel

theorem rows22240R_907 : rowsJ2 60 61 28 29 ≤ 16306504983 := by decide +kernel

theorem rows22240R_908 : rowsJ2 60 61 29 30 ≤ 8172813382 := by decide +kernel

theorem rows22240R_909 : rowsJ2 60 61 30 31 ≤ 4075869091 := by decide +kernel

theorem rows22240R_910 : rowsJ2 60 61 31 32 ≤ 0 := by decide +kernel

theorem rows22240R_911 : rowsJ2 60 61 32 33 ≤ 0 := by decide +kernel

theorem rows22240R_912 : rowsJ2 60 61 33 34 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_901
#print axioms SieveCert.rows22240R_912
