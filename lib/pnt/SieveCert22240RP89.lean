/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 893–900 of 5066

File 89 of 387: the parts `rows22240R_893` … `rows22240R_900` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (8 parts, work 95153 in units of a depth-4 test: row 59 columns 54–54, row 59 columns
55–55, row 59 columns 56–56, row 59 columns 57–57, row 59 columns 58–58, row 59 columns 59–339, row 60 columns 0–15,
row 60 columns 16–20), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_893 : rowsJ2 59 60 54 55 ≤ 8738844418222 := by decide +kernel

theorem rows22240R_894 : rowsJ2 59 60 55 56 ≤ 10084742476757 := by decide +kernel

theorem rows22240R_895 : rowsJ2 59 60 56 57 ≤ 11494509809869 := by decide +kernel

theorem rows22240R_896 : rowsJ2 59 60 57 58 ≤ 12724349288610 := by decide +kernel

theorem rows22240R_897 : rowsJ2 59 60 58 59 ≤ 13725502846449 := by decide +kernel

theorem rows22240R_898 : rowsJ2 59 60 59 340 ≤ 14760545939143 := by decide +kernel

theorem rows22240R_899 : rowsJ2 60 61 0 16 ≤ 2706372413510 := by decide +kernel

theorem rows22240R_900 : rowsJ2 60 61 16 21 ≤ 1038071149929 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_893
#print axioms SieveCert.rows22240R_900
