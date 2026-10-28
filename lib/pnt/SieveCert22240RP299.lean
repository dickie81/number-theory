/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3768–3779 of 5066

File 299 of 387: the parts `rows22240R_3768` … `rows22240R_3779` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 95750 in units of a depth-4 test: row 131 columns 60–60, row 131
columns 61–61, row 131 columns 62–62, row 131 columns 63–63, row 131 columns 64–64, row 131 columns 65–65, row 131
columns 66–66, row 131 columns 67–67, row 131 columns 68–68, row 131 columns 69–69, row 131 columns 70–70, row 131
columns 71–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22240R_3768 : rowsJ2 131 132 60 61 ≤ 5382331102336 := by decide +kernel

theorem rows22240R_3769 : rowsJ2 131 132 61 62 ≤ 6102620649200 := by decide +kernel

theorem rows22240R_3770 : rowsJ2 131 132 62 63 ≤ 6776530247523 := by decide +kernel

theorem rows22240R_3771 : rowsJ2 131 132 63 64 ≤ 7382442431947 := by decide +kernel

theorem rows22240R_3772 : rowsJ2 131 132 64 65 ≤ 7941265092862 := by decide +kernel

theorem rows22240R_3773 : rowsJ2 131 132 65 66 ≤ 8430987107216 := by decide +kernel

theorem rows22240R_3774 : rowsJ2 131 132 66 67 ≤ 8872578308207 := by decide +kernel

theorem rows22240R_3775 : rowsJ2 131 132 67 68 ≤ 9243560905326 := by decide +kernel

theorem rows22240R_3776 : rowsJ2 131 132 68 69 ≤ 8931623992999 := by decide +kernel

theorem rows22240R_3777 : rowsJ2 131 132 69 70 ≤ 8004724773568 := by decide +kernel

theorem rows22240R_3778 : rowsJ2 131 132 70 71 ≤ 7146953204629 := by decide +kernel

theorem rows22240R_3779 : rowsJ2 131 132 71 72 ≤ 6334380598342 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3768
#print axioms SieveCert.rows22240R_3779
