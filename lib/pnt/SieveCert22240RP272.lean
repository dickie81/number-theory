/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3360–3373 of 5066

File 272 of 387: the parts `rows22240R_3360` … `rows22240R_3373` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 94119 in units of a depth-4 test: row 117 columns 30–31, row 117
columns 32–33, row 117 columns 34–35, row 117 columns 36–38, row 117 columns 39–42, row 117 columns 43–51, row 117
columns 52–60, row 117 columns 61–62, row 117 columns 63–64, row 117 columns 65–66, row 117 columns 67–68, row 117
columns 69–70, row 117 columns 71–72, row 117 columns 73–75), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3360 : rowsJ2 117 118 30 32 ≤ 13630891988008 := by decide +kernel

theorem rows22240R_3361 : rowsJ2 117 118 32 34 ≤ 20798060803645 := by decide +kernel

theorem rows22240R_3362 : rowsJ2 117 118 34 36 ≤ 18180268916109 := by decide +kernel

theorem rows22240R_3363 : rowsJ2 117 118 36 39 ≤ 19116858868835 := by decide +kernel

theorem rows22240R_3364 : rowsJ2 117 118 39 43 ≤ 9252415700298 := by decide +kernel

theorem rows22240R_3365 : rowsJ2 117 118 43 52 ≤ 1120262276139 := by decide +kernel

theorem rows22240R_3366 : rowsJ2 117 118 52 61 ≤ 3080053212120 := by decide +kernel

theorem rows22240R_3367 : rowsJ2 117 118 61 63 ≤ 3214995080909 := by decide +kernel

theorem rows22240R_3368 : rowsJ2 117 118 63 65 ≤ 4079783003221 := by decide +kernel

theorem rows22240R_3369 : rowsJ2 117 118 65 67 ≤ 4444940312700 := by decide +kernel

theorem rows22240R_3370 : rowsJ2 117 118 67 69 ≤ 4295456567341 := by decide +kernel

theorem rows22240R_3371 : rowsJ2 117 118 69 71 ≤ 3611622542450 := by decide +kernel

theorem rows22240R_3372 : rowsJ2 117 118 71 73 ≤ 2367348739953 := by decide +kernel

theorem rows22240R_3373 : rowsJ2 117 118 73 76 ≤ 530144140703 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3360
#print axioms SieveCert.rows22240R_3373
