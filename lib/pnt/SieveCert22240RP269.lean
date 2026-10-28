/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3314–3329 of 5066

File 269 of 387: the parts `rows22240R_3314` … `rows22240R_3329` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 99926 in units of a depth-4 test: row 115 columns 47–57, row 115
columns 58–62, row 115 columns 63–64, row 115 columns 65–66, row 115 columns 67–68, row 115 columns 69–71, row 115
columns 72–74, row 115 columns 75–77, row 115 columns 78–80, row 115 columns 81–83, row 115 columns 84–86, row 115
columns 87–88, row 115 columns 89–90, row 115 columns 91–92, row 115 columns 93–93, row 115 columns 94–94), each a
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

theorem rows22240R_3314 : rowsJ2 115 116 47 58 ≤ 224376222924 := by decide +kernel

theorem rows22240R_3315 : rowsJ2 115 116 58 63 ≤ 4065894898872 := by decide +kernel

theorem rows22240R_3316 : rowsJ2 115 116 63 65 ≤ 3046019960200 := by decide +kernel

theorem rows22240R_3317 : rowsJ2 115 116 65 67 ≤ 3195048634241 := by decide +kernel

theorem rows22240R_3318 : rowsJ2 115 116 67 69 ≤ 2824669507707 := by decide +kernel

theorem rows22240R_3319 : rowsJ2 115 116 69 72 ≤ 2350738904898 := by decide +kernel

theorem rows22240R_3320 : rowsJ2 115 116 72 75 ≤ 0 := by decide +kernel

theorem rows22240R_3321 : rowsJ2 115 116 75 78 ≤ 12705010073 := by decide +kernel

theorem rows22240R_3322 : rowsJ2 115 116 78 81 ≤ 0 := by decide +kernel

theorem rows22240R_3323 : rowsJ2 115 116 81 84 ≤ 1521976785588 := by decide +kernel

theorem rows22240R_3324 : rowsJ2 115 116 84 87 ≤ 5504412346756 := by decide +kernel

theorem rows22240R_3325 : rowsJ2 115 116 87 89 ≤ 6977455658065 := by decide +kernel

theorem rows22240R_3326 : rowsJ2 115 116 89 91 ≤ 10454722779170 := by decide +kernel

theorem rows22240R_3327 : rowsJ2 115 116 91 93 ≤ 14690669460048 := by decide +kernel

theorem rows22240R_3328 : rowsJ2 115 116 93 94 ≤ 9177792793998 := by decide +kernel

theorem rows22240R_3329 : rowsJ2 115 116 94 95 ≤ 10558829916734 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3314
#print axioms SieveCert.rows22240R_3329
