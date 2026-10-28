/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3892–3904 of 5066

File 308 of 387: the parts `rows22240R_3892` … `rows22240R_3904` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 99421 in units of a depth-4 test: row 135 columns 64–64, row 135
columns 65–65, row 135 columns 66–66, row 135 columns 67–67, row 135 columns 68–68, row 135 columns 69–69, row 135
columns 70–70, row 135 columns 71–71, row 135 columns 72–72, row 135 columns 73–73, row 135 columns 74–74, row 135
columns 75–75, row 135 columns 76–77), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3892 : rowsJ2 135 136 64 65 ≤ 10377390404245 := by decide +kernel

theorem rows22240R_3893 : rowsJ2 135 136 65 66 ≤ 10995117988865 := by decide +kernel

theorem rows22240R_3894 : rowsJ2 135 136 66 67 ≤ 10743787251734 := by decide +kernel

theorem rows22240R_3895 : rowsJ2 135 136 67 68 ≤ 9692536002845 := by decide +kernel

theorem rows22240R_3896 : rowsJ2 135 136 68 69 ≤ 8713736698143 := by decide +kernel

theorem rows22240R_3897 : rowsJ2 135 136 69 70 ≤ 7784055490248 := by decide +kernel

theorem rows22240R_3898 : rowsJ2 135 136 70 71 ≤ 6923329736487 := by decide +kernel

theorem rows22240R_3899 : rowsJ2 135 136 71 72 ≤ 6108153133518 := by decide +kernel

theorem rows22240R_3900 : rowsJ2 135 136 72 73 ≤ 5358820668250 := by decide +kernel

theorem rows22240R_3901 : rowsJ2 135 136 73 74 ≤ 4651816460713 := by decide +kernel

theorem rows22240R_3902 : rowsJ2 135 136 74 75 ≤ 4007896642808 := by decide +kernel

theorem rows22240R_3903 : rowsJ2 135 136 75 76 ≤ 3403415425021 := by decide +kernel

theorem rows22240R_3904 : rowsJ2 135 136 76 78 ≤ 5212168030882 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3892
#print axioms SieveCert.rows22240R_3904
