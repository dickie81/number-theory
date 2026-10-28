/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3905–3919 of 5066

File 309 of 387: the parts `rows22240R_3905` … `rows22240R_3919` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 95251 in units of a depth-4 test: row 135 columns 78–79, row 135
columns 80–82, row 135 columns 83–86, row 135 columns 87–339, row 136 columns 0–23, row 136 columns 24–32, row 136
columns 33–51, row 136 columns 52–53, row 136 columns 54–55, row 136 columns 56–56, row 136 columns 57–57, row 136
columns 58–58, row 136 columns 59–59, row 136 columns 60–60, row 136 columns 61–61), each a sum of refined costs
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

theorem rows22240R_3905 : rowsJ2 135 136 78 80 ≤ 3394154744949 := by decide +kernel

theorem rows22240R_3906 : rowsJ2 135 136 80 83 ≤ 5632243737880 := by decide +kernel

theorem rows22240R_3907 : rowsJ2 135 136 83 87 ≤ 23393221143600 := by decide +kernel

theorem rows22240R_3908 : rowsJ2 135 136 87 340 ≤ 525017762970334 := by decide +kernel

theorem rows22240R_3909 : rowsJ2 136 137 0 24 ≤ 5525621471561 := by decide +kernel

theorem rows22240R_3910 : rowsJ2 136 137 24 33 ≤ 8596561833817 := by decide +kernel

theorem rows22240R_3911 : rowsJ2 136 137 33 52 ≤ 5048986579473 := by decide +kernel

theorem rows22240R_3912 : rowsJ2 136 137 52 54 ≤ 4980315907927 := by decide +kernel

theorem rows22240R_3913 : rowsJ2 136 137 54 56 ≤ 7359696043259 := by decide +kernel

theorem rows22240R_3914 : rowsJ2 136 137 56 57 ≤ 4691550732313 := by decide +kernel

theorem rows22240R_3915 : rowsJ2 136 137 57 58 ≤ 5425669921712 := by decide +kernel

theorem rows22240R_3916 : rowsJ2 136 137 58 59 ≤ 6202233992276 := by decide +kernel

theorem rows22240R_3917 : rowsJ2 136 137 59 60 ≤ 7019523400550 := by decide +kernel

theorem rows22240R_3918 : rowsJ2 136 137 60 61 ≤ 7875937106155 := by decide +kernel

theorem rows22240R_3919 : rowsJ2 136 137 61 62 ≤ 8749499798631 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3905
#print axioms SieveCert.rows22240R_3919
