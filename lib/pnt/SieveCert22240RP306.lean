/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3864–3876 of 5066

File 306 of 387: the parts `rows22240R_3864` … `rows22240R_3876` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 94043 in units of a depth-4 test: row 134 columns 66–66, row 134
columns 67–67, row 134 columns 68–68, row 134 columns 69–69, row 134 columns 70–70, row 134 columns 71–71, row 134
columns 72–72, row 134 columns 73–73, row 134 columns 74–74, row 134 columns 75–75, row 134 columns 76–77, row 134
columns 78–79, row 134 columns 80–82), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22240R_3864 : rowsJ2 134 135 66 67 ≤ 10861555733093 := by decide +kernel

theorem rows22240R_3865 : rowsJ2 134 135 67 68 ≤ 9810932776121 := by decide +kernel

theorem rows22240R_3866 : rowsJ2 134 135 68 69 ≤ 8832812012573 := by decide +kernel

theorem rows22240R_3867 : rowsJ2 134 135 69 70 ≤ 7903726386683 := by decide +kernel

theorem rows22240R_3868 : rowsJ2 134 135 70 71 ≤ 7043638834168 := by decide +kernel

theorem rows22240R_3869 : rowsJ2 134 135 71 72 ≤ 6229014772883 := by decide +kernel

theorem rows22240R_3870 : rowsJ2 134 135 72 73 ≤ 5480279776514 := by decide +kernel

theorem rows22240R_3871 : rowsJ2 134 135 73 74 ≤ 4773789572004 := by decide +kernel

theorem rows22240R_3872 : rowsJ2 134 135 74 75 ≤ 4130421703361 := by decide +kernel

theorem rows22240R_3873 : rowsJ2 134 135 75 76 ≤ 3526401122194 := by decide +kernel

theorem rows22240R_3874 : rowsJ2 134 135 76 78 ≤ 5459536335614 := by decide +kernel

theorem rows22240R_3875 : rowsJ2 134 135 78 80 ≤ 3643158382526 := by decide +kernel

theorem rows22240R_3876 : rowsJ2 134 135 80 83 ≤ 5863716496054 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3864
#print axioms SieveCert.rows22240R_3876
