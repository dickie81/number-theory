/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3896–3912 of 5796

File 329 of 465: the parts `rows22250R_3896` … `rows22250R_3912` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 96242 tests: row 126 columns 67–67, row 126 columns 68–68, row 126 columns
69–69, row 126 columns 70–70, row 126 columns 71–71, row 126 columns 72–72, row 126 columns 73–73, row 126 columns
74–74, row 126 columns 75–76, row 126 columns 77–78, row 126 columns 79–81, row 126 columns 82–84, row 126 columns
85–87, row 126 columns 88–90, row 126 columns 91–92, row 126 columns 93–94, row 126 columns 95–96), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3896 : rowsJ2 126 127 67 68 ≤ 2334049005423 := by decide +kernel

theorem rows22250R_3897 : rowsJ2 126 127 68 69 ≤ 2446825093559 := by decide +kernel

theorem rows22250R_3898 : rowsJ2 126 127 69 70 ≤ 2498923685817 := by decide +kernel

theorem rows22250R_3899 : rowsJ2 126 127 70 71 ≤ 2508417080300 := by decide +kernel

theorem rows22250R_3900 : rowsJ2 126 127 71 72 ≤ 2455321183034 := by decide +kernel

theorem rows22250R_3901 : rowsJ2 126 127 72 73 ≤ 2357675927895 := by decide +kernel

theorem rows22250R_3902 : rowsJ2 126 127 73 74 ≤ 2195048164438 := by decide +kernel

theorem rows22250R_3903 : rowsJ2 126 127 74 75 ≤ 1985426975475 := by decide +kernel

theorem rows22250R_3904 : rowsJ2 126 127 75 77 ≤ 3088211831395 := by decide +kernel

theorem rows22250R_3905 : rowsJ2 126 127 77 79 ≤ 1457022360142 := by decide +kernel

theorem rows22250R_3906 : rowsJ2 126 127 79 82 ≤ 0 := by decide +kernel

theorem rows22250R_3907 : rowsJ2 126 127 82 85 ≤ 0 := by decide +kernel

theorem rows22250R_3908 : rowsJ2 126 127 85 88 ≤ 341867587752 := by decide +kernel

theorem rows22250R_3909 : rowsJ2 126 127 88 91 ≤ 3700492865299 := by decide +kernel

theorem rows22250R_3910 : rowsJ2 126 127 91 93 ≤ 5454463888995 := by decide +kernel

theorem rows22250R_3911 : rowsJ2 126 127 93 95 ≤ 8569699334869 := by decide +kernel

theorem rows22250R_3912 : rowsJ2 126 127 95 97 ≤ 12352894694547 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3896
#print axioms SieveCert.rows22250R_3912
