/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2944–2959 of 4715

File 233 of 351: the parts `rows22250R_2944` … `rows22250R_2959` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 96515 in units of a depth-4 test: row 109 columns 61–67, row 109
columns 68–72, row 109 columns 73–75, row 109 columns 76–77, row 109 columns 78–79, row 109 columns 80–82, row 109
columns 83–85, row 109 columns 86–88, row 109 columns 89–90, row 109 columns 91–92, row 109 columns 93–94, row 109
columns 95–95, row 109 columns 96–96, row 109 columns 97–97, row 109 columns 98–98, row 109 columns 99–339), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2944 : rowsJ2 109 110 61 68 ≤ 650787795467 := by decide +kernel

theorem rows22250R_2945 : rowsJ2 109 110 68 73 ≤ 0 := by decide +kernel

theorem rows22250R_2946 : rowsJ2 109 110 73 76 ≤ 14643199868 := by decide +kernel

theorem rows22250R_2947 : rowsJ2 109 110 76 78 ≤ 318513720725 := by decide +kernel

theorem rows22250R_2948 : rowsJ2 109 110 78 80 ≤ 521382750853 := by decide +kernel

theorem rows22250R_2949 : rowsJ2 109 110 80 83 ≤ 492312331655 := by decide +kernel

theorem rows22250R_2950 : rowsJ2 109 110 83 86 ≤ 1548764365801 := by decide +kernel

theorem rows22250R_2951 : rowsJ2 109 110 86 89 ≤ 4786631492271 := by decide +kernel

theorem rows22250R_2952 : rowsJ2 109 110 89 91 ≤ 6069797087519 := by decide +kernel

theorem rows22250R_2953 : rowsJ2 109 110 91 93 ≤ 9143923898816 := by decide +kernel

theorem rows22250R_2954 : rowsJ2 109 110 93 95 ≤ 12918605144116 := by decide +kernel

theorem rows22250R_2955 : rowsJ2 109 110 95 96 ≤ 8098861567838 := by decide +kernel

theorem rows22250R_2956 : rowsJ2 109 110 96 97 ≤ 9338954801763 := by decide +kernel

theorem rows22250R_2957 : rowsJ2 109 110 97 98 ≤ 10653019450023 := by decide +kernel

theorem rows22250R_2958 : rowsJ2 109 110 98 99 ≤ 12099148007980 := by decide +kernel

theorem rows22250R_2959 : rowsJ2 109 110 99 340 ≤ 1109806121938191 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2944
#print axioms SieveCert.rows22250R_2959
