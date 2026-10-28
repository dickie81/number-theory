/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4178–4192 of 4715

File 318 of 351: the parts `rows22250R_4178` … `rows22250R_4192` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 96398 in units of a depth-4 test: row 159 columns 44–45, row 159
columns 46–46, row 159 columns 47–47, row 159 columns 48–48, row 159 columns 49–49, row 159 columns 50–50, row 159
columns 51–51, row 159 columns 52–52, row 159 columns 53–53, row 159 columns 54–54, row 159 columns 55–55, row 159
columns 56–56, row 159 columns 57–57, row 159 columns 58–58, row 159 columns 59–59), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4178 : rowsJ2 159 160 44 46 ≤ 15134297673137 := by decide +kernel

theorem rows22250R_4179 : rowsJ2 159 160 46 47 ≤ 9255425968886 := by decide +kernel

theorem rows22250R_4180 : rowsJ2 159 160 47 48 ≤ 10458980176501 := by decide +kernel

theorem rows22250R_4181 : rowsJ2 159 160 48 49 ≤ 11718191121134 := by decide +kernel

theorem rows22250R_4182 : rowsJ2 159 160 49 50 ≤ 13031024137084 := by decide +kernel

theorem rows22250R_4183 : rowsJ2 159 160 50 51 ≤ 14395649186450 := by decide +kernel

theorem rows22250R_4184 : rowsJ2 159 160 51 52 ≤ 15810430751630 := by decide +kernel

theorem rows22250R_4185 : rowsJ2 159 160 52 53 ≤ 17273918840650 := by decide +kernel

theorem rows22250R_4186 : rowsJ2 159 160 53 54 ≤ 17101235163885 := by decide +kernel

theorem rows22250R_4187 : rowsJ2 159 160 54 55 ≤ 15340963419385 := by decide +kernel

theorem rows22250R_4188 : rowsJ2 159 160 55 56 ≤ 13690202438016 := by decide +kernel

theorem rows22250R_4189 : rowsJ2 159 160 56 57 ≤ 12145696866696 := by decide +kernel

theorem rows22250R_4190 : rowsJ2 159 160 57 58 ≤ 10704430243242 := by decide +kernel

theorem rows22250R_4191 : rowsJ2 159 160 58 59 ≤ 9363612845122 := by decide +kernel

theorem rows22250R_4192 : rowsJ2 159 160 59 60 ≤ 8120670692779 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4178
#print axioms SieveCert.rows22250R_4192
