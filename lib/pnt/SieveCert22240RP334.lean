/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4239–4250 of 5066

File 334 of 387: the parts `rows22240R_4239` … `rows22240R_4250` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 98843 in units of a depth-4 test: row 148 columns 53–53, row 148
columns 54–54, row 148 columns 55–55, row 148 columns 56–56, row 148 columns 57–57, row 148 columns 58–58, row 148
columns 59–59, row 148 columns 60–60, row 148 columns 61–61, row 148 columns 62–62, row 148 columns 63–63, row 148
columns 64–64), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22240R_4239 : rowsJ2 148 149 53 54 ≤ 8514345725646 := by decide +kernel

theorem rows22240R_4240 : rowsJ2 148 149 54 55 ≤ 9546595208182 := by decide +kernel

theorem rows22240R_4241 : rowsJ2 148 149 55 56 ≤ 10623694775099 := by decide +kernel

theorem rows22240R_4242 : rowsJ2 148 149 56 57 ≤ 11744079276468 := by decide +kernel

theorem rows22240R_4243 : rowsJ2 148 149 57 58 ≤ 12906279676337 := by decide +kernel

theorem rows22240R_4244 : rowsJ2 148 149 58 59 ≤ 14108955247162 := by decide +kernel

theorem rows22240R_4245 : rowsJ2 148 149 59 60 ≤ 15350846050452 := by decide +kernel

theorem rows22240R_4246 : rowsJ2 148 149 60 61 ≤ 13844651915137 := by decide +kernel

theorem rows22240R_4247 : rowsJ2 148 149 61 62 ≤ 12427348907832 := by decide +kernel

theorem rows22240R_4248 : rowsJ2 148 149 62 63 ≤ 11096492019196 := by decide +kernel

theorem rows22240R_4249 : rowsJ2 148 149 63 64 ≤ 9849802839891 := by decide +kernel

theorem rows22240R_4250 : rowsJ2 148 149 64 65 ≤ 8685156321983 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4239
#print axioms SieveCert.rows22240R_4250
