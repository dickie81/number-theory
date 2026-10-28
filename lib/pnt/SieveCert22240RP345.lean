/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4393–4407 of 5066

File 345 of 387: the parts `rows22240R_4393` … `rows22240R_4407` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 98696 in units of a depth-4 test: row 154 columns 57–57, row 154
columns 58–58, row 154 columns 59–59, row 154 columns 60–60, row 154 columns 61–61, row 154 columns 62–62, row 154
columns 63–63, row 154 columns 64–64, row 154 columns 65–66, row 154 columns 67–69, row 154 columns 70–339, row 155
columns 0–41, row 155 columns 42–44, row 155 columns 45–46, row 155 columns 47–47), each a sum of refined costs
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

theorem rows22240R_4393 : rowsJ2 154 155 57 58 ≤ 15338524578630 := by decide +kernel

theorem rows22240R_4394 : rowsJ2 154 155 58 59 ≤ 13764330412112 := by decide +kernel

theorem rows22240R_4395 : rowsJ2 154 155 59 60 ≤ 12287054488984 := by decide +kernel

theorem rows22240R_4396 : rowsJ2 154 155 60 61 ≤ 10903991300078 := by decide +kernel

theorem rows22240R_4397 : rowsJ2 154 155 61 62 ≤ 9612626432073 := by decide +kernel

theorem rows22240R_4398 : rowsJ2 154 155 62 63 ≤ 8410627327468 := by decide +kernel

theorem rows22240R_4399 : rowsJ2 154 155 63 64 ≤ 7295828261909 := by decide +kernel

theorem rows22240R_4400 : rowsJ2 154 155 64 65 ≤ 6266234818341 := by decide +kernel

theorem rows22240R_4401 : rowsJ2 154 155 65 67 ≤ 9775526837211 := by decide +kernel

theorem rows22240R_4402 : rowsJ2 154 155 67 70 ≤ 8974300556298 := by decide +kernel

theorem rows22240R_4403 : rowsJ2 154 155 70 340 ≤ 2382859161017826 := by decide +kernel

theorem rows22240R_4404 : rowsJ2 155 156 0 42 ≤ 5597203180528 := by decide +kernel

theorem rows22240R_4405 : rowsJ2 155 156 42 45 ≤ 10344464777017 := by decide +kernel

theorem rows22240R_4406 : rowsJ2 155 156 45 47 ≤ 11025502961993 := by decide +kernel

theorem rows22240R_4407 : rowsJ2 155 156 47 48 ≤ 6939995742813 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4393
#print axioms SieveCert.rows22240R_4407
