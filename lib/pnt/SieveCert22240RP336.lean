/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4266–4278 of 5066

File 336 of 387: the parts `rows22240R_4266` … `rows22240R_4278` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 99853 in units of a depth-4 test: row 149 columns 55–55, row 149
columns 56–56, row 149 columns 57–57, row 149 columns 58–58, row 149 columns 59–59, row 149 columns 60–60, row 149
columns 61–61, row 149 columns 62–62, row 149 columns 63–63, row 149 columns 64–64, row 149 columns 65–65, row 149
columns 66–66, row 149 columns 67–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22240R_4266 : rowsJ2 149 150 55 56 ≤ 11358871301241 := by decide +kernel

theorem rows22240R_4267 : rowsJ2 149 150 56 57 ≤ 12519258003607 := by decide +kernel

theorem rows22240R_4268 : rowsJ2 149 150 57 58 ≤ 13721430093774 := by decide +kernel

theorem rows22240R_4269 : rowsJ2 149 150 58 59 ≤ 14964078610308 := by decide +kernel

theorem rows22240R_4270 : rowsJ2 149 150 59 60 ≤ 14822576681886 := by decide +kernel

theorem rows22240R_4271 : rowsJ2 149 150 60 61 ≤ 13335924565787 := by decide +kernel

theorem rows22240R_4272 : rowsJ2 149 150 61 62 ≤ 11938582214936 := by decide +kernel

theorem rows22240R_4273 : rowsJ2 149 150 62 63 ≤ 10628121379571 := by decide +kernel

theorem rows22240R_4274 : rowsJ2 149 150 63 64 ≤ 9402276294585 := by decide +kernel

theorem rows22240R_4275 : rowsJ2 149 150 64 65 ≤ 8258940670311 := by decide +kernel

theorem rows22240R_4276 : rowsJ2 149 150 65 66 ≤ 7196164795012 := by decide +kernel

theorem rows22240R_4277 : rowsJ2 149 150 66 67 ≤ 6212143853042 := by decide +kernel

theorem rows22240R_4278 : rowsJ2 149 150 67 68 ≤ 5305212051187 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4266
#print axioms SieveCert.rows22240R_4278
