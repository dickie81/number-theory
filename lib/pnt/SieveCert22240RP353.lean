/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4510–4525 of 5066

File 353 of 387: the parts `rows22240R_4510` … `rows22240R_4525` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 98100 in units of a depth-4 test: row 159 columns 57–57, row 159
columns 58–58, row 159 columns 59–59, row 159 columns 60–60, row 159 columns 61–61, row 159 columns 62–63, row 159
columns 64–66, row 159 columns 67–339, row 160 columns 0–40, row 160 columns 41–43, row 160 columns 44–45, row 160
columns 46–46, row 160 columns 47–47, row 160 columns 48–48, row 160 columns 49–49, row 160 columns 50–50), each a
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

theorem rows22240R_4510 : rowsJ2 159 160 57 58 ≤ 12651893219467 := by decide +kernel

theorem rows22240R_4511 : rowsJ2 159 160 58 59 ≤ 11188328311046 := by decide +kernel

theorem rows22240R_4512 : rowsJ2 159 160 59 60 ≤ 9824434819631 := by decide +kernel

theorem rows22240R_4513 : rowsJ2 159 160 60 61 ≤ 8557625127335 := by decide +kernel

theorem rows22240R_4514 : rowsJ2 159 160 61 62 ≤ 7385508937615 := by decide +kernel

theorem rows22240R_4515 : rowsJ2 159 160 62 64 ≤ 11622605887774 := by decide +kernel

theorem rows22240R_4516 : rowsJ2 159 160 64 67 ≤ 10893153290942 := by decide +kernel

theorem rows22240R_4517 : rowsJ2 159 160 67 340 ≤ 2595317950716822 := by decide +kernel

theorem rows22240R_4518 : rowsJ2 160 161 0 41 ≤ 10280679331555 := by decide +kernel

theorem rows22240R_4519 : rowsJ2 160 161 41 44 ≤ 15357419108158 := by decide +kernel

theorem rows22240R_4520 : rowsJ2 160 161 44 46 ≤ 15280358016139 := by decide +kernel

theorem rows22240R_4521 : rowsJ2 160 161 46 47 ≤ 9343950055713 := by decide +kernel

theorem rows22240R_4522 : rowsJ2 160 161 47 48 ≤ 10558443565135 := by decide +kernel

theorem rows22240R_4523 : rowsJ2 160 161 48 49 ≤ 11829051552678 := by decide +kernel

theorem rows22240R_4524 : rowsJ2 160 161 49 50 ≤ 13153800743045 := by decide +kernel

theorem rows22240R_4525 : rowsJ2 160 161 50 51 ≤ 14530913275325 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4510
#print axioms SieveCert.rows22240R_4525
