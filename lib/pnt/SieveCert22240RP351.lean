/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4482–4495 of 5066

File 351 of 387: the parts `rows22240R_4482` … `rows22240R_4495` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 95787 in units of a depth-4 test: row 158 columns 52–52, row 158
columns 53–53, row 158 columns 54–54, row 158 columns 55–55, row 158 columns 56–56, row 158 columns 57–57, row 158
columns 58–58, row 158 columns 59–59, row 158 columns 60–60, row 158 columns 61–61, row 158 columns 62–63, row 158
columns 64–65, row 158 columns 66–69, row 158 columns 70–339), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4482 : rowsJ2 158 159 52 53 ≤ 15379295529183 := by decide +kernel

theorem rows22240R_4483 : rowsJ2 158 159 53 54 ≤ 16804477726013 := by decide +kernel

theorem rows22240R_4484 : rowsJ2 158 159 54 55 ≤ 18275998609350 := by decide +kernel

theorem rows22240R_4485 : rowsJ2 158 159 55 56 ≤ 16474112862162 := by decide +kernel

theorem rows22240R_4486 : rowsJ2 158 159 56 57 ≤ 14780454758748 := by decide +kernel

theorem rows22240R_4487 : rowsJ2 158 159 57 58 ≤ 13191747901771 := by decide +kernel

theorem rows22240R_4488 : rowsJ2 158 159 58 59 ≤ 11704946472815 := by decide +kernel

theorem rows22240R_4489 : rowsJ2 158 159 59 60 ≤ 10317216388236 := by decide +kernel

theorem rows22240R_4490 : rowsJ2 158 159 60 61 ≤ 9025936612665 := by decide +kernel

theorem rows22240R_4491 : rowsJ2 158 159 61 62 ≤ 7828692058923 := by decide +kernel

theorem rows22240R_4492 : rowsJ2 158 159 62 64 ≤ 12430826657492 := by decide +kernel

theorem rows22240R_4493 : rowsJ2 158 159 64 66 ≤ 8717858608973 := by decide +kernel

theorem rows22240R_4494 : rowsJ2 158 159 66 70 ≤ 9008550451407 := by decide +kernel

theorem rows22240R_4495 : rowsJ2 158 159 70 340 ≤ 2595623866226406 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4482
#print axioms SieveCert.rows22240R_4495
