/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4336–4348 of 5066

File 341 of 387: the parts `rows22240R_4336` … `rows22240R_4348` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 96804 in units of a depth-4 test: row 152 columns 49–49, row 152
columns 50–50, row 152 columns 51–51, row 152 columns 52–52, row 152 columns 53–53, row 152 columns 54–54, row 152
columns 55–55, row 152 columns 56–56, row 152 columns 57–57, row 152 columns 58–58, row 152 columns 59–59, row 152
columns 60–60, row 152 columns 61–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22240R_4336 : rowsJ2 152 153 49 50 ≤ 7067520437246 := by decide +kernel

theorem rows22240R_4337 : rowsJ2 152 153 50 51 ≤ 8070126710845 := by decide +kernel

theorem rows22240R_4338 : rowsJ2 152 153 51 52 ≤ 9124152862153 := by decide +kernel

theorem rows22240R_4339 : rowsJ2 152 153 52 53 ≤ 10227662978489 := by decide +kernel

theorem rows22240R_4340 : rowsJ2 152 153 53 54 ≤ 11378847380140 := by decide +kernel

theorem rows22240R_4341 : rowsJ2 152 153 54 55 ≤ 12576075907271 := by decide +kernel

theorem rows22240R_4342 : rowsJ2 152 153 55 56 ≤ 13817832241097 := by decide +kernel

theorem rows22240R_4343 : rowsJ2 152 153 56 57 ≤ 15102741119177 := by decide +kernel

theorem rows22240R_4344 : rowsJ2 152 153 57 58 ≤ 16429529902625 := by decide +kernel

theorem rows22240R_4345 : rowsJ2 152 153 58 59 ≤ 14814426098114 := by decide +kernel

theorem rows22240R_4346 : rowsJ2 152 153 59 60 ≤ 13295304159334 := by decide +kernel

theorem rows22240R_4347 : rowsJ2 152 153 60 61 ≤ 11869417051352 := by decide +kernel

theorem rows22240R_4348 : rowsJ2 152 153 61 62 ≤ 10534206977126 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4336
#print axioms SieveCert.rows22240R_4348
