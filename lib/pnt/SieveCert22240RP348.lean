/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4438–4451 of 5066

File 348 of 387: the parts `rows22240R_4438` … `rows22240R_4451` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 99138 in units of a depth-4 test: row 156 columns 54–54, row 156
columns 55–55, row 156 columns 56–56, row 156 columns 57–57, row 156 columns 58–58, row 156 columns 59–59, row 156
columns 60–60, row 156 columns 61–61, row 156 columns 62–62, row 156 columns 63–63, row 156 columns 64–65, row 156
columns 66–68, row 156 columns 69–339, row 157 columns 0–41), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_4438 : rowsJ2 156 157 54 55 ≤ 16206572337893 := by decide +kernel

theorem rows22240R_4439 : rowsJ2 156 157 55 56 ≤ 17627318156579 := by decide +kernel

theorem rows22240R_4440 : rowsJ2 156 157 56 57 ≤ 15891110372819 := by decide +kernel

theorem rows22240R_4441 : rowsJ2 156 157 57 58 ≤ 14258807516952 := by decide +kernel

theorem rows22240R_4442 : rowsJ2 156 157 58 59 ≤ 12727324677217 := by decide +kernel

theorem rows22240R_4443 : rowsJ2 156 157 59 60 ≤ 11293792267272 := by decide +kernel

theorem rows22240R_4444 : rowsJ2 156 157 60 61 ≤ 9955544946501 := by decide +kernel

theorem rows22240R_4445 : rowsJ2 156 157 61 62 ≤ 8710104861751 := by decide +kernel

theorem rows22240R_4446 : rowsJ2 156 157 62 63 ≤ 7555184693857 := by decide +kernel

theorem rows22240R_4447 : rowsJ2 156 157 63 64 ≤ 6488682223088 := by decide +kernel

theorem rows22240R_4448 : rowsJ2 156 157 64 66 ≤ 10122013593021 := by decide +kernel

theorem rows22240R_4449 : rowsJ2 156 157 66 69 ≤ 9291786824356 := by decide +kernel

theorem rows22240R_4450 : rowsJ2 156 157 69 340 ≤ 2609856022941417 := by decide +kernel

theorem rows22240R_4451 : rowsJ2 157 158 0 42 ≤ 8461110629459 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4438
#print axioms SieveCert.rows22240R_4451
