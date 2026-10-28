/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4211–4222 of 5066

File 332 of 387: the parts `rows22240R_4211` … `rows22240R_4222` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 96774 in units of a depth-4 test: row 147 columns 50–51, row 147
columns 52–52, row 147 columns 53–53, row 147 columns 54–54, row 147 columns 55–55, row 147 columns 56–56, row 147
columns 57–57, row 147 columns 58–58, row 147 columns 59–59, row 147 columns 60–60, row 147 columns 61–61, row 147
columns 62–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22240R_4211 : rowsJ2 147 148 50 52 ≤ 11207243164628 := by decide +kernel

theorem rows22240R_4212 : rowsJ2 147 148 52 53 ≤ 6924504774731 := by decide +kernel

theorem rows22240R_4213 : rowsJ2 147 148 53 54 ≤ 7870662449735 := by decide +kernel

theorem rows22240R_4214 : rowsJ2 147 148 54 55 ≤ 8863585310099 := by decide +kernel

theorem rows22240R_4215 : rowsJ2 147 148 55 56 ≤ 9901521192135 := by decide +kernel

theorem rows22240R_4216 : rowsJ2 147 148 56 57 ≤ 10982845615417 := by decide +kernel

theorem rows22240R_4217 : rowsJ2 147 148 57 58 ≤ 12106053478279 := by decide +kernel

theorem rows22240R_4218 : rowsJ2 147 148 58 59 ≤ 13269750137549 := by decide +kernel

theorem rows22240R_4219 : rowsJ2 147 148 59 60 ≤ 14472643203101 := by decide +kernel

theorem rows22240R_4220 : rowsJ2 147 148 60 61 ≤ 14337052418341 := by decide +kernel

theorem rows22240R_4221 : rowsJ2 147 148 61 62 ≤ 12900380162333 := by decide +kernel

theorem rows22240R_4222 : rowsJ2 147 148 62 63 ≤ 11549733670848 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4211
#print axioms SieveCert.rows22240R_4222
