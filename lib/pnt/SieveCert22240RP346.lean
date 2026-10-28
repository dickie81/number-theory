/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4408–4421 of 5066

File 346 of 387: the parts `rows22240R_4408` … `rows22240R_4421` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 99805 in units of a depth-4 test: row 155 columns 48–48, row 155
columns 49–49, row 155 columns 50–50, row 155 columns 51–51, row 155 columns 52–52, row 155 columns 53–53, row 155
columns 54–54, row 155 columns 55–55, row 155 columns 56–56, row 155 columns 57–57, row 155 columns 58–58, row 155
columns 59–59, row 155 columns 60–60, row 155 columns 61–61), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_4408 : rowsJ2 155 156 48 49 ≤ 7968725264359 := by decide +kernel

theorem rows22240R_4409 : rowsJ2 155 156 49 50 ≤ 9052372556372 := by decide +kernel

theorem rows22240R_4410 : rowsJ2 155 156 50 51 ≤ 10188843002448 := by decide +kernel

theorem rows22240R_4411 : rowsJ2 155 156 51 52 ≤ 11376200914662 := by decide +kernel

theorem rows22240R_4412 : rowsJ2 155 156 52 53 ≤ 12612656853132 := by decide +kernel

theorem rows22240R_4413 : rowsJ2 155 156 53 54 ≤ 13896579311148 := by decide +kernel

theorem rows22240R_4414 : rowsJ2 155 156 54 55 ≤ 15226500303657 := by decide +kernel

theorem rows22240R_4415 : rowsJ2 155 156 55 56 ≤ 16601082019829 := by decide +kernel

theorem rows22240R_4416 : rowsJ2 155 156 56 57 ≤ 16439518208351 := by decide +kernel

theorem rows22240R_4417 : rowsJ2 155 156 57 58 ≤ 14786238066742 := by decide +kernel

theorem rows22240R_4418 : rowsJ2 155 156 58 59 ≤ 13233267793492 := by decide +kernel

theorem rows22240R_4419 : rowsJ2 155 156 59 60 ≤ 11777718663943 := by decide +kernel

theorem rows22240R_4420 : rowsJ2 155 156 60 61 ≤ 10416904671397 := by decide +kernel

theorem rows22240R_4421 : rowsJ2 155 156 61 62 ≤ 9148332410461 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4408
#print axioms SieveCert.rows22240R_4421
