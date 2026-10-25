/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4649–4664 of 4715

File 347 of 351: the parts `rows22250R_4649` … `rows22250R_4664` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 95109 tests: row 193 columns 30–32, row 193 columns 33–92, row 193 columns
93–339, row 194 columns 0–29, row 194 columns 30–32, row 194 columns 33–339, row 195 columns 0–28, row 195 columns
29–31, row 195 columns 32–339, row 196 columns 0–28, row 196 columns 29–91, row 196 columns 92–339, row 197 columns
0–28, row 197 columns 29–339, row 198 columns 0–28, row 198 columns 29–339), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4649 : rowsJ2 193 194 30 33 ≤ 47998273911081 := by decide +kernel

theorem rows22250R_4650 : rowsJ2 193 194 33 93 ≤ 1311586340126797 := by decide +kernel

theorem rows22250R_4651 : rowsJ2 193 194 93 340 ≤ 3588792955416714 := by decide +kernel

theorem rows22250R_4652 : rowsJ2 194 195 0 30 ≤ 31723857278206 := by decide +kernel

theorem rows22250R_4653 : rowsJ2 194 195 30 33 ≤ 52377004839179 := by decide +kernel

theorem rows22250R_4654 : rowsJ2 194 195 33 340 ≤ 4996298220981726 := by decide +kernel

theorem rows22250R_4655 : rowsJ2 195 196 0 29 ≤ 24673584554200 := by decide +kernel

theorem rows22250R_4656 : rowsJ2 195 196 29 32 ≤ 45861314173353 := by decide +kernel

theorem rows22250R_4657 : rowsJ2 195 196 32 340 ≤ 5115332183847115 := by decide +kernel

theorem rows22250R_4658 : rowsJ2 196 197 0 29 ≤ 28692185937810 := by decide +kernel

theorem rows22250R_4659 : rowsJ2 196 197 29 92 ≤ 1507829221104610 := by decide +kernel

theorem rows22250R_4660 : rowsJ2 196 197 92 340 ≤ 3755586016194176 := by decide +kernel

theorem rows22250R_4661 : rowsJ2 197 198 0 29 ≤ 33203766502100 := by decide +kernel

theorem rows22250R_4662 : rowsJ2 197 198 29 340 ≤ 5365909783286900 := by decide +kernel

theorem rows22250R_4663 : rowsJ2 198 199 0 29 ≤ 38226461135345 := by decide +kernel

theorem rows22250R_4664 : rowsJ2 198 199 29 340 ≤ 5468652338479598 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4649
#print axioms SieveCert.rows22250R_4664
