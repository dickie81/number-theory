/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4649–4660 of 5796

File 384 of 465: the parts `rows22250R_4649` … `rows22250R_4660` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 93033 tests: row 150 columns 50–52, row 150 columns 53–54, row 150 columns
55–55, row 150 columns 56–56, row 150 columns 57–57, row 150 columns 58–58, row 150 columns 59–59, row 150 columns
60–60, row 150 columns 61–61, row 150 columns 62–62, row 150 columns 63–63, row 150 columns 64–64), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4649 : rowsJ2 150 151 50 53 ≤ 5965599474575 := by decide +kernel

theorem rows22250R_4650 : rowsJ2 150 151 53 55 ≤ 6551033359251 := by decide +kernel

theorem rows22250R_4651 : rowsJ2 150 151 55 56 ≤ 4177206528604 := by decide +kernel

theorem rows22250R_4652 : rowsJ2 150 151 56 57 ≤ 4831680168360 := by decide +kernel

theorem rows22250R_4653 : rowsJ2 150 151 57 58 ≤ 5524161711343 := by decide +kernel

theorem rows22250R_4654 : rowsJ2 150 151 58 59 ≤ 6253188047561 := by decide +kernel

theorem rows22250R_4655 : rowsJ2 150 151 59 60 ≤ 7017404588437 := by decide +kernel

theorem rows22250R_4656 : rowsJ2 150 151 60 61 ≤ 7815559696069 := by decide +kernel

theorem rows22250R_4657 : rowsJ2 150 151 61 62 ≤ 8646499568048 := by decide +kernel

theorem rows22250R_4658 : rowsJ2 150 151 62 63 ≤ 9509163548592 := by decide +kernel

theorem rows22250R_4659 : rowsJ2 150 151 63 64 ≤ 10402579840198 := by decide +kernel

theorem rows22250R_4660 : rowsJ2 150 151 64 65 ≤ 11293553734907 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4649
#print axioms SieveCert.rows22250R_4660
