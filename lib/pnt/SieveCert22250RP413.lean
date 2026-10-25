/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5021–5032 of 5796

File 413 of 465: the parts `rows22250R_5021` … `rows22250R_5032` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 99298 tests: row 163 columns 56–56, row 163 columns 57–57, row 163 columns
58–58, row 163 columns 59–59, row 163 columns 60–60, row 163 columns 61–61, row 163 columns 62–62, row 163 columns
63–63, row 163 columns 64–64, row 163 columns 65–65, row 163 columns 66–66, row 163 columns 67–67), each a sum of
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

theorem rows22250R_5021 : rowsJ2 163 164 56 57 ≤ 12230896183410 := by decide +kernel

theorem rows22250R_5022 : rowsJ2 163 164 57 58 ≤ 13340740208754 := by decide +kernel

theorem rows22250R_5023 : rowsJ2 163 164 58 59 ≤ 14486033306645 := by decide +kernel

theorem rows22250R_5024 : rowsJ2 163 164 59 60 ≤ 14352888080223 := by decide +kernel

theorem rows22250R_5025 : rowsJ2 163 164 60 61 ≤ 12976234938189 := by decide +kernel

theorem rows22250R_5026 : rowsJ2 163 164 61 62 ≤ 11678954174796 := by decide +kernel

theorem rows22250R_5027 : rowsJ2 163 164 62 63 ≤ 10458883735691 := by decide +kernel

theorem rows22250R_5028 : rowsJ2 163 164 63 64 ≤ 9314007745338 := by decide +kernel

theorem rows22250R_5029 : rowsJ2 163 164 64 65 ≤ 8242449667304 := by decide +kernel

theorem rows22250R_5030 : rowsJ2 163 164 65 66 ≤ 7242466062496 := by decide +kernel

theorem rows22250R_5031 : rowsJ2 163 164 66 67 ≤ 6312440903835 := by decide +kernel

theorem rows22250R_5032 : rowsJ2 163 164 67 68 ≤ 5450880411062 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5021
#print axioms SieveCert.rows22250R_5032
