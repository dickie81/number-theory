/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4071–4085 of 5796

File 340 of 465: the parts `rows22250R_4071` … `rows22250R_4085` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 96171 tests: row 131 columns 90–92, row 131 columns 93–94, row 131 columns
95–96, row 131 columns 97–359, row 132 columns 0–25, row 132 columns 26–28, row 132 columns 29–31, row 132 columns
32–35, row 132 columns 36–44, row 132 columns 45–58, row 132 columns 59–61, row 132 columns 62–62, row 132 columns
63–63, row 132 columns 64–64, row 132 columns 65–65), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4071 : rowsJ2 131 132 90 93 ≤ 9688638579042 := by decide +kernel

theorem rows22250R_4072 : rowsJ2 131 132 93 95 ≤ 11250408133954 := by decide +kernel

theorem rows22250R_4073 : rowsJ2 131 132 95 97 ≤ 15983926801550 := by decide +kernel

theorem rows22250R_4074 : rowsJ2 131 132 97 360 ≤ 911872190205805 := by decide +kernel

theorem rows22250R_4075 : rowsJ2 132 133 0 26 ≤ 1104940774501 := by decide +kernel

theorem rows22250R_4076 : rowsJ2 132 133 26 29 ≤ 8824991669340 := by decide +kernel

theorem rows22250R_4077 : rowsJ2 132 133 29 32 ≤ 14331311734248 := by decide +kernel

theorem rows22250R_4078 : rowsJ2 132 133 32 36 ≤ 9570801050591 := by decide +kernel

theorem rows22250R_4079 : rowsJ2 132 133 36 45 ≤ 3281286315361 := by decide +kernel

theorem rows22250R_4080 : rowsJ2 132 133 45 59 ≤ 2262326561057 := by decide +kernel

theorem rows22250R_4081 : rowsJ2 132 133 59 62 ≤ 4589793844190 := by decide +kernel

theorem rows22250R_4082 : rowsJ2 132 133 62 63 ≤ 2304448942849 := by decide +kernel

theorem rows22250R_4083 : rowsJ2 132 133 63 64 ≤ 2749775939501 := by decide +kernel

theorem rows22250R_4084 : rowsJ2 132 133 64 65 ≤ 3192351025903 := by decide +kernel

theorem rows22250R_4085 : rowsJ2 132 133 65 66 ≤ 3578205835791 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4071
#print axioms SieveCert.rows22250R_4085
