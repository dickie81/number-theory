/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4121–4133 of 4715

File 314 of 351: the parts `rows22250R_4121` … `rows22250R_4133` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 92717 in units of a depth-4 test: row 156 columns 52–52, row 156
columns 53–53, row 156 columns 54–54, row 156 columns 55–55, row 156 columns 56–56, row 156 columns 57–57, row 156
columns 58–58, row 156 columns 59–59, row 156 columns 60–60, row 156 columns 61–61, row 156 columns 62–63, row 156
columns 64–66, row 156 columns 67–339), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4121 : rowsJ2 156 157 52 53 ≤ 14277526748448 := by decide +kernel

theorem rows22250R_4122 : rowsJ2 156 157 53 54 ≤ 15642305989197 := by decide +kernel

theorem rows22250R_4123 : rowsJ2 156 157 54 55 ≤ 17052784631965 := by decide +kernel

theorem rows22250R_4124 : rowsJ2 156 157 55 56 ≤ 15335690740257 := by decide +kernel

theorem rows22250R_4125 : rowsJ2 156 157 56 57 ≤ 13723232686105 := by decide +kernel

theorem rows22250R_4126 : rowsJ2 156 157 57 58 ≤ 12212314499824 := by decide +kernel

theorem rows22250R_4127 : rowsJ2 156 157 58 59 ≤ 10800062429613 := by decide +kernel

theorem rows22250R_4128 : rowsJ2 156 157 59 60 ≤ 9483813689043 := by decide +kernel

theorem rows22250R_4129 : rowsJ2 156 157 60 61 ≤ 8261106249603 := by decide +kernel

theorem rows22250R_4130 : rowsJ2 156 157 61 62 ≤ 7129669601012 := by decide +kernel

theorem rows22250R_4131 : rowsJ2 156 157 62 64 ≤ 11219851432533 := by decide +kernel

theorem rows22250R_4132 : rowsJ2 156 157 64 67 ≤ 10514966901643 := by decide +kernel

theorem rows22250R_4133 : rowsJ2 156 157 67 340 ≤ 2652096879791115 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4121
#print axioms SieveCert.rows22250R_4133
