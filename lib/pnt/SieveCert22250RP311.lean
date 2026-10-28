/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4077–4090 of 4715

File 311 of 351: the parts `rows22250R_4077` … `rows22250R_4090` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 96222 in units of a depth-4 test: row 154 columns 53–53, row 154
columns 54–54, row 154 columns 55–55, row 154 columns 56–56, row 154 columns 57–57, row 154 columns 58–58, row 154
columns 59–59, row 154 columns 60–60, row 154 columns 61–61, row 154 columns 62–62, row 154 columns 63–64, row 154
columns 65–66, row 154 columns 67–70, row 154 columns 71–339), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4077 : rowsJ2 154 155 53 54 ≤ 13774725649095 := by decide +kernel

theorem rows22250R_4078 : rowsJ2 154 155 54 55 ≤ 15092942871877 := by decide +kernel

theorem rows22250R_4079 : rowsJ2 154 155 55 56 ≤ 16455397922492 := by decide +kernel

theorem rows22250R_4080 : rowsJ2 154 155 56 57 ≤ 14799967457976 := by decide +kernel

theorem rows22250R_4081 : rowsJ2 154 155 57 58 ≤ 13245092218581 := by decide +kernel

theorem rows22250R_4082 : rowsJ2 154 155 58 59 ≤ 11787848354001 := by decide +kernel

theorem rows22250R_4083 : rowsJ2 154 155 59 60 ≤ 10425520291438 := by decide +kernel

theorem rows22250R_4084 : rowsJ2 154 155 60 61 ≤ 9155590371797 := by decide +kernel

theorem rows22250R_4085 : rowsJ2 154 155 61 62 ≤ 7975729440116 := by decide +kernel

theorem rows22250R_4086 : rowsJ2 154 155 62 63 ≤ 6883788320472 := by decide +kernel

theorem rows22250R_4087 : rowsJ2 154 155 63 65 ≤ 10833713379574 := by decide +kernel

theorem rows22250R_4088 : rowsJ2 154 155 65 67 ≤ 7474662896636 := by decide +kernel

theorem rows22250R_4089 : rowsJ2 154 155 67 71 ≤ 7423787739772 := by decide +kernel

theorem rows22250R_4090 : rowsJ2 154 155 71 340 ≤ 2472373470931108 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4077
#print axioms SieveCert.rows22250R_4090
