/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5140–5151 of 5796

File 422 of 465: the parts `rows22250R_5140` … `rows22250R_5151` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 93465 tests: row 168 columns 46–47, row 168 columns 48–48, row 168 columns
49–49, row 168 columns 50–50, row 168 columns 51–51, row 168 columns 52–52, row 168 columns 53–53, row 168 columns
54–54, row 168 columns 55–55, row 168 columns 56–56, row 168 columns 57–57, row 168 columns 58–58), each a sum of
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

theorem rows22250R_5140 : rowsJ2 168 169 46 48 ≤ 12156553359130 := by decide +kernel

theorem rows22250R_5141 : rowsJ2 168 169 48 49 ≤ 7441762592809 := by decide +kernel

theorem rows22250R_5142 : rowsJ2 168 169 49 50 ≤ 8414782076353 := by decide +kernel

theorem rows22250R_5143 : rowsJ2 168 169 50 51 ≤ 9433500459837 := by decide +kernel

theorem rows22250R_5144 : rowsJ2 168 169 51 52 ≤ 10496253400848 := by decide +kernel

theorem rows22250R_5145 : rowsJ2 168 169 52 53 ≤ 11601528331173 := by decide +kernel

theorem rows22250R_5146 : rowsJ2 168 169 53 54 ≤ 12747956989052 := by decide +kernel

theorem rows22250R_5147 : rowsJ2 168 169 54 55 ≤ 13934308694768 := by decide +kernel

theorem rows22250R_5148 : rowsJ2 168 169 55 56 ≤ 15159484326784 := by decide +kernel

theorem rows22250R_5149 : rowsJ2 168 169 56 57 ≤ 16422510961216 := by decide +kernel

theorem rows22250R_5150 : rowsJ2 168 169 57 58 ≤ 14875595511963 := by decide +kernel

theorem rows22250R_5151 : rowsJ2 168 169 58 59 ≤ 13417259672823 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5140
#print axioms SieveCert.rows22250R_5151
