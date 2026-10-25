/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5126–5139 of 5796

File 421 of 465: the parts `rows22250R_5126` … `rows22250R_5139` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 92675 tests: row 167 columns 58–58, row 167 columns 59–59, row 167 columns
60–60, row 167 columns 61–61, row 167 columns 62–62, row 167 columns 63–63, row 167 columns 64–64, row 167 columns
65–65, row 167 columns 66–67, row 167 columns 68–69, row 167 columns 70–138, row 167 columns 139–359, row 168
columns 0–42, row 168 columns 43–45), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_5126 : rowsJ2 167 168 58 59 ≤ 13884252853292 := by decide +kernel

theorem rows22250R_5127 : rowsJ2 167 168 59 60 ≤ 12494087820872 := by decide +kernel

theorem rows22250R_5128 : rowsJ2 167 168 60 61 ≤ 11187114542510 := by decide +kernel

theorem rows22250R_5129 : rowsJ2 167 168 61 62 ≤ 9961087970023 := by decide +kernel

theorem rows22250R_5130 : rowsJ2 167 168 62 63 ≤ 8813920388518 := by decide +kernel

theorem rows22250R_5131 : rowsJ2 167 168 63 64 ≤ 7743674128556 := by decide +kernel

theorem rows22250R_5132 : rowsJ2 167 168 64 65 ≤ 6748554938699 := by decide +kernel

theorem rows22250R_5133 : rowsJ2 167 168 65 66 ≤ 5826905973505 := by decide +kernel

theorem rows22250R_5134 : rowsJ2 167 168 66 68 ≤ 9175248643218 := by decide +kernel

theorem rows22250R_5135 : rowsJ2 167 168 68 70 ≤ 6334557738320 := by decide +kernel

theorem rows22250R_5136 : rowsJ2 167 168 70 139 ≤ 1058197774616103 := by decide +kernel

theorem rows22250R_5137 : rowsJ2 167 168 139 360 ≤ 1477794678276356 := by decide +kernel

theorem rows22250R_5138 : rowsJ2 168 169 0 43 ≤ 8136687859893 := by decide +kernel

theorem rows22250R_5139 : rowsJ2 168 169 43 46 ≤ 12193895556244 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5126
#print axioms SieveCert.rows22250R_5139
