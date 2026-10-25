/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5195–5207 of 5796

File 426 of 465: the parts `rows22250R_5195` … `rows22250R_5207` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 98411 tests: row 170 columns 53–53, row 170 columns 54–54, row 170 columns
55–55, row 170 columns 56–56, row 170 columns 57–57, row 170 columns 58–58, row 170 columns 59–59, row 170 columns
60–60, row 170 columns 61–61, row 170 columns 62–62, row 170 columns 63–63, row 170 columns 64–65, row 170 columns
66–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5195 : rowsJ2 170 171 53 54 ≤ 14434732010236 := by decide +kernel

theorem rows22250R_5196 : rowsJ2 170 171 54 55 ≤ 15702534632081 := by decide +kernel

theorem rows22250R_5197 : rowsJ2 170 171 55 56 ≤ 17009436587211 := by decide +kernel

theorem rows22250R_5198 : rowsJ2 170 171 56 57 ≤ 15405696803091 := by decide +kernel

theorem rows22250R_5199 : rowsJ2 170 171 57 58 ≤ 13894098981521 := by decide +kernel

theorem rows22250R_5200 : rowsJ2 170 171 58 59 ≤ 12471927115433 := by decide +kernel

theorem rows22250R_5201 : rowsJ2 170 171 59 60 ≤ 11136651861728 := by decide +kernel

theorem rows22250R_5202 : rowsJ2 170 171 60 61 ≤ 9885921084317 := by decide +kernel

theorem rows22250R_5203 : rowsJ2 170 171 61 62 ≤ 8717551242407 := by decide +kernel

theorem rows22250R_5204 : rowsJ2 170 171 62 63 ≤ 7629519561597 := by decide +kernel

theorem rows22250R_5205 : rowsJ2 170 171 63 64 ≤ 6619956931183 := by decide +kernel

theorem rows22250R_5206 : rowsJ2 170 171 64 66 ≤ 10516634253892 := by decide +kernel

theorem rows22250R_5207 : rowsJ2 170 171 66 68 ≤ 7379617142454 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5195
#print axioms SieveCert.rows22250R_5207
