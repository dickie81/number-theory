/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5309–5321 of 5796

File 434 of 465: the parts `rows22250R_5309` … `rows22250R_5321` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 94653 tests: row 175 columns 49–49, row 175 columns 50–50, row 175 columns
51–51, row 175 columns 52–52, row 175 columns 53–53, row 175 columns 54–54, row 175 columns 55–55, row 175 columns
56–56, row 175 columns 57–57, row 175 columns 58–58, row 175 columns 59–59, row 175 columns 60–60, row 175 columns
61–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_5309 : rowsJ2 175 176 49 50 ≤ 13801261423349 := by decide +kernel

theorem rows22250R_5310 : rowsJ2 175 176 50 51 ≤ 15120162360268 := by decide +kernel

theorem rows22250R_5311 : rowsJ2 175 176 51 52 ≤ 16483204145236 := by decide +kernel

theorem rows22250R_5312 : rowsJ2 175 176 52 53 ≤ 17889275018144 := by decide +kernel

theorem rows22250R_5313 : rowsJ2 175 176 53 54 ≤ 17715252705742 := by decide +kernel

theorem rows22250R_5314 : rowsJ2 175 176 54 55 ≤ 16006805194015 := by decide +kernel

theorem rows22250R_5315 : rowsJ2 175 176 55 56 ≤ 14398771917614 := by decide +kernel

theorem rows22250R_5316 : rowsJ2 175 176 56 57 ≤ 12888123639581 := by decide +kernel

theorem rows22250R_5317 : rowsJ2 175 176 57 58 ≤ 11472045339983 := by decide +kernel

theorem rows22250R_5318 : rowsJ2 175 176 58 59 ≤ 10147925103363 := by decide +kernel

theorem rows22250R_5319 : rowsJ2 175 176 59 60 ≤ 8913344030261 := by decide +kernel

theorem rows22250R_5320 : rowsJ2 175 176 60 61 ≤ 7766067094791 := by decide +kernel

theorem rows22250R_5321 : rowsJ2 175 176 61 63 ≤ 12429391001874 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5309
#print axioms SieveCert.rows22250R_5321
