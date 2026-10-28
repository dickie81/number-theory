/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1262–1273 of 4715

File 114 of 351: the parts `rows22250R_1262` … `rows22250R_1273` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, work 98256 in units of a depth-4 test: row 68 columns 60–60, row 68 columns
61–61, row 68 columns 62–62, row 68 columns 63–63, row 68 columns 64–64, row 68 columns 65–65, row 68 columns 66–66,
row 68 columns 67–67, row 68 columns 68–339, row 69 columns 0–17, row 69 columns 18–20, row 69 columns 21–21), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1262 : rowsJ2 68 69 60 61 ≤ 5908881850674 := by decide +kernel

theorem rows22250R_1263 : rowsJ2 68 69 61 62 ≤ 5560697191020 := by decide +kernel

theorem rows22250R_1264 : rowsJ2 68 69 62 63 ≤ 5149709166547 := by decide +kernel

theorem rows22250R_1265 : rowsJ2 68 69 63 64 ≤ 4796330835938 := by decide +kernel

theorem rows22250R_1266 : rowsJ2 68 69 64 65 ≤ 4378699610038 := by decide +kernel

theorem rows22250R_1267 : rowsJ2 68 69 65 66 ≤ 4019200410588 := by decide +kernel

theorem rows22250R_1268 : rowsJ2 68 69 66 67 ≤ 3593922572693 := by decide +kernel

theorem rows22250R_1269 : rowsJ2 68 69 67 68 ≤ 3227344991818 := by decide +kernel

theorem rows22250R_1270 : rowsJ2 68 69 68 340 ≤ 2863604746844 := by decide +kernel

theorem rows22250R_1271 : rowsJ2 69 70 0 18 ≤ 988775881288 := by decide +kernel

theorem rows22250R_1272 : rowsJ2 69 70 18 21 ≤ 0 := by decide +kernel

theorem rows22250R_1273 : rowsJ2 69 70 21 22 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1262
#print axioms SieveCert.rows22250R_1273
