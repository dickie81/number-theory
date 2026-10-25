/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5353–5366 of 5796

File 437 of 465: the parts `rows22250R_5353` … `rows22250R_5366` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 98430 tests: row 177 columns 48–48, row 177 columns 49–49, row 177 columns
50–50, row 177 columns 51–51, row 177 columns 52–52, row 177 columns 53–53, row 177 columns 54–54, row 177 columns
55–55, row 177 columns 56–56, row 177 columns 57–57, row 177 columns 58–58, row 177 columns 59–59, row 177 columns
60–61, row 177 columns 62–359), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5353 : rowsJ2 177 178 48 49 ≤ 14329564043776 := by decide +kernel

theorem rows22250R_5354 : rowsJ2 177 178 49 50 ≤ 15697377277816 := by decide +kernel

theorem rows22250R_5355 : rowsJ2 177 178 50 51 ≤ 17110871328237 := by decide +kernel

theorem rows22250R_5356 : rowsJ2 177 178 51 52 ≤ 18568913390281 := by decide +kernel

theorem rows22250R_5357 : rowsJ2 177 178 52 53 ≤ 18386505309476 := by decide +kernel

theorem rows22250R_5358 : rowsJ2 177 178 53 54 ≤ 16611520729700 := by decide +kernel

theorem rows22250R_5359 : rowsJ2 177 178 54 55 ≤ 14941232416036 := by decide +kernel

theorem rows22250R_5360 : rowsJ2 177 178 55 56 ≤ 13372425196794 := by decide +kernel

theorem rows22250R_5361 : rowsJ2 177 178 56 57 ≤ 11902113096645 := by decide +kernel

theorem rows22250R_5362 : rowsJ2 177 178 57 58 ≤ 10527527230103 := by decide +kernel

theorem rows22250R_5363 : rowsJ2 177 178 58 59 ≤ 9246104821587 := by decide +kernel

theorem rows22250R_5364 : rowsJ2 177 178 59 60 ≤ 8055479264441 := by decide +kernel

theorem rows22250R_5365 : rowsJ2 177 178 60 62 ≤ 12891551279498 := by decide +kernel

theorem rows22250R_5366 : rowsJ2 177 178 62 360 ≤ 2562945776972735 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5353
#print axioms SieveCert.rows22250R_5366
