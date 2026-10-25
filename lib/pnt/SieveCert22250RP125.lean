/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1400–1414 of 4715

File 125 of 351: the parts `rows22250R_1400` … `rows22250R_1414` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 95845 tests: row 71 columns 62–62, row 71 columns 63–63, row 71 columns
64–64, row 71 columns 65–65, row 71 columns 66–66, row 71 columns 67–67, row 71 columns 68–68, row 71 columns 69–69,
row 71 columns 70–70, row 71 columns 71–339, row 72 columns 0–17, row 72 columns 18–19, row 72 columns 20–21, row 72
columns 22–22, row 72 columns 23–23), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_1400 : rowsJ2 71 72 62 63 ≤ 2949495868251 := by decide +kernel

theorem rows22250R_1401 : rowsJ2 71 72 63 64 ≤ 2655908520438 := by decide +kernel

theorem rows22250R_1402 : rowsJ2 71 72 64 65 ≤ 2354325936150 := by decide +kernel

theorem rows22250R_1403 : rowsJ2 71 72 65 66 ≤ 2055180641872 := by decide +kernel

theorem rows22250R_1404 : rowsJ2 71 72 66 67 ≤ 1747501109602 := by decide +kernel

theorem rows22250R_1405 : rowsJ2 71 72 67 68 ≤ 1442023400818 := by decide +kernel

theorem rows22250R_1406 : rowsJ2 71 72 68 69 ≤ 1195886209895 := by decide +kernel

theorem rows22250R_1407 : rowsJ2 71 72 69 70 ≤ 951376053914 := by decide +kernel

theorem rows22250R_1408 : rowsJ2 71 72 70 71 ≤ 766674367418 := by decide +kernel

theorem rows22250R_1409 : rowsJ2 71 72 71 340 ≤ 583099432912 := by decide +kernel

theorem rows22250R_1410 : rowsJ2 72 73 0 18 ≤ 629389277060 := by decide +kernel

theorem rows22250R_1411 : rowsJ2 72 73 18 20 ≤ 0 := by decide +kernel

theorem rows22250R_1412 : rowsJ2 72 73 20 22 ≤ 0 := by decide +kernel

theorem rows22250R_1413 : rowsJ2 72 73 22 23 ≤ 0 := by decide +kernel

theorem rows22250R_1414 : rowsJ2 72 73 23 24 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1400
#print axioms SieveCert.rows22250R_1414
