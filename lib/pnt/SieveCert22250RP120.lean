/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1342–1349 of 4715

File 120 of 351: the parts `rows22250R_1342` … `rows22250R_1349` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 89482 tests: row 70 columns 50–50, row 70 columns 51–51, row 70 columns
52–52, row 70 columns 53–53, row 70 columns 54–54, row 70 columns 55–55, row 70 columns 56–56, row 70 columns
57–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_1342 : rowsJ2 70 71 50 51 ≤ 3780521092115 := by decide +kernel

theorem rows22250R_1343 : rowsJ2 70 71 51 52 ≤ 4618555027677 := by decide +kernel

theorem rows22250R_1344 : rowsJ2 70 71 52 53 ≤ 5161968470073 := by decide +kernel

theorem rows22250R_1345 : rowsJ2 70 71 53 54 ≤ 5591285484784 := by decide +kernel

theorem rows22250R_1346 : rowsJ2 70 71 54 55 ≤ 5982809700645 := by decide +kernel

theorem rows22250R_1347 : rowsJ2 70 71 55 56 ≤ 6012046434852 := by decide +kernel

theorem rows22250R_1348 : rowsJ2 70 71 56 57 ≤ 5608313412815 := by decide +kernel

theorem rows22250R_1349 : rowsJ2 70 71 57 58 ≤ 5261336316595 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1342
#print axioms SieveCert.rows22250R_1349
