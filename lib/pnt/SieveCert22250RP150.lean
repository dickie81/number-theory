/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1479–1487 of 5796

File 150 of 465: the parts `rows22250R_1479` … `rows22250R_1487` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 94222 tests: row 72 columns 64–64, row 72 columns 65–65, row 72 columns
66–66, row 72 columns 67–67, row 72 columns 68–68, row 72 columns 69–69, row 72 columns 70–70, row 72 columns 71–71,
row 72 columns 72–359), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1479 : rowsJ2 72 73 64 65 ≤ 4912227121722 := by decide +kernel

theorem rows22250R_1480 : rowsJ2 72 73 65 66 ≤ 4536224981483 := by decide +kernel

theorem rows22250R_1481 : rowsJ2 72 73 66 67 ≤ 4205959335648 := by decide +kernel

theorem rows22250R_1482 : rowsJ2 72 73 67 68 ≤ 3878625703155 := by decide +kernel

theorem rows22250R_1483 : rowsJ2 72 73 68 69 ≤ 3597078191467 := by decide +kernel

theorem rows22250R_1484 : rowsJ2 72 73 69 70 ≤ 3317944767526 := by decide +kernel

theorem rows22250R_1485 : rowsJ2 72 73 70 71 ≤ 3084740322141 := by decide +kernel

theorem rows22250R_1486 : rowsJ2 72 73 71 72 ≤ 2800818389121 := by decide +kernel

theorem rows22250R_1487 : rowsJ2 72 73 72 360 ≤ 2563323269233 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1479
#print axioms SieveCert.rows22250R_1487
