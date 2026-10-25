/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4661–4672 of 5796

File 385 of 465: the parts `rows22250R_4661` … `rows22250R_4672` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 98960 tests: row 150 columns 65–65, row 150 columns 66–66, row 150 columns
67–67, row 150 columns 68–68, row 150 columns 69–69, row 150 columns 70–70, row 150 columns 71–71, row 150 columns
72–72, row 150 columns 73–73, row 150 columns 74–74, row 150 columns 75–75, row 150 columns 76–76), each a sum of
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

theorem rows22250R_4661 : rowsJ2 150 151 65 66 ≤ 12133327417723 := by decide +kernel

theorem rows22250R_4662 : rowsJ2 150 151 66 67 ≤ 11032993257998 := by decide +kernel

theorem rows22250R_4663 : rowsJ2 150 151 67 68 ≤ 9980943456243 := by decide +kernel

theorem rows22250R_4664 : rowsJ2 150 151 68 69 ≤ 8991899446324 := by decide +kernel

theorem rows22250R_4665 : rowsJ2 150 151 69 70 ≤ 8047620203554 := by decide +kernel

theorem rows22250R_4666 : rowsJ2 150 151 70 71 ≤ 7163168904462 := by decide +kernel

theorem rows22250R_4667 : rowsJ2 150 151 71 72 ≤ 6320304165244 := by decide +kernel

theorem rows22250R_4668 : rowsJ2 150 151 72 73 ≤ 5534423384586 := by decide +kernel

theorem rows22250R_4669 : rowsJ2 150 151 73 74 ≤ 4804393861761 := by decide +kernel

theorem rows22250R_4670 : rowsJ2 150 151 74 75 ≤ 4129167035130 := by decide +kernel

theorem rows22250R_4671 : rowsJ2 150 151 75 76 ≤ 3507775664344 := by decide +kernel

theorem rows22250R_4672 : rowsJ2 150 151 76 77 ≤ 2939331283558 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4661
#print axioms SieveCert.rows22250R_4672
