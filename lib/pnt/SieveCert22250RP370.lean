/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4476–4485 of 5796

File 370 of 465: the parts `rows22250R_4476` … `rows22250R_4485` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 98362 tests: row 144 columns 66–66, row 144 columns 67–67, row 144 columns
68–68, row 144 columns 69–69, row 144 columns 70–70, row 144 columns 71–71, row 144 columns 72–72, row 144 columns
73–73, row 144 columns 74–74, row 144 columns 75–75), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4476 : rowsJ2 144 145 66 67 ≤ 9196062328446 := by decide +kernel

theorem rows22250R_4477 : rowsJ2 144 145 67 68 ≤ 9781512388080 := by decide +kernel

theorem rows22250R_4478 : rowsJ2 144 145 68 69 ≤ 10329881974622 := by decide +kernel

theorem rows22250R_4479 : rowsJ2 144 145 69 70 ≤ 9389054335304 := by decide +kernel

theorem rows22250R_4480 : rowsJ2 144 145 70 71 ≤ 8508225689536 := by decide +kernel

theorem rows22250R_4481 : rowsJ2 144 145 71 72 ≤ 7668633784672 := by decide +kernel

theorem rows22250R_4482 : rowsJ2 144 145 72 73 ≤ 6886193931579 := by decide +kernel

theorem rows22250R_4483 : rowsJ2 144 145 73 74 ≤ 6142109948827 := by decide +kernel

theorem rows22250R_4484 : rowsJ2 144 145 74 75 ≤ 5452631610071 := by decide +kernel

theorem rows22250R_4485 : rowsJ2 144 145 75 76 ≤ 4798902934489 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4476
#print axioms SieveCert.rows22250R_4485
