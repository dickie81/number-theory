/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4600–4609 of 5796

File 380 of 465: the parts `rows22250R_4600` … `rows22250R_4609` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 96760 tests: row 148 columns 65–65, row 148 columns 66–66, row 148 columns
67–67, row 148 columns 68–68, row 148 columns 69–69, row 148 columns 70–70, row 148 columns 71–71, row 148 columns
72–72, row 148 columns 73–73, row 148 columns 74–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_4600 : rowsJ2 148 149 65 66 ≤ 10847619444539 := by decide +kernel

theorem rows22250R_4601 : rowsJ2 148 149 66 67 ≤ 11595450397298 := by decide +kernel

theorem rows22250R_4602 : rowsJ2 148 149 67 68 ≤ 10544592003918 := by decide +kernel

theorem rows22250R_4603 : rowsJ2 148 149 68 69 ≤ 9556797296170 := by decide +kernel

theorem rows22250R_4604 : rowsJ2 148 149 69 70 ≤ 8613657149737 := by decide +kernel

theorem rows22250R_4605 : rowsJ2 148 149 70 71 ≤ 7730402419893 := by decide +kernel

theorem rows22250R_4606 : rowsJ2 148 149 71 72 ≤ 6888621723856 := by decide +kernel

theorem rows22250R_4607 : rowsJ2 148 149 72 73 ≤ 6103881707849 := by decide +kernel

theorem rows22250R_4608 : rowsJ2 148 149 73 74 ≤ 5357741142588 := by decide +kernel

theorem rows22250R_4609 : rowsJ2 148 149 74 75 ≤ 4666097627264 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4600
#print axioms SieveCert.rows22250R_4609
