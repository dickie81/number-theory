/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4413–4422 of 5796

File 365 of 465: the parts `rows22250R_4413` … `rows22250R_4422` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 94706 tests: row 142 columns 67–67, row 142 columns 68–68, row 142 columns
69–69, row 142 columns 70–70, row 142 columns 71–71, row 142 columns 72–72, row 142 columns 73–73, row 142 columns
74–74, row 142 columns 75–75, row 142 columns 76–76), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_4413 : rowsJ2 142 143 67 68 ≤ 8661184426123 := by decide +kernel

theorem rows22250R_4414 : rowsJ2 142 143 68 69 ≤ 9156386621270 := by decide +kernel

theorem rows22250R_4415 : rowsJ2 142 143 69 70 ≤ 9596232669747 := by decide +kernel

theorem rows22250R_4416 : rowsJ2 142 143 70 71 ≤ 8716678022996 := by decide +kernel

theorem rows22250R_4417 : rowsJ2 142 143 71 72 ≤ 7878235282050 := by decide +kernel

theorem rows22250R_4418 : rowsJ2 142 143 72 73 ≤ 7096999415979 := by decide +kernel

theorem rows22250R_4419 : rowsJ2 142 143 73 74 ≤ 6353991104137 := by decide +kernel

theorem rows22250R_4420 : rowsJ2 142 143 74 75 ≤ 5665641620985 := by decide +kernel

theorem rows22250R_4421 : rowsJ2 142 143 75 76 ≤ 5012909644764 := by decide +kernel

theorem rows22250R_4422 : rowsJ2 142 143 76 77 ≤ 4412560501395 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4413
#print axioms SieveCert.rows22250R_4422
