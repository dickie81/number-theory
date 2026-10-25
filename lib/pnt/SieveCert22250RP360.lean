/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4348–4358 of 5796

File 360 of 465: the parts `rows22250R_4348` … `rows22250R_4358` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 95348 tests: row 140 columns 68–68, row 140 columns 69–69, row 140 columns
70–70, row 140 columns 71–71, row 140 columns 72–72, row 140 columns 73–73, row 140 columns 74–74, row 140 columns
75–75, row 140 columns 76–76, row 140 columns 77–77, row 140 columns 78–78), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4348 : rowsJ2 140 141 68 69 ≤ 8067154957695 := by decide +kernel

theorem rows22250R_4349 : rowsJ2 140 141 69 70 ≤ 8454567611755 := by decide +kernel

theorem rows22250R_4350 : rowsJ2 140 141 70 71 ≤ 8802812571664 := by decide +kernel

theorem rows22250R_4351 : rowsJ2 140 141 71 72 ≤ 7965584449074 := by decide +kernel

theorem rows22250R_4352 : rowsJ2 140 141 72 73 ≤ 7185617487594 := by decide +kernel

theorem rows22250R_4353 : rowsJ2 140 141 73 74 ≤ 6443745309734 := by decide +kernel

theorem rows22250R_4354 : rowsJ2 140 141 74 75 ≤ 5756584468134 := by decide +kernel

theorem rows22250R_4355 : rowsJ2 140 141 75 76 ≤ 5104904356419 := by decide +kernel

theorem rows22250R_4356 : rowsJ2 140 141 76 77 ≤ 4505657586263 := by decide +kernel

theorem rows22250R_4357 : rowsJ2 140 141 77 78 ≤ 3939524805991 := by decide +kernel

theorem rows22250R_4358 : rowsJ2 140 141 78 79 ≤ 3423794567787 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4348
#print axioms SieveCert.rows22250R_4358
