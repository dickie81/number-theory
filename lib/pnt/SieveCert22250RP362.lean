/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4375–4384 of 5796

File 362 of 465: the parts `rows22250R_4375` … `rows22250R_4384` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 95741 tests: row 141 columns 62–62, row 141 columns 63–63, row 141 columns
64–64, row 141 columns 65–65, row 141 columns 66–66, row 141 columns 67–67, row 141 columns 68–68, row 141 columns
69–69, row 141 columns 70–70, row 141 columns 71–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_4375 : rowsJ2 141 142 62 63 ≤ 5146607332770 := by decide +kernel

theorem rows22250R_4376 : rowsJ2 141 142 63 64 ≤ 5803458454111 := by decide +kernel

theorem rows22250R_4377 : rowsJ2 141 142 64 65 ≤ 6457253340614 := by decide +kernel

theorem rows22250R_4378 : rowsJ2 141 142 65 66 ≤ 7056722421012 := by decide +kernel

theorem rows22250R_4379 : rowsJ2 141 142 66 67 ≤ 7618783377920 := by decide +kernel

theorem rows22250R_4380 : rowsJ2 141 142 67 68 ≤ 8125983837563 := by decide +kernel

theorem rows22250R_4381 : rowsJ2 141 142 68 69 ≤ 8595231444967 := by decide +kernel

theorem rows22250R_4382 : rowsJ2 141 142 69 70 ≤ 9008730039683 := by decide +kernel

theorem rows22250R_4383 : rowsJ2 141 142 70 71 ≤ 8768939948414 := by decide +kernel

theorem rows22250R_4384 : rowsJ2 141 142 71 72 ≤ 7931146391932 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4375
#print axioms SieveCert.rows22250R_4384
