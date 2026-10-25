/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 360–363 of 1732

File 90 of 430: the parts `rows22310R_360` … `rows22310R_363` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29556 tests: row 93 columns 0–34, row 93 columns 35–43, row 93 columns 44–49,
row 93 columns 50–55), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_360 : rowsJ2 93 94 0 35 ≤ 388555318474688 := by decide +kernel

theorem rows22310R_361 : rowsJ2 93 94 35 44 ≤ 60522388497575 := by decide +kernel

theorem rows22310R_362 : rowsJ2 93 94 44 50 ≤ 140704846158406 := by decide +kernel

theorem rows22310R_363 : rowsJ2 93 94 50 56 ≤ 209879571230863 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_360
#print axioms SieveCert.rows22310R_363
