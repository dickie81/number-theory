/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1379–1381 of 1732

File 346 of 430: the parts `rows22310R_1379` … `rows22310R_1381` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 22425 tests: row 164 columns 69–72, row 164 columns 73–76, row 164 columns
77–81), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1379 : rowsJ2 164 165 69 73 ≤ 24759421281130 := by decide +kernel

theorem rows22310R_1380 : rowsJ2 164 165 73 77 ≤ 15776558366218 := by decide +kernel

theorem rows22310R_1381 : rowsJ2 164 165 77 82 ≤ 10167029302938 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1379
#print axioms SieveCert.rows22310R_1381
