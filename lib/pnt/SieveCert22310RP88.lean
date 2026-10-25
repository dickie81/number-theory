/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 353–355 of 1732

File 88 of 430: the parts `rows22310R_353` … `rows22310R_355` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 22390 tests: row 92 columns 44–49, row 92 columns 50–55, row 92 columns
56–63), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22310R_353 : rowsJ2 92 93 44 50 ≤ 133294883531488 := by decide +kernel

theorem rows22310R_354 : rowsJ2 92 93 50 56 ≤ 212630596600440 := by decide +kernel

theorem rows22310R_355 : rowsJ2 92 93 56 64 ≤ 238198530086201 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_353
#print axioms SieveCert.rows22310R_355
