/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 778–781 of 1732

File 195 of 430: the parts `rows22310R_778` … `rows22310R_781` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24386 tests: row 120 columns 107–109, row 120 columns 110–112, row 120
columns 113–116, row 120 columns 117–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_778 : rowsJ2 120 121 107 110 ≤ 6151380308163 := by decide +kernel

theorem rows22310R_779 : rowsJ2 120 121 110 113 ≤ 10359112681202 := by decide +kernel

theorem rows22310R_780 : rowsJ2 120 121 113 117 ≤ 22407531092130 := by decide +kernel

theorem rows22310R_781 : rowsJ2 120 121 117 400 ≤ 193414499673359 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_778
#print axioms SieveCert.rows22310R_781
