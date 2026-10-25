/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 372–374 of 1732

File 93 of 430: the parts `rows22310R_372` … `rows22310R_374` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 22579 tests: row 94 columns 50–55, row 94 columns 56–64, row 94 columns
65–81), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22310R_372 : rowsJ2 94 95 50 56 ≤ 207046509694096 := by decide +kernel

theorem rows22310R_373 : rowsJ2 94 95 56 65 ≤ 248258215433604 := by decide +kernel

theorem rows22310R_374 : rowsJ2 94 95 65 82 ≤ 279515816839217 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_372
#print axioms SieveCert.rows22310R_374
