/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1046–1049 of 1732

File 262 of 430: the parts `rows22310R_1046` … `rows22310R_1049` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24812 tests: row 136 columns 101–104, row 136 columns 105–109, row 136
columns 110–399, row 137 columns 0–39), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22310R_1046 : rowsJ2 136 137 101 105 ≤ 4326565590591 := by decide +kernel

theorem rows22310R_1047 : rowsJ2 136 137 105 110 ≤ 19004850830920 := by decide +kernel

theorem rows22310R_1048 : rowsJ2 136 137 110 400 ≤ 586459639012669 := by decide +kernel

theorem rows22310R_1049 : rowsJ2 137 138 0 40 ≤ 243265124879758 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1046
#print axioms SieveCert.rows22310R_1049
