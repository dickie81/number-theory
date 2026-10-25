/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 141–144 of 1732

File 35 of 430: the parts `rows22310R_141` … `rows22310R_144` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29260 tests: row 67 columns 0–34, row 67 columns 35–43, row 67 columns 44–49,
row 67 columns 50–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22310R_141 : rowsJ2 67 68 0 35 ≤ 1026969275717210 := by decide +kernel

theorem rows22310R_142 : rowsJ2 67 68 35 44 ≤ 280950527431080 := by decide +kernel

theorem rows22310R_143 : rowsJ2 67 68 44 50 ≤ 124229197896377 := by decide +kernel

theorem rows22310R_144 : rowsJ2 67 68 50 55 ≤ 108904947223731 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_141
#print axioms SieveCert.rows22310R_144
