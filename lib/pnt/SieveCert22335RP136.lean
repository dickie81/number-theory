/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 533–535 of 549

File 136 of 140: the parts `rows22335R_533` … `rows22335R_535` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (3 parts, 22588 tests: rows 200–202, rows 203–205, rows 206–208), each a sum of refined
costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_533 : rows2 200 203 ≤ 27387077268997050 := by decide +kernel

theorem rows22335R_534 : rows2 203 206 ≤ 28672386512787122 := by decide +kernel

theorem rows22335R_535 : rows2 206 209 ≤ 29484256008788702 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_533
#print axioms SieveCert.rows22335R_535
