/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 492–495 of 549

File 127 of 140: the parts `rows22335R_492` … `rows22335R_495` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 23284 tests: row 145 columns 0–39, row 145 columns 40–299, row 146 columns
0–39, row 146 columns 40–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_492 : rowsJ2 145 146 0 40 ≤ 173688532497915 := by decide +kernel

theorem rows22335R_493 : rowsJ2 145 146 40 300 ≤ 2875901725887266 := by decide +kernel

theorem rows22335R_494 : rowsJ2 146 147 0 40 ≤ 185327206814243 := by decide +kernel

theorem rows22335R_495 : rowsJ2 146 147 40 300 ≤ 2879079425931627 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_492
#print axioms SieveCert.rows22335R_495
