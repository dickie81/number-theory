/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 91–94 of 549

File 23 of 140: the parts `rows22335R_91` … `rows22335R_94` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 23814 tests: row 61 columns 0–34, row 61 columns 35–44, row 61 columns 45–60,
row 61 columns 61–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_91 : rowsJ2 61 62 0 35 ≤ 889591823195595 := by decide +kernel

theorem rows22335R_92 : rowsJ2 61 62 35 45 ≤ 560229123848617 := by decide +kernel

theorem rows22335R_93 : rowsJ2 61 62 45 61 ≤ 796960797520403 := by decide +kernel

theorem rows22335R_94 : rowsJ2 61 62 61 300 ≤ 32326905915385 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_91
#print axioms SieveCert.rows22335R_94
