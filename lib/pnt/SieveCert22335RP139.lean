/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 544–547 of 549

File 139 of 140: the parts `rows22335R_544` … `rows22335R_547` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 28925 tests: rows 234–283, rows 284–288, rows 289–292, rows 293–296), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_544 : rows2 234 284 ≤ 42224240765067071 := by decide +kernel

theorem rows22335R_545 : rows2 284 289 ≤ 58591441517500333 := by decide +kernel

theorem rows22335R_546 : rows2 289 293 ≤ 50597069507182635 := by decide +kernel

theorem rows22335R_547 : rows2 293 297 ≤ 54345288196445035 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_544
#print axioms SieveCert.rows22335R_547
