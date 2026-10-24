/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 525–528 of 549

File 134 of 140: the parts `rows22335R_525` … `rows22335R_528` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 28679 tests: rows 174–176, rows 177–179, rows 180–183, rows 184–187), each a
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

theorem rows22335R_525 : rows2 174 177 ≤ 17861332247988174 := by decide +kernel

theorem rows22335R_526 : rows2 177 180 ≤ 19223403699937817 := by decide +kernel

theorem rows22335R_527 : rows2 180 184 ≤ 27818777942570183 := by decide +kernel

theorem rows22335R_528 : rows2 184 188 ≤ 29965818340938796 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_525
#print axioms SieveCert.rows22335R_528
