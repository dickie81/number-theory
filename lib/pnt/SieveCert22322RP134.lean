/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 524–527 of 561

File 134 of 143: the parts `rows22322R_524` … `rows22322R_527` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 25620 tests: rows 156–156, rows 157–157, rows 158–158, rows 159–159), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_524 : rows2 156 157 ≤ 3312275992895156 := by decide +kernel

theorem rows22322R_525 : rows2 157 158 ≤ 3396725119446430 := by decide +kernel

theorem rows22322R_526 : rows2 158 159 ≤ 3550369099802688 := by decide +kernel

theorem rows22322R_527 : rows2 159 160 ≤ 3698809005261105 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_524
#print axioms SieveCert.rows22322R_527
