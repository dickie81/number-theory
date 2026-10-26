/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 533–536 of 561

File 136 of 143: the parts `rows22322R_533` … `rows22322R_536` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 27840 tests: rows 165–166, rows 167–168, rows 169–170, rows 171–173), each a
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

theorem rows22322R_533 : rows2 165 167 ≤ 9315526499199462 := by decide +kernel

theorem rows22322R_534 : rows2 167 169 ≤ 9911327084846564 := by decide +kernel

theorem rows22322R_535 : rows2 169 171 ≤ 10508426935087714 := by decide +kernel

theorem rows22322R_536 : rows2 171 174 ≤ 16882285197246136 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_533
#print axioms SieveCert.rows22322R_536
