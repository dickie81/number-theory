/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 521–524 of 549

File 133 of 140: the parts `rows22335R_521` … `rows22335R_524` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 27696 tests: rows 165–166, rows 167–168, rows 169–170, rows 171–173), each a
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

theorem rows22335R_521 : rows2 165 167 ≤ 9119180382961226 := by decide +kernel

theorem rows22335R_522 : rows2 167 169 ≤ 9703234647869535 := by decide +kernel

theorem rows22335R_523 : rows2 169 171 ≤ 10288999066041711 := by decide +kernel

theorem rows22335R_524 : rows2 171 174 ≤ 16532858399038399 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_521
#print axioms SieveCert.rows22335R_524
