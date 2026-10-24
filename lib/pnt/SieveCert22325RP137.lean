/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 540–543 of 561

File 137 of 142: the parts `rows22325R_540` … `rows22325R_543` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 27117 tests: rows 184–187, rows 188–190, rows 191–193, rows 194–196), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_540 : rows2 184 188 ≤ 29972735060600473 := by decide +kernel

theorem rows22325R_541 : rows2 188 191 ≤ 23324854748732612 := by decide +kernel

theorem rows22325R_542 : rows2 191 194 ≤ 24211979554474667 := by decide +kernel

theorem rows22325R_543 : rows2 194 197 ≤ 25147230782198562 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_540
#print axioms SieveCert.rows22325R_543
