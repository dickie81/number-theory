/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 552–555 of 561

File 140 of 142: the parts `rows22325R_552` … `rows22325R_555` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 26744 tests: rows 221–223, rows 224–226, rows 227–229, rows 230–233), each a
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

theorem rows22325R_552 : rows2 221 224 ≤ 30587809399047926 := by decide +kernel

theorem rows22325R_553 : rows2 224 227 ≤ 30954856073480096 := by decide +kernel

theorem rows22325R_554 : rows2 227 230 ≤ 31078321242040145 := by decide +kernel

theorem rows22325R_555 : rows2 230 234 ≤ 41875984377227984 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_552
#print axioms SieveCert.rows22325R_555
