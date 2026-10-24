/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 540–543 of 549

File 138 of 140: the parts `rows22335R_540` … `rows22335R_543` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 26744 tests: rows 221–223, rows 224–226, rows 227–229, rows 230–233), each a
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

theorem rows22335R_540 : rows2 221 224 ≤ 30579125933777690 := by decide +kernel

theorem rows22335R_541 : rows2 224 227 ≤ 30945933618004608 := by decide +kernel

theorem rows22335R_542 : rows2 227 230 ≤ 31069304582940749 := by decide +kernel

theorem rows22335R_543 : rows2 230 234 ≤ 41863655497841900 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_540
#print axioms SieveCert.rows22335R_543
