/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 556–559 of 561

File 142 of 143: the parts `rows22322R_556` … `rows22322R_559` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 29035 tests: rows 234–283, rows 284–288, rows 289–292, rows 293–296), each a
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

theorem rows22322R_556 : rows2 234 284 ≤ 42477002496173776 := by decide +kernel

theorem rows22322R_557 : rows2 284 289 ≤ 58658935364352615 := by decide +kernel

theorem rows22322R_558 : rows2 289 293 ≤ 50659164235955121 := by decide +kernel

theorem rows22322R_559 : rows2 293 297 ≤ 54416048718733859 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_556
#print axioms SieveCert.rows22322R_559
