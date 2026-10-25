/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 548–551 of 561

File 140 of 143: the parts `rows22322R_548` … `rows22322R_551` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 28751 tests: rows 209–211, rows 212–214, rows 215–217, rows 218–220), each a
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

theorem rows22322R_548 : rows2 209 212 ≤ 29860823746208885 := by decide +kernel

theorem rows22322R_549 : rows2 212 215 ≤ 29935775031925784 := by decide +kernel

theorem rows22322R_550 : rows2 215 218 ≤ 30328156061778844 := by decide +kernel

theorem rows22322R_551 : rows2 218 221 ≤ 30411376522570816 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_548
#print axioms SieveCert.rows22322R_551
