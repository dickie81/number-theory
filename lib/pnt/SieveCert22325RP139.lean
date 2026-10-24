/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 548–551 of 561

File 139 of 142: the parts `rows22325R_548` … `rows22325R_551` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 28643 tests: rows 209–211, rows 212–214, rows 215–217, rows 218–220), each a
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

theorem rows22325R_548 : rows2 209 212 ≤ 29638830130395847 := by decide +kernel

theorem rows22325R_549 : rows2 212 215 ≤ 29967786796544111 := by decide +kernel

theorem rows22325R_550 : rows2 215 218 ≤ 30087308421520933 := by decide +kernel

theorem rows22325R_551 : rows2 218 221 ≤ 30438932625154209 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_548
#print axioms SieveCert.rows22325R_551
