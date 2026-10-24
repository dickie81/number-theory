/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 536–539 of 549

File 137 of 140: the parts `rows22335R_536` … `rows22335R_539` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 28643 tests: rows 209–211, rows 212–214, rows 215–217, rows 218–220), each a
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

theorem rows22335R_536 : rows2 209 212 ≤ 29630667635868418 := by decide +kernel

theorem rows22335R_537 : rows2 212 215 ≤ 29959462318509670 := by decide +kernel

theorem rows22335R_538 : rows2 215 218 ≤ 30078937209326486 := by decide +kernel

theorem rows22335R_539 : rows2 218 221 ≤ 30430352518750964 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_536
#print axioms SieveCert.rows22335R_539
