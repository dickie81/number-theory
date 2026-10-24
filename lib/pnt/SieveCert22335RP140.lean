/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 548–548 of 549

File 140 of 140: the parts `rows22335R_548` … `rows22335R_548` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (1 parts, 4056 tests: rows 297–299), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_548 : rows2 297 300 ≤ 43529946319058425 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_548
