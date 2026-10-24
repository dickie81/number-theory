/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 251–254 of 549

File 65 of 140: the parts `rows22335R_251` … `rows22335R_254` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29982 tests: row 91 columns 0–52, row 91 columns 53–60, row 91 columns 61–65,
row 91 columns 66–70), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_251 : rowsJ2 91 92 0 53 ≤ 699618580252383 := by decide +kernel

theorem rows22335R_252 : rowsJ2 91 92 53 61 ≤ 0 := by decide +kernel

theorem rows22335R_253 : rowsJ2 91 92 61 66 ≤ 699904540319 := by decide +kernel

theorem rows22335R_254 : rowsJ2 91 92 66 71 ≤ 1083325003058 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_251
#print axioms SieveCert.rows22335R_254
