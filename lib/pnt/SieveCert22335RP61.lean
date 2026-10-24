/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 236–238 of 549

File 61 of 140: the parts `rows22335R_236` … `rows22335R_238` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (3 parts, 23327 tests: row 88 columns 82–299, row 89 columns 0–50, row 89 columns
51–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_236 : rowsJ2 88 89 82 300 ≤ 63572595510587 := by decide +kernel

theorem rows22335R_237 : rowsJ2 89 90 0 51 ≤ 756600267065743 := by decide +kernel

theorem rows22335R_238 : rowsJ2 89 90 51 62 ≤ 6202531533853 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_236
#print axioms SieveCert.rows22335R_238
