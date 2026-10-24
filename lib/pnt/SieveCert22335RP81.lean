/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 313–315 of 549

File 81 of 140: the parts `rows22335R_313` … `rows22335R_315` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (3 parts, 22901 tests: row 100 columns 0–52, row 100 columns 53–59, row 100 columns
60–64), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22335R_313 : rowsJ2 100 101 0 53 ≤ 479273007698218 := by decide +kernel

theorem rows22335R_314 : rowsJ2 100 101 53 60 ≤ 2628097459922 := by decide +kernel

theorem rows22335R_315 : rowsJ2 100 101 60 65 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_313
#print axioms SieveCert.rows22335R_315
