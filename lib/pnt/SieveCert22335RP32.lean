/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 122–125 of 549

File 32 of 140: the parts `rows22335R_122` … `rows22335R_125` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 26908 tests: row 70 columns 0–34, row 70 columns 35–49, row 70 columns 50–67,
row 70 columns 68–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_122 : rowsJ2 70 71 0 35 ≤ 577277635177361 := by decide +kernel

theorem rows22335R_123 : rowsJ2 70 71 35 50 ≤ 787503189154317 := by decide +kernel

theorem rows22335R_124 : rowsJ2 70 71 50 68 ≤ 376526133424969 := by decide +kernel

theorem rows22335R_125 : rowsJ2 70 71 68 300 ≤ 21281798338133 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_122
#print axioms SieveCert.rows22335R_125
