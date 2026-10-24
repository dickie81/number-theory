/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 328–331 of 549

File 85 of 140: the parts `rows22335R_328` … `rows22335R_331` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 26704 tests: row 102 columns 64–69, row 102 columns 70–76, row 102 columns
77–299, row 103 columns 0–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_328 : rowsJ2 102 103 64 70 ≤ 0 := by decide +kernel

theorem rows22335R_329 : rowsJ2 102 103 70 77 ≤ 2879316693172 := by decide +kernel

theorem rows22335R_330 : rowsJ2 102 103 77 300 ≤ 834265310268429 := by decide +kernel

theorem rows22335R_331 : rowsJ2 103 104 0 52 ≤ 421614800295504 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_328
#print axioms SieveCert.rows22335R_331
