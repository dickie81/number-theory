/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 324–327 of 549

File 84 of 140: the parts `rows22335R_324` … `rows22335R_327` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 27569 tests: row 101 columns 77–299, row 102 columns 0–52, row 102 columns
53–58, row 102 columns 59–63), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_324 : rowsJ2 101 102 77 300 ≤ 847971367779035 := by decide +kernel

theorem rows22335R_325 : rowsJ2 102 103 0 53 ≤ 441200717838892 := by decide +kernel

theorem rows22335R_326 : rowsJ2 102 103 53 59 ≤ 7513399222370 := by decide +kernel

theorem rows22335R_327 : rowsJ2 102 103 59 64 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_324
#print axioms SieveCert.rows22335R_327
