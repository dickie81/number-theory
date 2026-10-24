/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 320–323 of 549

File 83 of 140: the parts `rows22335R_320` … `rows22335R_323` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29196 tests: row 101 columns 53–58, row 101 columns 59–63, row 101 columns
64–69, row 101 columns 70–76), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_320 : rowsJ2 101 102 53 59 ≤ 4643535945295 := by decide +kernel

theorem rows22335R_321 : rowsJ2 101 102 59 64 ≤ 0 := by decide +kernel

theorem rows22335R_322 : rowsJ2 101 102 64 70 ≤ 0 := by decide +kernel

theorem rows22335R_323 : rowsJ2 101 102 70 77 ≤ 2725768526892 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_320
#print axioms SieveCert.rows22335R_323
