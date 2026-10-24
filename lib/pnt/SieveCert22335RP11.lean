/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 44–47 of 549

File 11 of 140: the parts `rows22335R_44` … `rows22335R_47` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 27405 tests: row 48 columns 44–299, row 49 columns 0–34, row 49 columns
35–43, row 49 columns 44–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_44 : rowsJ2 48 49 44 300 ≤ 372119521049994 := by decide +kernel

theorem rows22335R_45 : rowsJ2 49 50 0 35 ≤ 1667800590378210 := by decide +kernel

theorem rows22335R_46 : rowsJ2 49 50 35 44 ≤ 359508428872898 := by decide +kernel

theorem rows22335R_47 : rowsJ2 49 50 44 300 ≤ 459198466425711 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_44
#print axioms SieveCert.rows22335R_47
