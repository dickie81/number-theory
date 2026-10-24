/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 220–223 of 549

File 57 of 140: the parts `rows22335R_220` … `rows22335R_223` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29752 tests: row 86 columns 76–80, row 86 columns 81–299, row 87 columns
0–42, row 87 columns 43–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_220 : rowsJ2 86 87 76 81 ≤ 7804803266901 := by decide +kernel

theorem rows22335R_221 : rowsJ2 86 87 81 300 ≤ 35923310423189 := by decide +kernel

theorem rows22335R_222 : rowsJ2 87 88 0 43 ≤ 717411054902096 := by decide +kernel

theorem rows22335R_223 : rowsJ2 87 88 43 62 ≤ 114644200502617 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_220
#print axioms SieveCert.rows22335R_223
