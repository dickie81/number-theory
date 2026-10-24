/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 192–195 of 549

File 50 of 140: the parts `rows22335R_192` … `rows22335R_195` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 25822 tests: row 82 columns 76–80, row 82 columns 81–299, row 83 columns
0–36, row 83 columns 37–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_192 : rowsJ2 82 83 76 81 ≤ 9983198062222 := by decide +kernel

theorem rows22335R_193 : rowsJ2 82 83 81 300 ≤ 6467980968793 := by decide +kernel

theorem rows22335R_194 : rowsJ2 83 84 0 37 ≤ 591248728171386 := by decide +kernel

theorem rows22335R_195 : rowsJ2 83 84 37 62 ≤ 400211047178231 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_192
#print axioms SieveCert.rows22335R_195
