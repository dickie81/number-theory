/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 224–227 of 549

File 58 of 140: the parts `rows22335R_224` … `rows22335R_227` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 28630 tests: row 87 columns 62–66, row 87 columns 67–70, row 87 columns
71–75, row 87 columns 76–80), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_224 : rowsJ2 87 88 62 67 ≤ 1556484862785 := by decide +kernel

theorem rows22335R_225 : rowsJ2 87 88 67 71 ≤ 4263676662366 := by decide +kernel

theorem rows22335R_226 : rowsJ2 87 88 71 76 ≤ 2702267391534 := by decide +kernel

theorem rows22335R_227 : rowsJ2 87 88 76 81 ≤ 8035906865549 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_224
#print axioms SieveCert.rows22335R_227
