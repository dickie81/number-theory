/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 268–271 of 561

File 70 of 142: the parts `rows22325R_268` … `rows22325R_271` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 29454 tests: row 92 columns 75–80, row 92 columns 81–299, row 93 columns
0–52, row 93 columns 53–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_268 : rowsJ2 92 93 75 81 ≤ 9268360774745 := by decide +kernel

theorem rows22325R_269 : rowsJ2 92 93 81 300 ≤ 867944880135392 := by decide +kernel

theorem rows22325R_270 : rowsJ2 93 94 0 53 ≤ 642927283825877 := by decide +kernel

theorem rows22325R_271 : rowsJ2 93 94 53 61 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_268
#print axioms SieveCert.rows22325R_271
