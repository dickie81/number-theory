/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 202–205 of 561

File 53 of 143: the parts `rows22322R_202` … `rows22322R_205` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 27946 tests: row 84 columns 38–61, row 84 columns 62–66, row 84 columns
67–70, row 84 columns 71–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_202 : rowsJ2 84 85 38 62 ≤ 329135084716636 := by decide +kernel

theorem rows22322R_203 : rowsJ2 84 85 62 67 ≤ 1600603118008 := by decide +kernel

theorem rows22322R_204 : rowsJ2 84 85 67 71 ≤ 8179464596563 := by decide +kernel

theorem rows22322R_205 : rowsJ2 84 85 71 75 ≤ 7437814318521 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_202
#print axioms SieveCert.rows22322R_205
