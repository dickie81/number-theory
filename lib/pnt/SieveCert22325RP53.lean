/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 202–205 of 561

File 53 of 142: the parts `rows22325R_202` … `rows22325R_205` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 27946 tests: row 84 columns 38–61, row 84 columns 62–66, row 84 columns
67–70, row 84 columns 71–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_202 : rowsJ2 84 85 38 62 ≤ 327823867474439 := by decide +kernel

theorem rows22325R_203 : rowsJ2 84 85 62 67 ≤ 1596924545175 := by decide +kernel

theorem rows22325R_204 : rowsJ2 84 85 67 71 ≤ 8161383517546 := by decide +kernel

theorem rows22325R_205 : rowsJ2 84 85 71 75 ≤ 7420865161314 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_202
#print axioms SieveCert.rows22325R_205
