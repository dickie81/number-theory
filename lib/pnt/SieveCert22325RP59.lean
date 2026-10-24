/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 225–228 of 561

File 59 of 142: the parts `rows22325R_225` … `rows22325R_228` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 28079 tests: row 87 columns 43–61, row 87 columns 62–66, row 87 columns
67–70, row 87 columns 71–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_225 : rowsJ2 87 88 43 62 ≤ 114779749086785 := by decide +kernel

theorem rows22325R_226 : rowsJ2 87 88 62 67 ≤ 1557492689558 := by decide +kernel

theorem rows22325R_227 : rowsJ2 87 88 67 71 ≤ 5220718643249 := by decide +kernel

theorem rows22325R_228 : rowsJ2 87 88 71 75 ≤ 3202481649155 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_225
#print axioms SieveCert.rows22325R_228
