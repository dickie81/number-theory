/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 198–201 of 561

File 52 of 142: the parts `rows22325R_198` … `rows22325R_201` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 28826 tests: row 83 columns 71–74, row 83 columns 75–78, row 83 columns
79–299, row 84 columns 0–37), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_198 : rowsJ2 83 84 71 75 ≤ 9225155250850 := by decide +kernel

theorem rows22325R_199 : rowsJ2 83 84 75 79 ≤ 7151028233182 := by decide +kernel

theorem rows22325R_200 : rowsJ2 83 84 79 300 ≤ 15377845800325 := by decide +kernel

theorem rows22325R_201 : rowsJ2 84 85 0 38 ≤ 620874287718149 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_198
#print axioms SieveCert.rows22325R_201
