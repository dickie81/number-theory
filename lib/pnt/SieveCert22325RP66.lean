/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 253–256 of 561

File 66 of 142: the parts `rows22325R_253` … `rows22325R_256` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 23991 tests: row 90 columns 75–79, row 90 columns 80–85, row 90 columns
86–299, row 91 columns 0–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_253 : rowsJ2 90 91 75 80 ≤ 4912286239166 := by decide +kernel

theorem rows22325R_254 : rowsJ2 90 91 80 86 ≤ 35332342265829 := by decide +kernel

theorem rows22325R_255 : rowsJ2 90 91 86 300 ≤ 470789376952778 := by decide +kernel

theorem rows22325R_256 : rowsJ2 91 92 0 53 ≤ 700406106182189 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_253
#print axioms SieveCert.rows22325R_256
