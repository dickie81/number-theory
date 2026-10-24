/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 221–224 of 561

File 58 of 142: the parts `rows22325R_221` … `rows22325R_224` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 24585 tests: row 86 columns 75–79, row 86 columns 80–85, row 86 columns
86–299, row 87 columns 0–42), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_221 : rowsJ2 86 87 75 80 ≤ 5752403043068 := by decide +kernel

theorem rows22325R_222 : rowsJ2 86 87 80 86 ≤ 27084188742884 := by decide +kernel

theorem rows22325R_223 : rowsJ2 86 87 86 300 ≤ 8486804082824 := by decide +kernel

theorem rows22325R_224 : rowsJ2 87 88 0 43 ≤ 718206502921906 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_221
#print axioms SieveCert.rows22325R_224
