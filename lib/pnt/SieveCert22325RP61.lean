/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 233–236 of 561

File 61 of 142: the parts `rows22325R_233` … `rows22325R_236` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 29664 tests: row 88 columns 48–61, row 88 columns 62–66, row 88 columns
67–70, row 88 columns 71–75), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_233 : rowsJ2 88 89 48 62 ≤ 31130373022652 := by decide +kernel

theorem rows22325R_234 : rowsJ2 88 89 62 67 ≤ 1544202379932 := by decide +kernel

theorem rows22325R_235 : rowsJ2 88 89 67 71 ≤ 4230060885408 := by decide +kernel

theorem rows22325R_236 : rowsJ2 88 89 71 76 ≤ 2483357286751 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_233
#print axioms SieveCert.rows22325R_236
