/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 400–403 of 561

File 104 of 142: the parts `rows22325R_400` … `rows22325R_403` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 25720 tests: row 114 columns 56–61, row 114 columns 62–69, row 114 columns
70–299, row 115 columns 0–48), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_400 : rowsJ2 114 115 56 62 ≤ 33745376771838 := by decide +kernel

theorem rows22325R_401 : rowsJ2 114 115 62 70 ≤ 9780330342682 := by decide +kernel

theorem rows22325R_402 : rowsJ2 114 115 70 300 ≤ 107041062241210 := by decide +kernel

theorem rows22325R_403 : rowsJ2 115 116 0 49 ≤ 239045584533207 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_400
#print axioms SieveCert.rows22325R_403
