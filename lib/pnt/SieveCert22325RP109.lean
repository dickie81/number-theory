/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 420–423 of 561

File 109 of 142: the parts `rows22325R_420` … `rows22325R_423` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 22716 tests: row 118 columns 55–61, row 118 columns 62–71, row 118 columns
72–299, row 119 columns 0–47), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_420 : rowsJ2 118 119 55 62 ≤ 42059229446141 := by decide +kernel

theorem rows22325R_421 : rowsJ2 118 119 62 72 ≤ 8652781035121 := by decide +kernel

theorem rows22325R_422 : rowsJ2 118 119 72 300 ≤ 101394806062525 := by decide +kernel

theorem rows22325R_423 : rowsJ2 119 120 0 48 ≤ 197867443303948 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_420
#print axioms SieveCert.rows22325R_423
