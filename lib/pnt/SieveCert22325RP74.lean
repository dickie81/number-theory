/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 284–286 of 561

File 74 of 142: the parts `rows22325R_284` … `rows22325R_286` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (3 parts, 23315 tests: row 95 columns 0–52, row 95 columns 53–60, row 95 columns
61–65), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_284 : rowsJ2 95 96 0 53 ≤ 590621219256247 := by decide +kernel

theorem rows22325R_285 : rowsJ2 95 96 53 61 ≤ 0 := by decide +kernel

theorem rows22325R_286 : rowsJ2 95 96 61 66 ≤ 178292218362 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_284
#print axioms SieveCert.rows22325R_286
