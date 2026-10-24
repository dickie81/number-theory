/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 307–309 of 561

File 80 of 142: the parts `rows22325R_307` … `rows22325R_309` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (3 parts, 22299 tests: row 98 columns 60–64, row 98 columns 65–69, row 98 columns
70–75), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22325R_307 : rowsJ2 98 99 60 65 ≤ 0 := by decide +kernel

theorem rows22325R_308 : rowsJ2 98 99 65 70 ≤ 0 := by decide +kernel

theorem rows22325R_309 : rowsJ2 98 99 70 76 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_307
#print axioms SieveCert.rows22325R_309
