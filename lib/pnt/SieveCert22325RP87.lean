/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 333–336 of 561

File 87 of 142: the parts `rows22325R_333` … `rows22325R_336` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 27753 tests: row 102 columns 59–63, row 102 columns 64–69, row 102 columns
70–76, row 102 columns 77–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_333 : rowsJ2 102 103 59 64 ≤ 0 := by decide +kernel

theorem rows22325R_334 : rowsJ2 102 103 64 70 ≤ 0 := by decide +kernel

theorem rows22325R_335 : rowsJ2 102 103 70 77 ≤ 986605186229 := by decide +kernel

theorem rows22325R_336 : rowsJ2 102 103 77 300 ≤ 828642276130508 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_333
#print axioms SieveCert.rows22325R_336
