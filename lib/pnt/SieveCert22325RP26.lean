/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 101–103 of 561

File 26 of 142: the parts `rows22325R_101` … `rows22325R_103` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (3 parts, 22847 tests: row 64 columns 0–34, row 64 columns 35–44, row 64 columns
45–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22325R_101 : rowsJ2 64 65 0 35 ≤ 753962983880797 := by decide +kernel

theorem rows22325R_102 : rowsJ2 64 65 35 45 ≤ 585834559004125 := by decide +kernel

theorem rows22325R_103 : rowsJ2 64 65 45 300 ≤ 795627296822349 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_101
#print axioms SieveCert.rows22325R_103
