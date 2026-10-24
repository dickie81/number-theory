/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 522–525 of 561

File 133 of 142: the parts `rows22325R_522` … `rows22325R_525` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 28908 tests: rows 154–154, rows 155–155, rows 156–156, rows 157–157), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_522 : rows2 154 155 ≤ 3190456883970557 := by decide +kernel

theorem rows22325R_523 : rows2 155 156 ≤ 3205731621290682 := by decide +kernel

theorem rows22325R_524 : rows2 156 157 ≤ 3223564916488296 := by decide +kernel

theorem rows22325R_525 : rows2 157 158 ≤ 3308212224123296 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_522
#print axioms SieveCert.rows22325R_525
