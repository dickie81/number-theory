/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 118–121 of 561

File 31 of 142: the parts `rows22325R_118` … `rows22325R_121` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 25639 tests: row 69 columns 0–34, row 69 columns 35–48, row 69 columns 49–67,
row 69 columns 68–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_118 : rowsJ2 69 70 0 35 ≤ 598248146753954 := by decide +kernel

theorem rows22325R_119 : rowsJ2 69 70 35 49 ≤ 767690684942544 := by decide +kernel

theorem rows22325R_120 : rowsJ2 69 70 49 68 ≤ 449194538579415 := by decide +kernel

theorem rows22325R_121 : rowsJ2 69 70 68 300 ≤ 17144412433414 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_118
#print axioms SieveCert.rows22325R_121
