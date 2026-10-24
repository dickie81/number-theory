/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 126–129 of 561

File 33 of 142: the parts `rows22325R_126` … `rows22325R_129` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 28403 tests: row 71 columns 0–34, row 71 columns 35–50, row 71 columns 51–67,
row 71 columns 68–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22325R_126 : rowsJ2 71 72 0 35 ≤ 561388007232279 := by decide +kernel

theorem rows22325R_127 : rowsJ2 71 72 35 51 ≤ 802620092003199 := by decide +kernel

theorem rows22325R_128 : rowsJ2 71 72 51 68 ≤ 311488563963783 := by decide +kernel

theorem rows22325R_129 : rowsJ2 71 72 68 300 ≤ 23314790209081 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_126
#print axioms SieveCert.rows22325R_129
