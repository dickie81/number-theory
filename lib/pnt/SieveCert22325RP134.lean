/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 526–530 of 561

File 134 of 142: the parts `rows22325R_526` … `rows22325R_530` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (5 parts, 27200 tests: rows 158–158, rows 159–159, rows 160–160, rows 161–161, rows
162–162), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22325R_526 : rows2 158 159 ≤ 3460132363410658 := by decide +kernel

theorem rows22325R_527 : rows2 159 160 ≤ 3606845483727408 := by decide +kernel

theorem rows22325R_528 : rows2 160 161 ≤ 3751584812409919 := by decide +kernel

theorem rows22325R_529 : rows2 161 162 ≤ 3896663327899253 := by decide +kernel

theorem rows22325R_530 : rows2 162 163 ≤ 4042076198237262 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_526
#print axioms SieveCert.rows22325R_530
