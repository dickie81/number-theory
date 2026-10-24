/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 114–117 of 561

File 30 of 142: the parts `rows22325R_114` … `rows22325R_117` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 24617 tests: row 68 columns 0–34, row 68 columns 35–47, row 68 columns 48–67,
row 68 columns 68–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22325R_114 : rowsJ2 68 69 0 35 ≤ 622181161439889 := by decide +kernel

theorem rows22325R_115 : rowsJ2 68 69 35 48 ≤ 735779805749665 := by decide +kernel

theorem rows22325R_116 : rowsJ2 68 69 48 68 ≤ 528170674073088 := by decide +kernel

theorem rows22325R_117 : rowsJ2 68 69 68 300 ≤ 10298975629866 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_114
#print axioms SieveCert.rows22325R_117
