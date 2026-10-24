/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 155–158 of 549

File 41 of 140: the parts `rows22335R_155` … `rows22335R_158` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29053 tests: row 77 columns 0–34, row 77 columns 35–60, row 77 columns 61–67,
row 77 columns 68–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_155 : rowsJ2 77 78 0 35 ≤ 522107195340534 := by decide +kernel

theorem rows22335R_156 : rowsJ2 77 78 35 61 ≤ 754591714796129 := by decide +kernel

theorem rows22335R_157 : rowsJ2 77 78 61 68 ≤ 18659276417662 := by decide +kernel

theorem rows22335R_158 : rowsJ2 77 78 68 72 ≤ 12807854007781 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_155
#print axioms SieveCert.rows22335R_158
