/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 114–117 of 549

File 30 of 140: the parts `rows22335R_114` … `rows22335R_117` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 24617 tests: row 68 columns 0–34, row 68 columns 35–47, row 68 columns 48–67,
row 68 columns 68–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_114 : rowsJ2 68 69 0 35 ≤ 621405566143317 := by decide +kernel

theorem rows22335R_115 : rowsJ2 68 69 35 48 ≤ 735022831693153 := by decide +kernel

theorem rows22335R_116 : rowsJ2 68 69 48 68 ≤ 527592286184202 := by decide +kernel

theorem rows22335R_117 : rowsJ2 68 69 68 300 ≤ 10287833644864 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_114
#print axioms SieveCert.rows22335R_117
