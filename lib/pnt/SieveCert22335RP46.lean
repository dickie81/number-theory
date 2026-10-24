/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 175–179 of 549

File 46 of 140: the parts `rows22335R_175` … `rows22335R_179` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (5 parts, 29379 tests: row 80 columns 62–67, row 80 columns 68–71, row 80 columns
72–75, row 80 columns 76–79, row 80 columns 80–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_175 : rowsJ2 80 81 62 68 ≤ 4266808021426 := by decide +kernel

theorem rows22335R_176 : rowsJ2 80 81 68 72 ≤ 11878481669783 := by decide +kernel

theorem rows22335R_177 : rowsJ2 80 81 72 76 ≤ 12542590446870 := by decide +kernel

theorem rows22335R_178 : rowsJ2 80 81 76 80 ≤ 9986377765809 := by decide +kernel

theorem rows22335R_179 : rowsJ2 80 81 80 300 ≤ 2806711944031 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_175
#print axioms SieveCert.rows22335R_179
