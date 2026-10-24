/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 67–70 of 549

File 17 of 140: the parts `rows22335R_67` … `rows22335R_70` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 24850 tests: row 55 columns 0–34, row 55 columns 35–43, row 55 columns 44–52,
row 55 columns 53–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22335R_67 : rowsJ2 55 56 0 35 ≤ 1241971802886047 := by decide +kernel

theorem rows22335R_68 : rowsJ2 55 56 35 44 ≤ 395908129221827 := by decide +kernel

theorem rows22335R_69 : rowsJ2 55 56 44 53 ≤ 640939050427327 := by decide +kernel

theorem rows22335R_70 : rowsJ2 55 56 53 300 ≤ 177342007220107 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_67
#print axioms SieveCert.rows22335R_70
