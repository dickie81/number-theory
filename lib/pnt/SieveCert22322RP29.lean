/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 110–113 of 561

File 29 of 143: the parts `rows22322R_110` … `rows22322R_113` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 23819 tests: row 67 columns 0–34, row 67 columns 35–46, row 67 columns 47–66,
row 67 columns 67–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_110 : rowsJ2 67 68 0 35 ≤ 693248875478506 := by decide +kernel

theorem rows22322R_111 : rowsJ2 67 68 35 47 ≤ 699934045346848 := by decide +kernel

theorem rows22322R_112 : rowsJ2 67 68 47 67 ≤ 603794761649313 := by decide +kernel

theorem rows22322R_113 : rowsJ2 67 68 67 300 ≤ 12655703424370 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_110
#print axioms SieveCert.rows22322R_113
