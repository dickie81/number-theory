/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 51–54 of 549

File 13 of 140: the parts `rows22335R_51` … `rows22335R_54` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 23379 tests: row 51 columns 0–34, row 51 columns 35–43, row 51 columns 44–50,
row 51 columns 51–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22335R_51 : rowsJ2 51 52 0 35 ≤ 1519801552463013 := by decide +kernel

theorem rows22335R_52 : rowsJ2 51 52 35 44 ≤ 360119139014442 := by decide +kernel

theorem rows22335R_53 : rowsJ2 51 52 44 51 ≤ 537160021289196 := by decide +kernel

theorem rows22335R_54 : rowsJ2 51 52 51 300 ≤ 73115208756431 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_51
#print axioms SieveCert.rows22335R_54
