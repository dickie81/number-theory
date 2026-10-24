/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 71–74 of 549

File 18 of 140: the parts `rows22335R_71` … `rows22335R_74` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 24904 tests: row 56 columns 0–34, row 56 columns 35–43, row 56 columns 44–52,
row 56 columns 53–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22335R_71 : rowsJ2 56 57 0 35 ≤ 1177404921768482 := by decide +kernel

theorem rows22335R_72 : rowsJ2 56 57 35 44 ≤ 411821289536848 := by decide +kernel

theorem rows22335R_73 : rowsJ2 56 57 44 53 ≤ 623468528875618 := by decide +kernel

theorem rows22335R_74 : rowsJ2 56 57 53 300 ≤ 223918355632876 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_71
#print axioms SieveCert.rows22335R_74
