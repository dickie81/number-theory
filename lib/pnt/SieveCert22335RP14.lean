/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 55–58 of 549

File 14 of 140: the parts `rows22335R_55` … `rows22335R_58` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 23932 tests: row 52 columns 0–34, row 52 columns 35–43, row 52 columns 44–51,
row 52 columns 52–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22335R_55 : rowsJ2 52 53 0 35 ≤ 1447897014613194 := by decide +kernel

theorem rows22335R_56 : rowsJ2 52 53 35 44 ≤ 364569876435744 := by decide +kernel

theorem rows22335R_57 : rowsJ2 52 53 44 52 ≤ 604341778367166 := by decide +kernel

theorem rows22335R_58 : rowsJ2 52 53 52 300 ≤ 69203650481569 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_55
#print axioms SieveCert.rows22335R_58
