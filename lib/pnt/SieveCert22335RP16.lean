/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 63–66 of 549

File 16 of 140: the parts `rows22335R_63` … `rows22335R_66` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 24660 tests: row 54 columns 0–34, row 54 columns 35–43, row 54 columns 44–51,
row 54 columns 52–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22335R_63 : rowsJ2 54 55 0 35 ≤ 1308969732873800 := by decide +kernel

theorem rows22335R_64 : rowsJ2 54 55 35 44 ≤ 382516351532073 := by decide +kernel

theorem rows22335R_65 : rowsJ2 54 55 44 52 ≤ 588260469905297 := by decide +kernel

theorem rows22335R_66 : rowsJ2 54 55 52 300 ≤ 189610984813739 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_63
#print axioms SieveCert.rows22335R_66
