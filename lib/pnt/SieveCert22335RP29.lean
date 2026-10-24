/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 110–113 of 549

File 29 of 140: the parts `rows22335R_110` … `rows22335R_113` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 23819 tests: row 67 columns 0–34, row 67 columns 35–46, row 67 columns 47–66,
row 67 columns 67–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22335R_110 : rowsJ2 67 68 0 35 ≤ 648713471434851 := by decide +kernel

theorem rows22335R_111 : rowsJ2 67 68 35 47 ≤ 696715853398750 := by decide +kernel

theorem rows22335R_112 : rowsJ2 67 68 47 67 ≤ 600849463253657 := by decide +kernel

theorem rows22335R_113 : rowsJ2 67 68 67 300 ≤ 12592398823778 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_110
#print axioms SieveCert.rows22335R_113
