/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 75–78 of 549

File 19 of 140: the parts `rows22335R_75` … `rows22335R_78` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 24875 tests: row 57 columns 0–34, row 57 columns 35–43, row 57 columns 44–53,
row 57 columns 54–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22335R_75 : rowsJ2 57 58 0 35 ≤ 1114712463695588 := by decide +kernel

theorem rows22335R_76 : rowsJ2 57 58 35 44 ≤ 430187530703179 := by decide +kernel

theorem rows22335R_77 : rowsJ2 57 58 44 54 ≤ 662895539276032 := by decide +kernel

theorem rows22335R_78 : rowsJ2 57 58 54 300 ≤ 206982285117373 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_75
#print axioms SieveCert.rows22335R_78
