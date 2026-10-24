/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 79–82 of 549

File 20 of 140: the parts `rows22335R_79` … `rows22335R_82` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 24726 tests: row 58 columns 0–34, row 58 columns 35–43, row 58 columns 44–54,
row 58 columns 55–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22335R_79 : rowsJ2 58 59 0 35 ≤ 1054520645881300 := by decide +kernel

theorem rows22335R_80 : rowsJ2 58 59 35 44 ≤ 445719937313161 := by decide +kernel

theorem rows22335R_81 : rowsJ2 58 59 44 55 ≤ 695878644597524 := by decide +kernel

theorem rows22335R_82 : rowsJ2 58 59 55 300 ≤ 190063873511850 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_79
#print axioms SieveCert.rows22335R_82
