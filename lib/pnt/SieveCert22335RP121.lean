/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 466–470 of 549

File 121 of 140: the parts `rows22335R_466` … `rows22335R_470` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (5 parts, 28150 tests: row 134 columns 43–51, row 134 columns 52–299, row 135 columns
0–42, row 135 columns 43–52, row 135 columns 53–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22335R_466 : rowsJ2 134 135 43 52 ≤ 108986523831492 := by decide +kernel

theorem rows22335R_467 : rowsJ2 134 135 52 300 ≤ 2815406197032913 := by decide +kernel

theorem rows22335R_468 : rowsJ2 135 136 0 43 ≤ 129976341351948 := by decide +kernel

theorem rows22335R_469 : rowsJ2 135 136 43 53 ≤ 109517011151867 := by decide +kernel

theorem rows22335R_470 : rowsJ2 135 136 53 300 ≤ 2796761776192193 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_466
#print axioms SieveCert.rows22335R_470
