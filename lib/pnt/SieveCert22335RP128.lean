/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 496–500 of 549

File 128 of 140: the parts `rows22335R_496` … `rows22335R_500` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (5 parts, 28909 tests: row 147 columns 0–39, row 147 columns 40–299, row 148 columns
0–38, row 148 columns 39–299, row 149 columns 0–38), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22335R_496 : rowsJ2 147 148 0 40 ≤ 197502744972865 := by decide +kernel

theorem rows22335R_497 : rowsJ2 147 148 40 300 ≤ 2875370652779133 := by decide +kernel

theorem rows22335R_498 : rowsJ2 148 149 0 39 ≤ 190011018301910 := by decide +kernel

theorem rows22335R_499 : rowsJ2 148 149 39 300 ≤ 2901636206473209 := by decide +kernel

theorem rows22335R_500 : rowsJ2 149 150 0 39 ≤ 202424456462659 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_496
#print axioms SieveCert.rows22335R_500
