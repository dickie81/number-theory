/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 938–941 of 1732

File 235 of 430: the parts `rows22310R_938` … `rows22310R_941` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24701 tests: row 129 columns 105–108, row 129 columns 109–112, row 129
columns 113–399, row 130 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_938 : rowsJ2 129 130 105 109 ≤ 9842481904147 := by decide +kernel

theorem rows22310R_939 : rowsJ2 129 130 109 113 ≤ 19753490794543 := by decide +kernel

theorem rows22310R_940 : rowsJ2 129 130 113 400 ≤ 886743514872961 := by decide +kernel

theorem rows22310R_941 : rowsJ2 130 131 0 35 ≤ 152909631195515 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_938
#print axioms SieveCert.rows22310R_941
