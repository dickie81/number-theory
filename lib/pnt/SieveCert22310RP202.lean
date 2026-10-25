/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 806–809 of 1732

File 202 of 430: the parts `rows22310R_806` … `rows22310R_809` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24600 tests: row 122 columns 82–84, row 122 columns 85–86, row 122 columns
87–88, row 122 columns 89–90), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_806 : rowsJ2 122 123 82 85 ≤ 0 := by decide +kernel

theorem rows22310R_807 : rowsJ2 122 123 85 87 ≤ 116252256256 := by decide +kernel

theorem rows22310R_808 : rowsJ2 122 123 87 89 ≤ 480518584163 := by decide +kernel

theorem rows22310R_809 : rowsJ2 122 123 89 91 ≤ 477966285430 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_806
#print axioms SieveCert.rows22310R_809
