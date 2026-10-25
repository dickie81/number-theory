/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 843–846 of 1732

File 211 of 430: the parts `rows22310R_843` … `rows22310R_846` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24876 tests: row 124 columns 82–84, row 124 columns 85–86, row 124 columns
87–88, row 124 columns 89–90), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_843 : rowsJ2 124 125 82 85 ≤ 0 := by decide +kernel

theorem rows22310R_844 : rowsJ2 124 125 85 87 ≤ 114998066884 := by decide +kernel

theorem rows22310R_845 : rowsJ2 124 125 87 89 ≤ 320506217617 := by decide +kernel

theorem rows22310R_846 : rowsJ2 124 125 89 91 ≤ 203385352435 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_843
#print axioms SieveCert.rows22310R_846
