/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 934–937 of 1732

File 234 of 430: the parts `rows22310R_934` … `rows22310R_937` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27048 tests: row 129 columns 93–95, row 129 columns 96–98, row 129 columns
99–101, row 129 columns 102–104), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_934 : rowsJ2 129 130 93 96 ≤ 0 := by decide +kernel

theorem rows22310R_935 : rowsJ2 129 130 96 99 ≤ 0 := by decide +kernel

theorem rows22310R_936 : rowsJ2 129 130 99 102 ≤ 250645464459 := by decide +kernel

theorem rows22310R_937 : rowsJ2 129 130 102 105 ≤ 2721741159862 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_934
#print axioms SieveCert.rows22310R_937
