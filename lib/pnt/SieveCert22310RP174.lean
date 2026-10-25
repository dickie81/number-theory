/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 690–693 of 1732

File 174 of 430: the parts `rows22310R_690` … `rows22310R_693` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25993 tests: row 116 columns 80–83, row 116 columns 84–86, row 116 columns
87–88, row 116 columns 89–90), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_690 : rowsJ2 116 117 80 84 ≤ 0 := by decide +kernel

theorem rows22310R_691 : rowsJ2 116 117 84 87 ≤ 120184517436 := by decide +kernel

theorem rows22310R_692 : rowsJ2 116 117 87 89 ≤ 499884157461 := by decide +kernel

theorem rows22310R_693 : rowsJ2 116 117 89 91 ≤ 1137340345990 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_690
#print axioms SieveCert.rows22310R_693
