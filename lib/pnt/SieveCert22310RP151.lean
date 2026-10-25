/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 598–601 of 1732

File 151 of 430: the parts `rows22310R_598` … `rows22310R_601` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25328 tests: row 111 columns 78–82, row 111 columns 83–85, row 111 columns
86–88, row 111 columns 89–90), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_598 : rowsJ2 111 112 78 83 ≤ 5151658076929 := by decide +kernel

theorem rows22310R_599 : rowsJ2 111 112 83 86 ≤ 135939170496 := by decide +kernel

theorem rows22310R_600 : rowsJ2 111 112 86 89 ≤ 607725278462 := by decide +kernel

theorem rows22310R_601 : rowsJ2 111 112 89 91 ≤ 1174987416121 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_598
#print axioms SieveCert.rows22310R_601
