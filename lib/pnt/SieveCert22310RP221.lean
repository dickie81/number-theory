/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 882–885 of 1732

File 221 of 430: the parts `rows22310R_882` … `rows22310R_885` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27577 tests: row 126 columns 91–92, row 126 columns 93–95, row 126 columns
96–98, row 126 columns 99–101), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_882 : rowsJ2 126 127 91 93 ≤ 7328748947 := by decide +kernel

theorem rows22310R_883 : rowsJ2 126 127 93 96 ≤ 0 := by decide +kernel

theorem rows22310R_884 : rowsJ2 126 127 96 99 ≤ 0 := by decide +kernel

theorem rows22310R_885 : rowsJ2 126 127 99 102 ≤ 215625230929 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_882
#print axioms SieveCert.rows22310R_885
