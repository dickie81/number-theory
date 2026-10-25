/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1010–1013 of 1732

File 253 of 430: the parts `rows22310R_1010` … `rows22310R_1013` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27577 tests: row 134 columns 83–84, row 134 columns 85–87, row 134 columns
88–90, row 134 columns 91–93), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1010 : rowsJ2 134 135 83 85 ≤ 0 := by decide +kernel

theorem rows22310R_1011 : rowsJ2 134 135 85 88 ≤ 0 := by decide +kernel

theorem rows22310R_1012 : rowsJ2 134 135 88 91 ≤ 0 := by decide +kernel

theorem rows22310R_1013 : rowsJ2 134 135 91 94 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1010
#print axioms SieveCert.rows22310R_1013
