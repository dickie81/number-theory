/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 745–748 of 1732

File 187 of 430: the parts `rows22310R_745` … `rows22310R_748` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29398 tests: row 119 columns 35–47, row 119 columns 48–73, row 119 columns
74–78, row 119 columns 79–82), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_745 : rowsJ2 119 120 35 48 ≤ 290467359107514 := by decide +kernel

theorem rows22310R_746 : rowsJ2 119 120 48 74 ≤ 206502598935420 := by decide +kernel

theorem rows22310R_747 : rowsJ2 119 120 74 79 ≤ 420235127430 := by decide +kernel

theorem rows22310R_748 : rowsJ2 119 120 79 83 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_745
#print axioms SieveCert.rows22310R_748
