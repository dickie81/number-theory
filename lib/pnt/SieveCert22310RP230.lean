/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 918–921 of 1732

File 230 of 430: the parts `rows22310R_918` … `rows22310R_921` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27807 tests: row 128 columns 96–98, row 128 columns 99–101, row 128 columns
102–104, row 128 columns 105–108), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_918 : rowsJ2 128 129 96 99 ≤ 0 := by decide +kernel

theorem rows22310R_919 : rowsJ2 128 129 99 102 ≤ 246381525315 := by decide +kernel

theorem rows22310R_920 : rowsJ2 128 129 102 105 ≤ 2580571396455 := by decide +kernel

theorem rows22310R_921 : rowsJ2 128 129 105 109 ≤ 9382079221644 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_918
#print axioms SieveCert.rows22310R_921
