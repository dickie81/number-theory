/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 946–949 of 1732

File 237 of 430: the parts `rows22310R_946` … `rows22310R_949` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27034 tests: row 130 columns 81–83, row 130 columns 84–85, row 130 columns
86–87, row 130 columns 88–90), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_946 : rowsJ2 130 131 81 84 ≤ 0 := by decide +kernel

theorem rows22310R_947 : rowsJ2 130 131 84 86 ≤ 0 := by decide +kernel

theorem rows22310R_948 : rowsJ2 130 131 86 88 ≤ 0 := by decide +kernel

theorem rows22310R_949 : rowsJ2 130 131 88 91 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_946
#print axioms SieveCert.rows22310R_949
