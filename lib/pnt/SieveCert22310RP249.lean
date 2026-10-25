/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 994–997 of 1732

File 249 of 430: the parts `rows22310R_994` … `rows22310R_997` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26344 tests: row 133 columns 81–82, row 133 columns 83–84, row 133 columns
85–87, row 133 columns 88–90), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_994 : rowsJ2 133 134 81 83 ≤ 0 := by decide +kernel

theorem rows22310R_995 : rowsJ2 133 134 83 85 ≤ 0 := by decide +kernel

theorem rows22310R_996 : rowsJ2 133 134 85 88 ≤ 0 := by decide +kernel

theorem rows22310R_997 : rowsJ2 133 134 88 91 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_994
#print axioms SieveCert.rows22310R_997
