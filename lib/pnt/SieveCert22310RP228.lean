/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 910–913 of 1732

File 228 of 430: the parts `rows22310R_910` … `rows22310R_913` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26670 tests: row 128 columns 74–77, row 128 columns 78–80, row 128 columns
81–83, row 128 columns 84–85), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_910 : rowsJ2 128 129 74 78 ≤ 0 := by decide +kernel

theorem rows22310R_911 : rowsJ2 128 129 78 81 ≤ 0 := by decide +kernel

theorem rows22310R_912 : rowsJ2 128 129 81 84 ≤ 0 := by decide +kernel

theorem rows22310R_913 : rowsJ2 128 129 84 86 ≤ 28220083270 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_910
#print axioms SieveCert.rows22310R_913
