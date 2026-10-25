/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 562–565 of 1732

File 142 of 430: the parts `rows22310R_562` … `rows22310R_565` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29669 tests: row 109 columns 44–54, row 109 columns 55–77, row 109 columns
78–83, row 109 columns 84–86), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_562 : rowsJ2 109 110 44 55 ≤ 273499620392347 := by decide +kernel

theorem rows22310R_563 : rowsJ2 109 110 55 78 ≤ 246892697856053 := by decide +kernel

theorem rows22310R_564 : rowsJ2 109 110 78 84 ≤ 9898158438539 := by decide +kernel

theorem rows22310R_565 : rowsJ2 109 110 84 87 ≤ 539472345344 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_562
#print axioms SieveCert.rows22310R_565
