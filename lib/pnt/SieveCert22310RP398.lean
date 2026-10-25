/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1581–1584 of 1732

File 398 of 430: the parts `rows22310R_1581` … `rows22310R_1584` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26989 tests: row 196 columns 44–50, row 196 columns 51–56, row 196 columns
57–399, row 197 columns 0–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1581 : rowsJ2 196 197 44 51 ≤ 71857335764544 := by decide +kernel

theorem rows22310R_1582 : rowsJ2 196 197 51 57 ≤ 67178130286784 := by decide +kernel

theorem rows22310R_1583 : rowsJ2 196 197 57 400 ≤ 2126794921656496 := by decide +kernel

theorem rows22310R_1584 : rowsJ2 197 198 0 44 ≤ 32553357280487 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1581
#print axioms SieveCert.rows22310R_1584
