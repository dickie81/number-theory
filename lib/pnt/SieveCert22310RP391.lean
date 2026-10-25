/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1553–1556 of 1732

File 391 of 430: the parts `rows22310R_1553` … `rows22310R_1556` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29339 tests: row 190 columns 0–46, row 190 columns 47–52, row 190 columns
53–57, row 190 columns 58–63), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1553 : rowsJ2 190 191 0 47 ≤ 33715135366773 := by decide +kernel

theorem rows22310R_1554 : rowsJ2 190 191 47 53 ≤ 53187958208800 := by decide +kernel

theorem rows22310R_1555 : rowsJ2 190 191 53 58 ≤ 56389692798261 := by decide +kernel

theorem rows22310R_1556 : rowsJ2 190 191 58 64 ≤ 39328113445871 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1553
#print axioms SieveCert.rows22310R_1556
