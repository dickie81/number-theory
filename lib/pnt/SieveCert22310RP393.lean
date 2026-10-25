/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1561–1564 of 1732

File 393 of 430: the parts `rows22310R_1561` … `rows22310R_1564` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24731 tests: row 191 columns 57–62, row 191 columns 63–399, row 192 columns
0–45, row 192 columns 46–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1561 : rowsJ2 191 192 57 63 ≤ 42447409718135 := by decide +kernel

theorem rows22310R_1562 : rowsJ2 191 192 63 400 ≤ 2090689418512325 := by decide +kernel

theorem rows22310R_1563 : rowsJ2 192 193 0 46 ≤ 32056437174813 := by decide +kernel

theorem rows22310R_1564 : rowsJ2 192 193 46 52 ≤ 54962871542412 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1561
#print axioms SieveCert.rows22310R_1564
