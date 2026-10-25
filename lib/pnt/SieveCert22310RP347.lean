/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1382–1385 of 1732

File 347 of 430: the parts `rows22310R_1382` … `rows22310R_1385` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26542 tests: row 164 columns 82–87, row 164 columns 88–399, row 165 columns
0–55, row 165 columns 56–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1382 : rowsJ2 164 165 82 88 ≤ 3486827118780 := by decide +kernel

theorem rows22310R_1383 : rowsJ2 164 165 88 400 ≤ 711126664598692 := by decide +kernel

theorem rows22310R_1384 : rowsJ2 165 166 0 56 ≤ 92454776604471 := by decide +kernel

theorem rows22310R_1385 : rowsJ2 165 166 56 61 ≤ 20043822277731 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1382
#print axioms SieveCert.rows22310R_1385
